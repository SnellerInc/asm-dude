// The MIT License (MIT)
//
// Copyright (c) 2023 Henk-Jan Lebbink
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

namespace AsmDude2LS
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.Diagnostics.Contracts;
    using System.IO;
    using System.Linq;
    using System.Windows.Xps;

    using AsmTools;

    public readonly struct LabelID
    {
        private readonly ulong data;

        public LabelID(int lineNumber, int fileID, int startPos, int endPos)
        {
            data = ((ulong)lineNumber & 0xFFFFFF) | ((ulong)(fileID & 0xFF) << 24) | ((ulong)(startPos & 0xFFFFF) << 32) | ((ulong)(endPos & 0xFFFFF) << 48);
        }

        public int LineNumber
        {
            get
            {
                return (int)(this.data & 0x00FFFFFF);
            }
        }

        public int File_Id
        {
            get
            {
                return (int)((this.data >> 24) & 0xFF);
            }
        }

        public int Start_Pos
        {
            get
            {
                return (int)((this.data >> 32) & 0xFFFF);
            }

        }

        public int End_Pos
        {
            get
            {
                return (int)((this.data >> 48) & 0xFFFF);
            }
        }

        public bool Is_From_Main_File
        {
            get
            {
                return File_Id == 0;
            }
        }

        public override string ToString()
        {
            return $"LabelID({LineNumber}, {File_Id}, {Start_Pos}, {End_Pos})";
        }
    }


    public sealed class LabelGraph
    {
        #region Fields
        private readonly TraceSource traceSource;
        private readonly AsmLanguageServerOptions options;

        private readonly string[] lines;
        private readonly string thisFilename_;
        private readonly bool caseSenstiveLabel_; 
        private readonly Dictionary<int, string> filenames_;

        /// <summary>
        /// Include_Filename = the file that is supposed to be included
        /// Path = path at which the include_filename is supposed to be found
        /// Source_Filename = full path and name of the source file in which the include is defined
        /// LineNumber = the lineNumber at which the include is defined
        /// </summary>
        private readonly List<(string include_filename, string path, string source_filename, int lineNumber)> undefined_includes_;

        private readonly Dictionary<string, List<LabelID>> usedAt_;
        private readonly Dictionary<string, List<LabelID>> defAt_;
        private readonly Dictionary<string, List<LabelID>> defAt_PROTO_;
        private readonly HashSet<LabelID> hasLabel_;
        private readonly HashSet<LabelID> hasDef_;

        public bool Enabled { get; private set; }

        #endregion Private Fields

        public LabelGraph(
                string[] lines,
                string filename,
                bool caseSensitiveLabel,
                TraceSource traceSource,
                AsmLanguageServerOptions options)
        {
            this.traceSource = traceSource;
            LogInfo($"LabelGraph: constructor: creating a label graph for {filename}"); //NOTE first init traceSource!

            this.lines = lines;
            this.thisFilename_ = filename;
            this.caseSenstiveLabel_ = caseSensitiveLabel;
            this.options = options;

            this.filenames_ = new Dictionary<int, string>();
            this.usedAt_ = new Dictionary<string, List<LabelID>>(); // if LabelGraph is case insensitive then string is UPPERCASE
            this.defAt_ = new Dictionary<string, List<LabelID>>();// if LabelGraph is case insensitive then string is UPPERCASE
            this.defAt_PROTO_ = new Dictionary<string, List<LabelID>>();// if LabelGraph is case insensitive then string is UPPERCASE
            this.hasLabel_ = new HashSet<LabelID>();
            this.hasDef_ = new HashSet<LabelID>();
            this.undefined_includes_ = new List<(string include_filename, string path, string source_filename, int lineNumber)>();
            this.Enabled = this.options.IntelliSense_Label_Analysis_On;

            if (lines.Length >= options.MaxFileLines)
            {
                this.Enabled = false;
                LogWarning($"{this}:LabelGraph; file {filename} contains {lines.Length} lines which is more than maxLines {options.MaxFileLines}; switching off label analysis");
            }

            for (int lineNumber = 0; lineNumber < lines.Length; ++lineNumber)
            {
                this.Add_Linenumber(lines[lineNumber], lineNumber, 0);
            }
        }
 
        private void LogInfo(string msg)
        {
            this.traceSource.TraceEvent(TraceEventType.Information, 0, msg);
        }
        private void LogWarning(string msg)
        {
            this.traceSource.TraceEvent(TraceEventType.Warning, 0, msg);
        }
        private void LogError(string msg)
        {
            this.traceSource.TraceEvent(TraceEventType.Error, 0, msg);
        }

        #region Public Methods

        public string Get_Filename(LabelID labelID)
        {
            if (this.filenames_.TryGetValue(labelID.File_Id, out string filename))
            {
                return filename;
            }
            else
            {
                LogWarning("LabelGraph:Get_Filename: no filename for labelID=" + labelID + " (fileId " + labelID.File_Id + "; line " + labelID.LineNumber + ")");
                return string.Empty;
            }
        }

        public IEnumerable<List<LabelID>> Label_Clashes
        {
            get
            {
                foreach ((string _, List<LabelID> labelIDs) in this.defAt_)
                {
                    if (labelIDs.Count > 1)
                    {
                        yield return labelIDs;
                    }
                }
            }
        }

        public IEnumerable<LabelID> Undefined_Labels
        {
            get
            {
                AssemblerEnum usedAssembler = this.options.Used_Assembler;
                foreach ((string full_Qualified_Label, List<LabelID> labelIDs) in this.usedAt_)
                {
                    // NOTE: if LabelGraph is case insensitive then full_Qualified_Label is UPPERCASE
                    if (this.defAt_.ContainsKey(full_Qualified_Label))
                    {
                        continue;
                    }

                    string regular_Label = AsmDudeToolsStatic.Retrieve_Regular_Label(full_Qualified_Label, usedAssembler);
                    if (this.defAt_.ContainsKey(regular_Label))
                    {
                        continue;
                    }

                    if (this.defAt_PROTO_.ContainsKey(regular_Label))
                    {
                        continue;
                    }

                    Console.WriteLine($"Undefined_Labels: full_Qualified_Label {full_Qualified_Label}");
                    foreach (var x in this.defAt_)
                    {
                        Console.WriteLine($"label {x.Key} ");
                    }

                    foreach (LabelID labelID in labelIDs)
                    {
                        yield return labelID;
                    }
                }
            }
        }

        public SortedDictionary<string, string> Label_Descriptions
        {
            get
            {
                SortedDictionary<string, string> result = new();
                {
                    foreach (KeyValuePair<string, List<LabelID>> entry in this.defAt_)
                    {
                        LabelID id = entry.Value[0];
                        int lineNumber = id.LineNumber;
                        string filename = Path.GetFileName(this.Get_Filename(id));
                        string lineContent;
                        if (id.Is_From_Main_File())
                        {
                            lineContent = " :" + this.lines.ElementAtOrDefault(lineNumber);
                        }
                        else
                        {
                            lineContent = " :TODO";
                        }
                        result.Add(entry.Key, AsmDudeToolsStatic.Cleanup($"LINE {lineNumber + 1} ({filename}){lineContent}"));
                    }
                }
                return result;
            }
        }

        public bool Has_Label(string label)
        {
            return this.defAt_.ContainsKey(label) || this.defAt_PROTO_.ContainsKey(label);
        }

        public bool Has_Label_Clash(string label)
        {
            if (this.defAt_.TryGetValue(label, out List<LabelID> list))
            {
                return list.Count > 1;
            }
            return false;
        }

        public SortedSet<LabelID> Get_Label_Def_Linenumbers(string label)
        {
            SortedSet<LabelID> results = new();
            {
                if (this.defAt_.TryGetValue(label, out List<LabelID> list))
                {
                    // AsmDudeToolsStatic.Output_INFO("LabelGraph:Get_Label_Def_Linenumbers: Regular label definitions. label=" + label + ": found "+list.Count +" definitions.");
                    results.UnionWith(list);
                }
            }
            {
                if (this.defAt_PROTO_.TryGetValue(label, out List<LabelID> list))
                {
                    // AsmDudeToolsStatic.Output_INFO("LabelGraph:Get_Label_Def_Linenumbers: PROTO label definitions. label=" + label + ": found "+list.Count +" definitions.");
                    results.UnionWith(list);
                }
            }
            return results;
        }

        public HashSet<LabelID> Label_Used_At_Info(string full_Qualified_Label, string label)
        {
            Contract.Requires(full_Qualified_Label != null);
            Contract.Requires(label != null);
            throw new NotImplementedException("TODO: handling of case sensitive labels");

            // AsmDudeToolsStatic.Output_INFO("LabelGraph:Label_Used_At_Info: full_Qualified_Label=" + full_Qualified_Label + "; label=" + label);
            HashSet<LabelID> results = new();
            {
                if (this.usedAt_.TryGetValue(full_Qualified_Label, out List<LabelID> lines))
                {
                    results.UnionWith(lines);
                }
            }
            {
                if (this.usedAt_.TryGetValue(label, out List<LabelID> lines))
                {
                    results.UnionWith(lines);
                }
            }
            if (full_Qualified_Label.Equals(label, StringComparison.Ordinal))
            {
                AssemblerEnum usedAssembler = this.options.Used_Assembler;
                foreach ((string label2, List<LabelID> labelIDs) in this.usedAt_)
                {
                    string regular_Label = AsmDudeToolsStatic.Retrieve_Regular_Label(label2, usedAssembler);
                    if (label.Equals(regular_Label, StringComparison.Ordinal))
                    {
                        results.UnionWith(labelIDs);
                    }
                }
            }
            return results;
        }

        public IEnumerable<(string include_Filename, string path, string source_Filename, int lineNumber)> Undefined_Includes { get { return this.undefined_includes_; } }

        #endregion Public Methods

        #region Private Methods

        private void Disable()
        {
            string msg = $"Performance of LabelGraph is horrible: disabling label analysis for {this.thisFilename_}.";
            LogWarning(msg);

            this.Enabled = false;
            {
                this.defAt_.Clear();
                this.defAt_PROTO_.Clear();
                this.hasDef_.Clear();
                this.usedAt_.Clear();
                this.hasLabel_.Clear();
                this.undefined_includes_.Clear();
            }
            // AsmDudeToolsStatic.Disable_Message(msg, this.thisFilename_, this.Error_List_Provider);
        }
 
        private void Add_Linenumber(string lineStr, int lineNumber, int fileID)
        {
            AssemblerEnum usedAssembler = this.options.Used_Assembler;

            (string label, Mnemonic mnemonic, string[] args, string _) = AsmSourceTools.ParseLine(lineStr);

            if (label.Length > 0)
            {
                int startPos = lineStr.IndexOf(label);
                LabelID labelID = new(lineNumber, fileID, startPos, startPos + label.Length);

                string extra_Tag_Info = null; // TODO asmTokenTag.Tag.Misc;

                if ((extra_Tag_Info != null))// TODO && extra_Tag_Info.Equals(AsmTokenTag.MISC_KEYWORD_PROTO, StringComparison.Ordinal))
                {
                    LogInfo("LabelGraph:Add_Linenumber: found PROTO labelDef \"" + label + "\" at line " + lineNumber);
                    Add_To_Dictionary(label, labelID, this.caseSenstiveLabel_, this.defAt_PROTO_);
                }
                else
                {
                    string full_Qualified_Label = AsmDudeToolsStatic.Make_Full_Qualified_Label(extra_Tag_Info, label, usedAssembler);
                    LogInfo("LabelGraph:Add_Linenumber: found labelDef \"" + label + "\" at line " + lineNumber + "; full_Qualified_Label = \"" + full_Qualified_Label + "\".");
                    Add_To_Dictionary(full_Qualified_Label, labelID, this.caseSenstiveLabel_, this.defAt_);
                }
                this.hasDef_.Add(labelID);
            }
            if (AsmSourceTools.IsJump(mnemonic))
            {
                if (args.Length > 0)
                {
                    string labelStr = args[0];
                    string prefix = null; // TODO asmTokenTag.Tag.Misc 
                    string full_Qualified_Label = AsmDudeToolsStatic.Make_Full_Qualified_Label(prefix, labelStr, usedAssembler);

                    int startPos = lineStr.IndexOf(labelStr);
                    if (startPos < 0)
                    {
                        LogError($"LabelGraph:Add_Linenumber: startPos {startPos}");
                    } 
                    else
                    {
                        LabelID labelID = new(lineNumber, fileID, startPos, startPos + labelStr.Length);
                        Add_To_Dictionary(full_Qualified_Label, labelID, this.caseSenstiveLabel_, this.usedAt_);
                        LogInfo("LabelGraph:Add_Linenumber: used label \"" + label + "\" at line " + lineNumber);
                        this.hasLabel_.Add(labelID);
                    }
                }
            }

            bool hasIncludes = false; //TODO
            if (hasIncludes)
            {
                //string directive_upcase = Get_Text(buffer, asmTokenTag).ToUpperInvariant();
                //switch (directive_upcase)
                //{
                //    case "%INCLUDE":
                //    case "INCLUDE":
                //        {
                //            if (enumerator.MoveNext()) // check whether a word exists after the include keyword
                //            {
                //                string currentFilename = this.Get_Filename(labelID);
                //                string includeFilename = Get_Text(buffer, enumerator.Current);
                //                this.Handle_Include(includeFilename, lineNumber, currentFilename);
                //            }
                //            break;
                //        }
                //    default:
                //        {
                //            break;
                //        }
                //}
            }
        }

        private static void Add_To_Dictionary(string key, LabelID id, bool caseSensitiveLabels, Dictionary<string, List<LabelID>> dict)
        {
            if ((key == null) || (key.Length == 0))
            {
                return;
            }
            string key2 = (caseSensitiveLabels) ? key : key.ToUpper();

            if (dict.TryGetValue(key2, out List<LabelID> list))
            {
                list.Add(id);
            }
            else
            {
                dict.Add(key2, new List<LabelID> { id });
            }
        }

        //private void Handle_Include(string includeFilename, int lineNumber, string currentFilename)
        //{
        //    try
        //    {
        //        if (includeFilename.Length < 1)
        //        {
        //            //AsmDudeToolsStatic.Output_INFO("LabelGraph:Handle_Include: file with name \"" + includeFilename + "\" is too short.");
        //            return;
        //        }
        //        if (includeFilename.Length > 2)
        //        {
        //            if (includeFilename.StartsWith("[", StringComparison.Ordinal) && includeFilename.EndsWith("]", StringComparison.Ordinal))
        //            {
        //                includeFilename = includeFilename.Substring(1, includeFilename.Length - 2);
        //            }
        //            else if (includeFilename.StartsWith("\"", StringComparison.Ordinal) && includeFilename.EndsWith("\"", StringComparison.Ordinal))
        //            {
        //                includeFilename = includeFilename.Substring(1, includeFilename.Length - 2);
        //            }
        //        }
        //        string filePath = Path.GetDirectoryName(this.thisFilename_) + Path.DirectorySeparatorChar + includeFilename;

        //        if (!File.Exists(filePath))
        //        {
        //            //AsmDudeToolsStatic.Output_INFO("LabelGraph:Handle_Include: file " + filePath + " does not exist");
        //            this.undefined_includes_.Add((include_filename: includeFilename, path: filePath, source_filename: currentFilename, lineNumber: lineNumber));
        //        }
        //        else
        //        {
        //            if (this.filenames_.Values.Contains(filePath))
        //            {
        //                //AsmDudeToolsStatic.Output_INFO("LabelGraph:Handle_Include: including file " + filePath + " has already been included");
        //            }
        //            else
        //            {
        //                //AsmDudeToolsStatic.Output_INFO("LabelGraph:Handle_Include: including file " + filePath);

        //                ITextDocument doc = this.docFactory_.CreateAndLoadTextDocument(filePath, this.contentType_, true, out bool characterSubstitutionsOccurred);
        //                doc.FileActionOccurred += this.Doc_File_Action_Occurred;
        //                uint fileId = (uint)this.filenames_.Count;
        //                this.filenames_.Add(fileId, filePath);
        //                this.Add_All(doc.TextBuffer, fileId);
        //            }
        //        }
        //    }
        //    catch (Exception e)
        //    {
        //        LogWarning("LabelGraph:Handle_Include. Exception:" + e.Message);
        //    }
        //}

        //private void Doc_File_Action_Occurred(object sender, TextDocumentFileActionEventArgs e)
        //{
            //ITextDocument doc = sender as ITextDocument;
            //AsmDudeToolsStatic.Output_INFO("LabelGraph:Doc_File_Action_Occurred: " + doc.FilePath + ":" + e.FileActionType);
        //}

        #endregion Private Methods
    }
}
