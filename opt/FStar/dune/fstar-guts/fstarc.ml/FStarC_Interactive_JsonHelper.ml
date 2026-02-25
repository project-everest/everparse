open Prims
type assoct = (Prims.string * FStarC_Json.json) Prims.list
let try_assoc (key : Prims.string) (d : assoct) :
  FStarC_Json.json FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Util.try_find
      (fun uu___1 -> match uu___1 with | (k, uu___2) -> k = key) d in
  FStarC_Option.map FStar_Pervasives_Native.snd uu___
exception MissingKey of Prims.string 
let uu___is_MissingKey (projectee : Prims.exn) : Prims.bool=
  match projectee with | MissingKey uu___ -> true | uu___ -> false
let __proj__MissingKey__item__uu___ (projectee : Prims.exn) : Prims.string=
  match projectee with | MissingKey uu___ -> uu___
exception InvalidQuery of Prims.string 
let uu___is_InvalidQuery (projectee : Prims.exn) : Prims.bool=
  match projectee with | InvalidQuery uu___ -> true | uu___ -> false
let __proj__InvalidQuery__item__uu___ (projectee : Prims.exn) : Prims.string=
  match projectee with | InvalidQuery uu___ -> uu___
exception UnexpectedJsonType of (Prims.string * FStarC_Json.json) 
let uu___is_UnexpectedJsonType (projectee : Prims.exn) : Prims.bool=
  match projectee with | UnexpectedJsonType uu___ -> true | uu___ -> false
let __proj__UnexpectedJsonType__item__uu___ (projectee : Prims.exn) :
  (Prims.string * FStarC_Json.json)=
  match projectee with | UnexpectedJsonType uu___ -> uu___
exception MalformedHeader 
let uu___is_MalformedHeader (projectee : Prims.exn) : Prims.bool=
  match projectee with | MalformedHeader -> true | uu___ -> false
exception InputExhausted 
let uu___is_InputExhausted (projectee : Prims.exn) : Prims.bool=
  match projectee with | InputExhausted -> true | uu___ -> false
let assoc (key : Prims.string) (a : assoct) : FStarC_Json.json=
  let uu___ = try_assoc key a in
  match uu___ with
  | FStar_Pervasives_Native.Some v -> v
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 = FStarC_Format.fmt1 "Missing key [%s]" key in
        MissingKey uu___2 in
      FStarC_Effect.raise uu___1
let write_json (js : FStarC_Json.json) : unit=
  (let uu___1 = FStarC_Json.string_of_json js in
   FStarC_Format.print_raw uu___1);
  FStarC_Format.print_raw "\n"
let write_jsonrpc (js : FStarC_Json.json) : unit=
  let js_str = FStarC_Json.string_of_json js in
  let len =
    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
      (FStarC_String.length js_str) in
  let uu___ = FStarC_Format.fmt2 "Content-Length: %s\r\n\r\n%s" len js_str in
  FStarC_Format.print_raw uu___
let js_fail (expected : Prims.string) (got : FStarC_Json.json) : 'a=
  FStarC_Effect.raise (UnexpectedJsonType (expected, got))
let js_int (uu___ : FStarC_Json.json) : Prims.int=
  match uu___ with
  | FStarC_Json.JsonInt i -> i
  | other -> js_fail "int" other
let js_bool (uu___ : FStarC_Json.json) : Prims.bool=
  match uu___ with
  | FStarC_Json.JsonBool b -> b
  | other -> js_fail "int" other
let js_str (uu___ : FStarC_Json.json) : Prims.string=
  match uu___ with
  | FStarC_Json.JsonStr s -> s
  | other -> js_fail "string" other
let js_list (k : FStarC_Json.json -> 'a) (uu___ : FStarC_Json.json) :
  'a Prims.list=
  match uu___ with
  | FStarC_Json.JsonList l -> FStarC_List.map k l
  | other -> js_fail "list" other
let js_assoc (uu___ : FStarC_Json.json) : assoct=
  match uu___ with
  | FStarC_Json.JsonAssoc a -> a
  | other -> js_fail "dictionary" other
let js_str_int (uu___ : FStarC_Json.json) : Prims.int=
  match uu___ with
  | FStarC_Json.JsonInt i -> i
  | FStarC_Json.JsonStr s -> FStarC_Util.int_of_string s
  | other -> js_fail "string or int" other
let arg (k : Prims.string) (r : assoct) : FStarC_Json.json=
  let uu___ = let uu___1 = assoc "params" r in js_assoc uu___1 in
  assoc k uu___
let uri_to_path (u : Prims.string) : Prims.string=
  let uu___ =
    let uu___1 =
      FStarC_Util.substring u (Prims.of_int (9)) (Prims.of_int (3)) in
    uu___1 = "%3A" in
  if uu___
  then
    let uu___1 = FStarC_Util.substring u (Prims.of_int (8)) Prims.int_one in
    let uu___2 = FStarC_Util.substring_from u (Prims.of_int (12)) in
    FStarC_Format.fmt2 "%s:%s" uu___1 uu___2
  else FStarC_Util.substring_from u (Prims.of_int (7))
type completion_context =
  {
  trigger_kind: Prims.int ;
  trigger_char: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkcompletion_context__item__trigger_kind
  (projectee : completion_context) : Prims.int=
  match projectee with | { trigger_kind; trigger_char;_} -> trigger_kind
let __proj__Mkcompletion_context__item__trigger_char
  (projectee : completion_context) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { trigger_kind; trigger_char;_} -> trigger_char
let path_to_uri (u : Prims.string) : Prims.string=
  let uu___ = let uu___1 = FStarC_Util.char_at u Prims.int_one in uu___1 = 58 in
  if uu___
  then
    let rest =
      let uu___1 = FStarC_Util.substring_from u (Prims.of_int (2)) in
      FStarC_Util.replace_char uu___1 92 47 in
    let uu___1 = FStarC_Util.substring u Prims.int_zero Prims.int_one in
    FStarC_Format.fmt2 "file:///%s%3A%s" uu___1 rest
  else FStarC_Format.fmt1 "file://%s" u
let js_compl_context (uu___ : FStarC_Json.json) : completion_context=
  match uu___ with
  | FStarC_Json.JsonAssoc a ->
      let uu___1 = let uu___2 = assoc "triggerKind" a in js_int uu___2 in
      let uu___2 =
        let uu___3 = try_assoc "triggerChar" a in
        FStarC_Option.map js_str uu___3 in
      { trigger_kind = uu___1; trigger_char = uu___2 }
  | other -> js_fail "dictionary" other
type txdoc_item =
  {
  fname: Prims.string ;
  langId: Prims.string ;
  version: Prims.int ;
  text: Prims.string }
let __proj__Mktxdoc_item__item__fname (projectee : txdoc_item) :
  Prims.string=
  match projectee with | { fname; langId; version; text;_} -> fname
let __proj__Mktxdoc_item__item__langId (projectee : txdoc_item) :
  Prims.string=
  match projectee with | { fname; langId; version; text;_} -> langId
let __proj__Mktxdoc_item__item__version (projectee : txdoc_item) : Prims.int=
  match projectee with | { fname; langId; version; text;_} -> version
let __proj__Mktxdoc_item__item__text (projectee : txdoc_item) : Prims.string=
  match projectee with | { fname; langId; version; text;_} -> text
let js_txdoc_item (uu___ : FStarC_Json.json) : txdoc_item=
  match uu___ with
  | FStarC_Json.JsonAssoc a ->
      let arg1 k = assoc k a in
      let uu___1 =
        let uu___2 = let uu___3 = arg1 "uri" in js_str uu___3 in
        uri_to_path uu___2 in
      let uu___2 = let uu___3 = arg1 "languageId" in js_str uu___3 in
      let uu___3 = let uu___4 = arg1 "version" in js_int uu___4 in
      let uu___4 = let uu___5 = arg1 "text" in js_str uu___5 in
      { fname = uu___1; langId = uu___2; version = uu___3; text = uu___4 }
  | other -> js_fail "dictionary" other
type txdoc_pos = {
  path: Prims.string ;
  line: Prims.int ;
  col: Prims.int }
let __proj__Mktxdoc_pos__item__path (projectee : txdoc_pos) : Prims.string=
  match projectee with | { path; line; col;_} -> path
let __proj__Mktxdoc_pos__item__line (projectee : txdoc_pos) : Prims.int=
  match projectee with | { path; line; col;_} -> line
let __proj__Mktxdoc_pos__item__col (projectee : txdoc_pos) : Prims.int=
  match projectee with | { path; line; col;_} -> col
let js_txdoc_id (r : (Prims.string * FStarC_Json.json) Prims.list) :
  Prims.string=
  let uu___ =
    let uu___1 =
      let uu___2 = let uu___3 = arg "textDocument" r in js_assoc uu___3 in
      assoc "uri" uu___2 in
    js_str uu___1 in
  uri_to_path uu___
let js_txdoc_pos (r : (Prims.string * FStarC_Json.json) Prims.list) :
  txdoc_pos=
  let pos = let uu___ = arg "position" r in js_assoc uu___ in
  let uu___ = js_txdoc_id r in
  let uu___1 = let uu___2 = assoc "line" pos in js_int uu___2 in
  let uu___2 = let uu___3 = assoc "character" pos in js_int uu___3 in
  { path = uu___; line = uu___1; col = uu___2 }
type workspace_folder = {
  wk_uri: Prims.string ;
  wk_name: Prims.string }
let __proj__Mkworkspace_folder__item__wk_uri (projectee : workspace_folder) :
  Prims.string= match projectee with | { wk_uri; wk_name;_} -> wk_uri
let __proj__Mkworkspace_folder__item__wk_name (projectee : workspace_folder)
  : Prims.string= match projectee with | { wk_uri; wk_name;_} -> wk_name
type wsch_event = {
  added: workspace_folder ;
  removed: workspace_folder }
let __proj__Mkwsch_event__item__added (projectee : wsch_event) :
  workspace_folder= match projectee with | { added; removed;_} -> added
let __proj__Mkwsch_event__item__removed (projectee : wsch_event) :
  workspace_folder= match projectee with | { added; removed;_} -> removed
let js_wsch_event (uu___ : FStarC_Json.json) : wsch_event=
  match uu___ with
  | FStarC_Json.JsonAssoc a ->
      let added' = let uu___1 = assoc "added" a in js_assoc uu___1 in
      let removed' = let uu___1 = assoc "removed" a in js_assoc uu___1 in
      let uu___1 =
        let uu___2 = let uu___3 = assoc "uri" added' in js_str uu___3 in
        let uu___3 = let uu___4 = assoc "name" added' in js_str uu___4 in
        { wk_uri = uu___2; wk_name = uu___3 } in
      let uu___2 =
        let uu___3 = let uu___4 = assoc "uri" removed' in js_str uu___4 in
        let uu___4 = let uu___5 = assoc "name" removed' in js_str uu___5 in
        { wk_uri = uu___3; wk_name = uu___4 } in
      { added = uu___1; removed = uu___2 }
  | other -> js_fail "dictionary" other
let js_contentch (uu___ : FStarC_Json.json) : Prims.string=
  match uu___ with
  | FStarC_Json.JsonList l ->
      let uu___1 =
        FStarC_List.map
          (fun uu___2 ->
             match uu___2 with
             | FStarC_Json.JsonAssoc a ->
                 let uu___3 = assoc "text" a in js_str uu___3) l in
      FStarC_List.hd uu___1
  | other -> js_fail "dictionary" other
type lquery =
  | Initialize of (Prims.int * Prims.string) 
  | Initialized 
  | Shutdown 
  | Exit 
  | Cancel of Prims.int 
  | FolderChange of wsch_event 
  | ChangeConfig 
  | ChangeWatch 
  | Symbol of Prims.string 
  | ExecCommand of Prims.string 
  | DidOpen of txdoc_item 
  | DidChange of (Prims.string * Prims.string) 
  | WillSave of Prims.string 
  | WillSaveWait of Prims.string 
  | DidSave of (Prims.string * Prims.string) 
  | DidClose of Prims.string 
  | Completion of (txdoc_pos * completion_context) 
  | Resolve 
  | Hover of txdoc_pos 
  | SignatureHelp of txdoc_pos 
  | Declaration of txdoc_pos 
  | Definition of txdoc_pos 
  | TypeDefinition of txdoc_pos 
  | Implementation of txdoc_pos 
  | References 
  | DocumentHighlight of txdoc_pos 
  | DocumentSymbol 
  | CodeAction 
  | CodeLens 
  | CodeLensResolve 
  | DocumentLink 
  | DocumentLinkResolve 
  | DocumentColor 
  | ColorPresentation 
  | Formatting 
  | RangeFormatting 
  | TypeFormatting 
  | Rename 
  | PrepareRename of txdoc_pos 
  | FoldingRange 
  | BadProtocolMsg of Prims.string 
let uu___is_Initialize (projectee : lquery) : Prims.bool=
  match projectee with | Initialize _0 -> true | uu___ -> false
let __proj__Initialize__item___0 (projectee : lquery) :
  (Prims.int * Prims.string)= match projectee with | Initialize _0 -> _0
let uu___is_Initialized (projectee : lquery) : Prims.bool=
  match projectee with | Initialized -> true | uu___ -> false
let uu___is_Shutdown (projectee : lquery) : Prims.bool=
  match projectee with | Shutdown -> true | uu___ -> false
let uu___is_Exit (projectee : lquery) : Prims.bool=
  match projectee with | Exit -> true | uu___ -> false
let uu___is_Cancel (projectee : lquery) : Prims.bool=
  match projectee with | Cancel _0 -> true | uu___ -> false
let __proj__Cancel__item___0 (projectee : lquery) : Prims.int=
  match projectee with | Cancel _0 -> _0
let uu___is_FolderChange (projectee : lquery) : Prims.bool=
  match projectee with | FolderChange _0 -> true | uu___ -> false
let __proj__FolderChange__item___0 (projectee : lquery) : wsch_event=
  match projectee with | FolderChange _0 -> _0
let uu___is_ChangeConfig (projectee : lquery) : Prims.bool=
  match projectee with | ChangeConfig -> true | uu___ -> false
let uu___is_ChangeWatch (projectee : lquery) : Prims.bool=
  match projectee with | ChangeWatch -> true | uu___ -> false
let uu___is_Symbol (projectee : lquery) : Prims.bool=
  match projectee with | Symbol _0 -> true | uu___ -> false
let __proj__Symbol__item___0 (projectee : lquery) : Prims.string=
  match projectee with | Symbol _0 -> _0
let uu___is_ExecCommand (projectee : lquery) : Prims.bool=
  match projectee with | ExecCommand _0 -> true | uu___ -> false
let __proj__ExecCommand__item___0 (projectee : lquery) : Prims.string=
  match projectee with | ExecCommand _0 -> _0
let uu___is_DidOpen (projectee : lquery) : Prims.bool=
  match projectee with | DidOpen _0 -> true | uu___ -> false
let __proj__DidOpen__item___0 (projectee : lquery) : txdoc_item=
  match projectee with | DidOpen _0 -> _0
let uu___is_DidChange (projectee : lquery) : Prims.bool=
  match projectee with | DidChange _0 -> true | uu___ -> false
let __proj__DidChange__item___0 (projectee : lquery) :
  (Prims.string * Prims.string)= match projectee with | DidChange _0 -> _0
let uu___is_WillSave (projectee : lquery) : Prims.bool=
  match projectee with | WillSave _0 -> true | uu___ -> false
let __proj__WillSave__item___0 (projectee : lquery) : Prims.string=
  match projectee with | WillSave _0 -> _0
let uu___is_WillSaveWait (projectee : lquery) : Prims.bool=
  match projectee with | WillSaveWait _0 -> true | uu___ -> false
let __proj__WillSaveWait__item___0 (projectee : lquery) : Prims.string=
  match projectee with | WillSaveWait _0 -> _0
let uu___is_DidSave (projectee : lquery) : Prims.bool=
  match projectee with | DidSave _0 -> true | uu___ -> false
let __proj__DidSave__item___0 (projectee : lquery) :
  (Prims.string * Prims.string)= match projectee with | DidSave _0 -> _0
let uu___is_DidClose (projectee : lquery) : Prims.bool=
  match projectee with | DidClose _0 -> true | uu___ -> false
let __proj__DidClose__item___0 (projectee : lquery) : Prims.string=
  match projectee with | DidClose _0 -> _0
let uu___is_Completion (projectee : lquery) : Prims.bool=
  match projectee with | Completion _0 -> true | uu___ -> false
let __proj__Completion__item___0 (projectee : lquery) :
  (txdoc_pos * completion_context)=
  match projectee with | Completion _0 -> _0
let uu___is_Resolve (projectee : lquery) : Prims.bool=
  match projectee with | Resolve -> true | uu___ -> false
let uu___is_Hover (projectee : lquery) : Prims.bool=
  match projectee with | Hover _0 -> true | uu___ -> false
let __proj__Hover__item___0 (projectee : lquery) : txdoc_pos=
  match projectee with | Hover _0 -> _0
let uu___is_SignatureHelp (projectee : lquery) : Prims.bool=
  match projectee with | SignatureHelp _0 -> true | uu___ -> false
let __proj__SignatureHelp__item___0 (projectee : lquery) : txdoc_pos=
  match projectee with | SignatureHelp _0 -> _0
let uu___is_Declaration (projectee : lquery) : Prims.bool=
  match projectee with | Declaration _0 -> true | uu___ -> false
let __proj__Declaration__item___0 (projectee : lquery) : txdoc_pos=
  match projectee with | Declaration _0 -> _0
let uu___is_Definition (projectee : lquery) : Prims.bool=
  match projectee with | Definition _0 -> true | uu___ -> false
let __proj__Definition__item___0 (projectee : lquery) : txdoc_pos=
  match projectee with | Definition _0 -> _0
let uu___is_TypeDefinition (projectee : lquery) : Prims.bool=
  match projectee with | TypeDefinition _0 -> true | uu___ -> false
let __proj__TypeDefinition__item___0 (projectee : lquery) : txdoc_pos=
  match projectee with | TypeDefinition _0 -> _0
let uu___is_Implementation (projectee : lquery) : Prims.bool=
  match projectee with | Implementation _0 -> true | uu___ -> false
let __proj__Implementation__item___0 (projectee : lquery) : txdoc_pos=
  match projectee with | Implementation _0 -> _0
let uu___is_References (projectee : lquery) : Prims.bool=
  match projectee with | References -> true | uu___ -> false
let uu___is_DocumentHighlight (projectee : lquery) : Prims.bool=
  match projectee with | DocumentHighlight _0 -> true | uu___ -> false
let __proj__DocumentHighlight__item___0 (projectee : lquery) : txdoc_pos=
  match projectee with | DocumentHighlight _0 -> _0
let uu___is_DocumentSymbol (projectee : lquery) : Prims.bool=
  match projectee with | DocumentSymbol -> true | uu___ -> false
let uu___is_CodeAction (projectee : lquery) : Prims.bool=
  match projectee with | CodeAction -> true | uu___ -> false
let uu___is_CodeLens (projectee : lquery) : Prims.bool=
  match projectee with | CodeLens -> true | uu___ -> false
let uu___is_CodeLensResolve (projectee : lquery) : Prims.bool=
  match projectee with | CodeLensResolve -> true | uu___ -> false
let uu___is_DocumentLink (projectee : lquery) : Prims.bool=
  match projectee with | DocumentLink -> true | uu___ -> false
let uu___is_DocumentLinkResolve (projectee : lquery) : Prims.bool=
  match projectee with | DocumentLinkResolve -> true | uu___ -> false
let uu___is_DocumentColor (projectee : lquery) : Prims.bool=
  match projectee with | DocumentColor -> true | uu___ -> false
let uu___is_ColorPresentation (projectee : lquery) : Prims.bool=
  match projectee with | ColorPresentation -> true | uu___ -> false
let uu___is_Formatting (projectee : lquery) : Prims.bool=
  match projectee with | Formatting -> true | uu___ -> false
let uu___is_RangeFormatting (projectee : lquery) : Prims.bool=
  match projectee with | RangeFormatting -> true | uu___ -> false
let uu___is_TypeFormatting (projectee : lquery) : Prims.bool=
  match projectee with | TypeFormatting -> true | uu___ -> false
let uu___is_Rename (projectee : lquery) : Prims.bool=
  match projectee with | Rename -> true | uu___ -> false
let uu___is_PrepareRename (projectee : lquery) : Prims.bool=
  match projectee with | PrepareRename _0 -> true | uu___ -> false
let __proj__PrepareRename__item___0 (projectee : lquery) : txdoc_pos=
  match projectee with | PrepareRename _0 -> _0
let uu___is_FoldingRange (projectee : lquery) : Prims.bool=
  match projectee with | FoldingRange -> true | uu___ -> false
let uu___is_BadProtocolMsg (projectee : lquery) : Prims.bool=
  match projectee with | BadProtocolMsg _0 -> true | uu___ -> false
let __proj__BadProtocolMsg__item___0 (projectee : lquery) : Prims.string=
  match projectee with | BadProtocolMsg _0 -> _0
type lsp_query =
  {
  query_id: Prims.int FStar_Pervasives_Native.option ;
  q: lquery }
let __proj__Mklsp_query__item__query_id (projectee : lsp_query) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with | { query_id; q;_} -> query_id
let __proj__Mklsp_query__item__q (projectee : lsp_query) : lquery=
  match projectee with | { query_id; q;_} -> q
type error_code =
  | ParseError 
  | InvalidRequest 
  | MethodNotFound 
  | InvalidParams 
  | InternalError 
  | ServerErrorStart 
  | ServerErrorEnd 
  | ServerNotInitialized 
  | UnknownErrorCode 
  | RequestCancelled 
  | ContentModified 
let uu___is_ParseError (projectee : error_code) : Prims.bool=
  match projectee with | ParseError -> true | uu___ -> false
let uu___is_InvalidRequest (projectee : error_code) : Prims.bool=
  match projectee with | InvalidRequest -> true | uu___ -> false
let uu___is_MethodNotFound (projectee : error_code) : Prims.bool=
  match projectee with | MethodNotFound -> true | uu___ -> false
let uu___is_InvalidParams (projectee : error_code) : Prims.bool=
  match projectee with | InvalidParams -> true | uu___ -> false
let uu___is_InternalError (projectee : error_code) : Prims.bool=
  match projectee with | InternalError -> true | uu___ -> false
let uu___is_ServerErrorStart (projectee : error_code) : Prims.bool=
  match projectee with | ServerErrorStart -> true | uu___ -> false
let uu___is_ServerErrorEnd (projectee : error_code) : Prims.bool=
  match projectee with | ServerErrorEnd -> true | uu___ -> false
let uu___is_ServerNotInitialized (projectee : error_code) : Prims.bool=
  match projectee with | ServerNotInitialized -> true | uu___ -> false
let uu___is_UnknownErrorCode (projectee : error_code) : Prims.bool=
  match projectee with | UnknownErrorCode -> true | uu___ -> false
let uu___is_RequestCancelled (projectee : error_code) : Prims.bool=
  match projectee with | RequestCancelled -> true | uu___ -> false
let uu___is_ContentModified (projectee : error_code) : Prims.bool=
  match projectee with | ContentModified -> true | uu___ -> false
type rng =
  {
  rng_start: (Prims.int * Prims.int) ;
  rng_end: (Prims.int * Prims.int) }
let __proj__Mkrng__item__rng_start (projectee : rng) :
  (Prims.int * Prims.int)=
  match projectee with | { rng_start; rng_end;_} -> rng_start
let __proj__Mkrng__item__rng_end (projectee : rng) : (Prims.int * Prims.int)=
  match projectee with | { rng_start; rng_end;_} -> rng_end
let js_rng (uu___ : FStarC_Json.json) : rng=
  match uu___ with
  | FStarC_Json.JsonAssoc a ->
      let st = assoc "start" a in
      let fin = assoc "end" a in
      let l = assoc "line" in
      let c = assoc "character" in
      let uu___1 =
        let uu___2 =
          let uu___3 = let uu___4 = js_assoc st in l uu___4 in js_int uu___3 in
        let uu___3 =
          let uu___4 = let uu___5 = js_assoc st in c uu___5 in js_int uu___4 in
        (uu___2, uu___3) in
      let uu___2 =
        let uu___3 =
          let uu___4 = let uu___5 = js_assoc fin in l uu___5 in js_int uu___4 in
        let uu___4 =
          let uu___5 = let uu___6 = js_assoc st in c uu___6 in js_int uu___5 in
        (uu___3, uu___4) in
      { rng_start = uu___1; rng_end = uu___2 }
  | other -> js_fail "dictionary" other
let errorcode_to_int (uu___ : error_code) : Prims.int=
  match uu___ with
  | ParseError -> (Prims.of_int (-32700))
  | InvalidRequest -> (Prims.of_int (-32600))
  | MethodNotFound -> (Prims.of_int (-32601))
  | InvalidParams -> (Prims.of_int (-32602))
  | InternalError -> (Prims.of_int (-32603))
  | ServerErrorStart -> (Prims.of_int (-32099))
  | ServerErrorEnd -> (Prims.of_int (-32000))
  | ServerNotInitialized -> (Prims.of_int (-32002))
  | UnknownErrorCode -> (Prims.of_int (-32001))
  | RequestCancelled -> (Prims.of_int (-32800))
  | ContentModified -> (Prims.of_int (-32801))
let json_debug (uu___ : FStarC_Json.json) : Prims.string=
  match uu___ with
  | FStarC_Json.JsonNull -> "null"
  | FStarC_Json.JsonBool b ->
      FStarC_Format.fmt1 "bool (%s)" (if b then "true" else "false")
  | FStarC_Json.JsonInt i ->
      let uu___1 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      FStarC_Format.fmt1 "int (%s)" uu___1
  | FStarC_Json.JsonStr s -> FStarC_Format.fmt1 "string (%s)" s
  | FStarC_Json.JsonList uu___1 -> "list (...)"
  | FStarC_Json.JsonAssoc uu___1 -> "dictionary (...)"
let wrap_jsfail (qid : Prims.int FStar_Pervasives_Native.option)
  (expected : Prims.string) (got : FStarC_Json.json) : lsp_query=
  let uu___ =
    let uu___1 =
      let uu___2 = json_debug got in
      FStarC_Format.fmt2 "JSON decoding failed: expected %s, got %s" expected
        uu___2 in
    BadProtocolMsg uu___1 in
  { query_id = qid; q = uu___ }
let resultResponse (r : FStarC_Json.json) :
  assoct FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some [("result", r)]
let errorResponse (r : FStarC_Json.json) :
  assoct FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.Some [("error", r)]
let nullResponse : assoct FStar_Pervasives_Native.option=
  resultResponse FStarC_Json.JsonNull
let json_of_response (qid : Prims.int FStar_Pervasives_Native.option)
  (response : assoct) : FStarC_Json.json=
  match qid with
  | FStar_Pervasives_Native.Some i ->
      FStarC_Json.JsonAssoc
        (FStarC_List.op_At
           [("jsonrpc", (FStarC_Json.JsonStr "2.0"));
           ("id", (FStarC_Json.JsonInt i))] response)
  | FStar_Pervasives_Native.None ->
      FStarC_Json.JsonAssoc
        (FStarC_List.op_At [("jsonrpc", (FStarC_Json.JsonStr "2.0"))]
           response)
let js_resperr (err : error_code) (msg : Prims.string) : FStarC_Json.json=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = errorcode_to_int err in FStarC_Json.JsonInt uu___3 in
      ("code", uu___2) in
    [uu___1; ("message", (FStarC_Json.JsonStr msg))] in
  FStarC_Json.JsonAssoc uu___
let wrap_content_szerr (m : Prims.string) : lsp_query=
  { query_id = FStar_Pervasives_Native.None; q = (BadProtocolMsg m) }
let js_servcap : FStarC_Json.json=
  FStarC_Json.JsonAssoc
    [("capabilities",
       (FStarC_Json.JsonAssoc
          [("textDocumentSync",
             (FStarC_Json.JsonAssoc
                [("openClose", (FStarC_Json.JsonBool true));
                ("change", (FStarC_Json.JsonInt Prims.int_one));
                ("willSave", (FStarC_Json.JsonBool false));
                ("willSaveWaitUntil", (FStarC_Json.JsonBool false));
                ("save",
                  (FStarC_Json.JsonAssoc
                     [("includeText", (FStarC_Json.JsonBool true))]))]));
          ("hoverProvider", (FStarC_Json.JsonBool true));
          ("completionProvider", (FStarC_Json.JsonAssoc []));
          ("signatureHelpProvider", (FStarC_Json.JsonAssoc []));
          ("definitionProvider", (FStarC_Json.JsonBool true));
          ("typeDefinitionProvider", (FStarC_Json.JsonBool false));
          ("implementationProvider", (FStarC_Json.JsonBool false));
          ("referencesProvider", (FStarC_Json.JsonBool false));
          ("documentSymbolProvider", (FStarC_Json.JsonBool false));
          ("workspaceSymbolProvider", (FStarC_Json.JsonBool false));
          ("codeActionProvider", (FStarC_Json.JsonBool false))]))]
let js_pos (p : FStarC_Range_Type.pos) : FStarC_Json.json=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Range_Ops.line_of_pos p in
          uu___4 - Prims.int_one in
        FStarC_Json.JsonInt uu___3 in
      ("line", uu___2) in
    let uu___2 =
      let uu___3 =
        let uu___4 =
          let uu___5 = FStarC_Range_Ops.col_of_pos p in
          FStarC_Json.JsonInt uu___5 in
        ("character", uu___4) in
      [uu___3] in
    uu___1 :: uu___2 in
  FStarC_Json.JsonAssoc uu___
let js_range (r : FStarC_Range_Type.t) : FStarC_Json.json=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Range_Ops.start_of_range r in js_pos uu___3 in
      ("start", uu___2) in
    let uu___2 =
      let uu___3 =
        let uu___4 =
          let uu___5 = FStarC_Range_Ops.end_of_range r in js_pos uu___5 in
        ("end", uu___4) in
      [uu___3] in
    uu___1 :: uu___2 in
  FStarC_Json.JsonAssoc uu___
let js_dummyrange : FStarC_Json.json=
  FStarC_Json.JsonAssoc
    [("start",
       (FStarC_Json.JsonAssoc
          [("line", (FStarC_Json.JsonInt Prims.int_zero));
          ("character", (FStarC_Json.JsonInt Prims.int_zero));
          ("end",
            (FStarC_Json.JsonAssoc
               [("line", (FStarC_Json.JsonInt Prims.int_zero));
               ("character", (FStarC_Json.JsonInt Prims.int_zero))]))]))]
let js_loclink (r : FStarC_Range_Type.t) : FStarC_Json.json=
  let s = js_range r in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = FStarC_Range_Ops.file_of_range r in
              path_to_uri uu___6 in
            FStarC_Json.JsonStr uu___5 in
          ("targetUri", uu___4) in
        [uu___3; ("targetRange", s); ("targetSelectionRange", s)] in
      FStarC_Json.JsonAssoc uu___2 in
    [uu___1] in
  FStarC_Json.JsonList uu___
let pos_munge (pos : txdoc_pos) : (Prims.string * Prims.int * Prims.int)=
  ((pos.path), (pos.line + Prims.int_one), (pos.col))
let js_diag (fname : Prims.string) (msg : Prims.string)
  (r : FStarC_Range_Type.t FStar_Pervasives_Native.option) : assoct=
  let r' =
    match r with
    | FStar_Pervasives_Native.Some r1 -> js_range r1
    | FStar_Pervasives_Native.None -> js_dummyrange in
  let ds =
    ("diagnostics",
      (FStarC_Json.JsonList
         [FStarC_Json.JsonAssoc
            [("range", r'); ("message", (FStarC_Json.JsonStr msg))]])) in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = path_to_uri fname in FStarC_Json.JsonStr uu___6 in
            ("uri", uu___5) in
          [uu___4; ds] in
        FStarC_Json.JsonAssoc uu___3 in
      ("params", uu___2) in
    [uu___1] in
  ("method", (FStarC_Json.JsonStr "textDocument/publishDiagnostics")) ::
    uu___
let js_diag_clear (fname : Prims.string) : assoct=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = path_to_uri fname in FStarC_Json.JsonStr uu___6 in
            ("uri", uu___5) in
          [uu___4; ("diagnostics", (FStarC_Json.JsonList []))] in
        FStarC_Json.JsonAssoc uu___3 in
      ("params", uu___2) in
    [uu___1] in
  ("method", (FStarC_Json.JsonStr "textDocument/publishDiagnostics")) ::
    uu___
