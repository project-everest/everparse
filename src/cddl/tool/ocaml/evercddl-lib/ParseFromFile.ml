let parse (env: CDDLParser.state) filename =
  let ch = open_in filename in
  let lexbuf = Lexing.from_channel ch in
  let buf : (Tokens.token, CDDLParser.state) TokenBuffer.t = TokenBuffer.create (fun _ -> CDDLLexer.token lexbuf) env in
  let p = CDDLParser.cddl () in
  let res = p buf in
  close_in ch;
  res
