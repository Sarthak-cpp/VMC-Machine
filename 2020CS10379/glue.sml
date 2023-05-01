(* glue.sml *)
(* Used from compiler.sml in Figure 13 in http://rogerprice.org/ug/ug.pdf *)

structure WhileLrVals = WhileLrValsFun(
              structure Token = LrParser.Token);
structure WhileLex    = WhileLexFun(
              structure Tokens = WhileLrVals.Tokens);
structure WhileParser = JoinWithArg(
              structure ParserData = WhileLrVals.ParserData
              structure Lex=WhileLex
              structure LrParser=LrParser);
