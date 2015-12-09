(* Parsing for different data-types. *)
(* val parse_vprop : model -> Genlex.token Stream.t -> vprop *)
module MT = MTypes
module GL = Genlex
module S = Spec

let grab_args = 
  let rec aux tl tokens =
    match Stream.peek tokens with
    | None -> raise (Stream.Error "Unmatched paren in args.")
    | Some (GL.Kwd "(") ->
        let sub = aux ((Stream.next tokens) :: tl) tokens in
        aux ((Stream.next tokens) :: sub) tokens
    | Some (GL.Kwd ")") -> tl
    | _ -> aux ((Stream.next tokens) :: tl) tokens
  in parser
    | [< 'GL.Kwd "(" ; relts = aux [] ; 'GL.Kwd ")" >] ->
        List.rev relts

