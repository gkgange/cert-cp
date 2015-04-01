(* Stuff for parsing streaming-DRUP proofs. *)
type proof_line =
    Intro of int list
  | Infer of int list
  | Delete of int list
  | Hint of string option
  | Comment of string

type t = proof_line

(* Buffering code duped from genlex.ml. *)
let buffer = ref (String.create 32)
let bufpos = ref 0

let buf_push chr =
  if !bufpos >= String.length !buffer then
  begin
    let newbuffer = String.create (2 * !bufpos) in
    String.blit !buffer 0 newbuffer 0 !bufpos; buffer := newbuffer
  end;
  String.set !buffer !bufpos chr;
  incr bufpos

let buf_clear () = bufpos := 0

let buf_get () = String.sub !buffer 0 !bufpos

let rec drop_whitespace stream =
  match Stream.peek stream with
  | Some (' ' | '\010' | '\013' | '\009' | '\026' | '\012') ->
      (Stream.junk stream ; drop_whitespace stream)
  | _ -> ()

let read_int stream =
  let rec aux () =
    match Stream.peek stream with
    | Some ('0'..'9' as c) ->
        buf_push c ; Stream.junk stream ; aux ()
    | _ -> int_of_string (buf_get ())
  in
  drop_whitespace stream ;
  buf_clear () ;
  match Stream.peek stream with
  | Some '-' -> (Stream.junk stream ; - (aux ()))
  | _ -> aux ()

let rec read_clause stream =
  match read_int stream with
  | 0 -> []
  | l -> l :: read_clause stream

let read_comment stream =
  let rec aux () = 
    match Stream.peek stream with
    | None -> buf_get ()
    | Some ('\010' | '\013') -> Stream.junk stream ; buf_get ()
    | Some c -> Stream.junk stream ; buf_push c ; aux ()
  in
  buf_clear () ; drop_whitespace stream; aux ()

let read_hint stream =
  drop_whitespace stream ;
  match Stream.peek stream with
  | Some '-' ->
      let com = read_comment stream in
      if String.length com = 1 then
        Hint None
      else
        Comment com
  | Some 'c' ->
      Hint (Some (read_comment stream))
  | _ -> Comment (read_comment stream)

let next stream =
  drop_whitespace stream ;
  match Stream.peek stream with
  | None -> None
  | Some 'c' -> Stream.junk stream ; Some (read_hint stream)
  | Some 'i' -> Stream.junk stream ; Some (Intro (read_clause stream))
  | Some 'd' -> Stream.junk stream ; Some (Delete (read_clause stream))
  | _ -> Some (Infer (read_clause stream))
