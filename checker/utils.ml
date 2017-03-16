(* Various helper functions *)
let chomp tokens token =
  let next = Stream.next tokens in
  if next <> token then
    begin
      (* Format.fprintf fmt "Parse error: expected %s, got %s." (string_of_token token) (string_of_token next) ; *)
      failwith "Parse error"
    end

let print_list
  ?pre:(pre=("@[<hov 1>[" : (unit, Format.formatter, unit) format))
  ?sep:(sep=(";@," : (unit, Format.formatter, unit) format))
  ?post:(post=("@]]" : (unit, Format.formatter, unit) format)) f fmt xs =
  Format.fprintf fmt pre ;
  begin
    match xs with
    | [] -> ()
    | (h :: tl) ->
      begin
        f fmt h ;
        List.iter (fun x ->
          Format.fprintf fmt sep ;
          f fmt x
        ) tl
      end
  end ;
  Format.fprintf fmt post

type fmtt = (unit, Format.formatter, unit) format
let print_dynarray ?sep:(sep=(";@,": fmtt)) f fmt xs =
  Format.fprintf fmt "@[<hov 1>[" ;
  if DynArray.length xs > 0 then
    begin
      f fmt (DynArray.get xs 0) ;
      for i = 1 to DynArray.length xs do
        Format.fprintf fmt sep ;
        f fmt (DynArray.get xs i)
      done 
    end ;
  Format.fprintf fmt "]@]"
(*
let print_dynarray ?sep:(sep=";") f fmt xs = print_enum ~sep:sep f fmt (DynArray.enum xs) *)
