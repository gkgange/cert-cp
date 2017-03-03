(* Various helper functions *)

let print_list ?sep:(sep=(";@," : (unit, Format.formatter, unit) format)) f fmt xs =
  Format.fprintf fmt "[@[" ;
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
  Format.fprintf fmt "]@]"

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
