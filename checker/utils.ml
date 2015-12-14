(* Various helper functions *)

let print_list ?sep:(sep=";") f fmt xs =
  Format.fprintf fmt "[@[" ;
  begin
    match xs with
    | [] -> ()
    | (h :: tl) ->
      begin
        f fmt h ;
        List.iter (fun x ->
          Format.fprintf fmt "%s@ " sep ;
          f fmt x
        ) tl
      end
  end ;
  Format.fprintf fmt "]@]"

let print_enum ?sep:(sep=";") f fmt es =
  Format.fprintf fmt "[@[" ;
  begin
    match Enum.get es with
    | None -> ()
    | Some e ->
      begin
        f fmt e ;
        Enum.iter (fun e ->
          Format.fprintf fmt "%s@ " sep ;
          f fmt e
        ) es
      end
    end ;
  Format.fprintf fmt "]@]"
      
let print_dynarray ?sep:(sep=";") f fmt xs = print_enum ~sep:sep f fmt (DynArray.enum xs)
