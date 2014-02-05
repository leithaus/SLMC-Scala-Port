(*** Module that handles the generation of bound and fresh names ***)

(*** Constant declaration ***)

let bn_init = "$name"
let fn_init = "#name"
let count = ref 0

(***)

(*** Determines if a string corresponds to a bound name ***)

let is_bname s = (String.sub s 0 (min (String.length s) (String.length bn_init))) = bn_init

(*** Returns a new bound name ***)

let gen_bname () = 
  let res = bn_init^(string_of_int !count) in
  incr count; 
  res

(*** Generates a fresh name ***)

let fresh_name () =
  let res = fn_init^(string_of_int !count) in
  incr count;
  res

(*** Generates a list of fresh names ***)

let rec fresh_names size i =
  if i = size then
    []
  else
    (fresh_name())::(fresh_names size (i+1))

(***)
