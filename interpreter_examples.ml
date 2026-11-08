(* Execution examples for the extracted interpreter (interpreter.ml).

   Run them with:

     ocamlc -w -a -c interpreter.ml && ocaml interpreter.cmo interpreter_examples.ml

   Each example runs one step of [elts g p act tau_arg s] and prints the
   type environment and the process before and after it. An environment
   entry [n/f: t] gives a name, its visibility flag and its type. The schedule [s] selects the redex at each
   parallel composition: SParL / SParR step inside one component, SComL makes
   the left component output and the right one input, SComR is the opposite.
   The script exits with status 1 if an example does not behave as expected. *)

open Interpreter

(* Names *)
let a = (1, 1)
let v = (2, 2)
let c = (3, 3)
let b = (4, 4)
let w = (5, 5)
(* Bound names: the typing rules for input require [snd x < max (domain g)]. *)
let x = (9, 1)
let y = (8, 1)

let name (n : int * int) =
  if n = a then "a"
  else if n = v then "v"
  else if n = c then "c"
  else if n = b then "b"
  else if n = w then "w"
  else if n = x then "x"
  else if n = y then "y"
  else Printf.sprintf "n%d.%d" (Stdlib.fst n) (Stdlib.snd n)

(* Process constructors on pairs of labels *)
let out (u1, u2) (v1, v2) k = DOut (u1, u2, v1, v2, k)
let inp (u1, u2) (x1, x2) k = DInp (u1, u2, x1, x2, k)
let bang (u1, u2) (x1, x2) k = DBang (u1, u2, x1, x2, k)
let nu (c1, c2) k = DNu (c1, c2, k)
let ( ||| ) p q = DPar (p, q)
let nil = DZero

(* Actions *)
let send (u1, u2) (v1, v2) = AOut (u1, u2, v1, v2)
let recv (u1, u2) (v1, v2) = AIn (u1, u2, v1, v2)
let tau (u1, u2) = ATau (u1, u2)

(* Printers *)
let rec proc = function
  | DZero -> "0"
  | DOut (a1, a2, b1, b2, DZero) ->
      Printf.sprintf "%s!%s" (name (a1, a2)) (name (b1, b2))
  | DOut (a1, a2, b1, b2, k) ->
      Printf.sprintf "%s!%s.%s" (name (a1, a2)) (name (b1, b2)) (proc k)
  | DInp (a1, a2, x1, x2, DZero) ->
      Printf.sprintf "%s?%s" (name (a1, a2)) (name (x1, x2))
  | DInp (a1, a2, x1, x2, k) ->
      Printf.sprintf "%s?%s.%s" (name (a1, a2)) (name (x1, x2)) (proc k)
  | DBang (a1, a2, x1, x2, k) ->
      Printf.sprintf "*%s?%s.%s" (name (a1, a2)) (name (x1, x2)) (proc k)
  | DPar (p, q) -> Printf.sprintf "(%s | %s)" (proc p) (proc q)
  | DNu (c1, c2, k) -> Printf.sprintf "(nu %s)%s" (name (c1, c2)) (proc k)

let action = function
  | AOut (a1, a2, b1, b2) -> Printf.sprintf "%s!%s" (name (a1, a2)) (name (b1, b2))
  | AIn (a1, a2, b1, b2) -> Printf.sprintf "%s?%s" (name (a1, a2)) (name (b1, b2))
  | ATau (a1, a2) -> Printf.sprintf "tau@%s" (name (a1, a2))

let rec schedule = function
  | SLeaf -> "SLeaf"
  | SParL s -> Printf.sprintf "SParL (%s)" (schedule s)
  | SParR s -> Printf.sprintf "SParR (%s)" (schedule s)
  | SComL (s1, s2) -> Printf.sprintf "SComL (%s, %s)" (schedule s1) (schedule s2)
  | SComR (s1, s2) -> Printf.sprintf "SComR (%s, %s)" (schedule s1) (schedule s2)

let flag = function Hid -> "hid" | Ill -> "ill" | Vis -> "vis"

let polarity = function
  | Empty -> "empty"
  | Inp -> "in"
  | Out -> "out"
  | Io -> "io"

let multiplicity = function Lin -> "lin" | Un -> "un"

let rec piType = function
  | Top -> "Top"
  | Chan (m, p, t) ->
      Printf.sprintf "%s %s[%s]" (multiplicity m) (polarity p) (piType t)

let env g =
  let entry ((n, f), t) =
    Printf.sprintf "%s/%s: %s" (name n) (flag f) (piType t) in
  "{" ^ String.concat ", " (List.map entry g) ^ "}"

(* Running the examples *)
type expected = Fires | Stuck

let failures = ref 0

let report expected fired =
  let ok = (expected = Fires) = fired in
  if not ok then incr failures;
  if ok then "" else "   <-- UNEXPECTED"

let step title g p act tau_arg s expected =
  Printf.printf "\n%s\n  env:   %s\n  %s  --%s-->  [%s]\n"
    title (env g) (proc p) (action act) (schedule s);
  match elts g p act tau_arg s with
  | Some (g', p') ->
      Printf.printf "  env':  %s\n  fires: %s%s\n" (env g') (proc p') (report expected true);
      Some (g', p')
  | None ->
      Printf.printf "  stuck%s\n" (report expected false);
      None

let example title g p act tau_arg s expected =
  ignore (step title g p act tau_arg s expected)

(* Typing environments *)
let chan m p = Chan (m, p, Top)
let lin_a = ((a, Vis), chan Lin Io)
let un_a = ((a, Vis), chan Un Io)
let lin_b = ((b, Vis), chan Lin Io)
let top_v = ((v, Vis), Top)
let top_w = ((w, Vis), Top)
let hid_c = ((c, Hid), Top)
let leaves = SComL (SLeaf, SLeaf)
let rleaves = SComR (SLeaf, SLeaf)

let () =
  print_endline "== Communication ==";
  example "Left rule: output on the left (lcomL)"
    [lin_a; top_v] (out a v nil ||| inp a x nil) (tau a) (Some v) leaves Fires;
  example "Right rule: output on the right (lcomR)"
    [lin_a; top_v] (inp a x nil ||| out a v nil) (tau a) (Some v) rleaves Fires;
  example "Wrong side: the schedule expects the output on the left"
    [lin_a; top_v] (inp a x nil ||| out a v nil) (tau a) (Some v) leaves Stuck;
  example "Unrestricted channel, right rule (ucomR)"
    [un_a; top_v] (inp a x nil ||| out a v nil) (tau a) (Some v) rleaves Fires;

  print_endline "\n== Choosing a redex ==";
  let two = out a v (out a w nil) ||| out a w nil in
  let g = [un_a; top_v; top_w] in
  example "Same process, left output selected (parL)"
    g two (send a v) None (SParL SLeaf) Fires;
  example "The right component cannot perform this output"
    g two (send a v) None (SParR SLeaf) Stuck;
  example "Same process, right output selected (parR)"
    g two (send a w) None (SParR SLeaf) Fires;
  example "Sender nested on the right of the left component"
    [lin_a; top_v] ((nil ||| out a v nil) ||| inp a x nil)
    (tau a) (Some v) (SComL (SParR SLeaf, SLeaf)) Fires;
  example "A communication inside the right component (parR)"
    [lin_a; top_v] (nil ||| (inp a x nil ||| out a v nil))
    (tau a) (Some v) (SParR rleaves) Fires;

  print_endline "\n== Restriction ==";
  let g = [lin_a; top_v; hid_c] in
  example "Communication under a restriction (hide)"
    g (nu c (out a v nil ||| inp a x nil)) (tau a) (Some v) leaves Fires;
  example "Right-rule communication under a restriction"
    g (nu c (inp a x nil ||| out a v nil)) (tau a) (Some v) rleaves Fires;
  example "Input on another channel under a restriction"
    [((a, Vis), chan Lin Inp); top_v; hid_c]
    (nu c (inp a x nil)) (recv a v) None SLeaf Fires;
  example "Input whose object is the restricted name"
    [((a, Vis), chan Lin Inp); top_v; hid_c]
    (nu c (inp a x nil)) (recv a c) None SLeaf Stuck;
  example "Scope extrusion of the restricted name (open)"
    [un_a; hid_c] (nu c (out a c nil)) (send a c) None SLeaf Fires;
  example "Scope extrusion to the other component (lclsL)"
    [lin_a; hid_c] (nu c (out a c nil) ||| inp a x nil)
    (tau a) (Some c) leaves Fires;
  example "Scope extrusion, output on the right (lclsR)"
    [lin_a; hid_c] (inp a x nil ||| nu c (out a c nil))
    (tau a) (Some c) rleaves Fires;
  example "A hidden name cannot be sent outside its restriction"
    [lin_a; hid_c] (out a c nil ||| inp a x nil)
    (tau a) (Some c) leaves Stuck;

  print_endline "\n== Replication ==";
  example "Replicated input consumes a message and stays available"
    [un_a; top_v] (bang a x nil ||| out a v nil) (tau a) (Some v) rleaves Fires;

  print_endline "\n== A two-step run ==";
  let g = [lin_a; lin_b; top_v] in
  let p = out a v (out b v nil) ||| inp a x (inp b y nil) in
  (match step "First synchronisation on a" g p (tau a) (Some v) leaves Fires with
   | Some (g1, p1) ->
       ignore (step "Second synchronisation on b" g1 p1 (tau b) (Some v) leaves Fires)
   | None -> ());

  if !failures = 0 then print_endline "\nAll examples behaved as expected."
  else begin
    Printf.printf "\n%d example(s) did not behave as expected.\n" !failures;
    exit 1
  end
