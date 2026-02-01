(** Warning: The extraction is currently set to bypass opacity, the
following opaque constant bodies have been accessed
: nat_pair_eq_dec.
 [extraction-opaque-accessed,extraction] *)


(** val andb : bool -> bool -> bool **)

let andb = (&&)

(** val negb : bool -> bool **)

let negb = not

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| _,y -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app = (@)

(** val add : int -> int -> int **)

let rec add = (+)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb = (<)
 end

(** val nat_pair_eq_dec : (int*int) -> (int*int) -> bool **)

let nat_pair_eq_dec n m =
  let x,x0 = n in
  let n0,n1 = m in
  if let rec f n2 x1 =
       (fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> true)
           (fun _ -> false)
           x1)
         (fun n3 ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> false)
           (fun n4 -> f n3 n4)
           x1)
         n2
     in f x n0
  then let rec f n2 x1 =
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> true)
             (fun _ -> false)
             x1)
           (fun n3 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> false)
             (fun n4 -> f n3 n4)
             x1)
           n2
       in f x0 n1
  else false

(** val pair_eq : (int*int) -> (int*int) -> bool **)

let pair_eq = (=)

type dproc =
| DZero
| DBang of int * int * int * int * dproc
| DPar of dproc * dproc
| DNu of int * int * dproc
| DInp of int * int * int * int * dproc
| DOut of int * int * int * int * dproc

(** val secLabs : dproc -> (int*int) list **)

let rec secLabs = function
| DZero -> []
| DBang (_, _, _, _, p0) -> secLabs p0
| DPar (p0, q) -> app (secLabs q) (secLabs p0)
| DNu (h, i, p0) -> app (secLabs p0) ((h,i)::[])
| DInp (_, _, _, _, p0) -> secLabs p0
| DOut (_, _, _, _, p0) -> secLabs p0

(** val mv : (int*int) -> (int*int) -> (int*int) -> int*int **)

let mv py pz pv =
  let y1 = fst py in
  let y2 = snd py in
  let z1 = fst pz in
  let z2 = snd pz in
  let v1 = fst pv in
  let v2 = snd pv in
  if andb ((=) y1 z1) ((=) y2 z2) then v1,v2 else y1,y2

(** val pmap : dproc -> int -> int -> int -> int -> dproc **)

let rec pmap p z1 z2 v1 v2 =
  match p with
  | DZero -> p
  | DBang (x1, x2, y1, y2, q) ->
    let r = mv (x1,x2) (z1,z2) (v1,v2) in
    DBang ((fst r), (snd r), y1, y2, (pmap q z1 z2 v1 v2))
  | DPar (p0, q) ->
    DPar ((pmap p0 z1 z2 v1 v2), (pmap q z1 z2 v1 v2))
  | DNu (h, i, q) -> DNu (h, i, (pmap q z1 z2 v1 v2))
  | DInp (x1, x2, y1, y2, q) ->
    let r = mv (x1,x2) (z1,z2) (v1,v2) in
    DInp ((fst r), (snd r), y1, y2, (pmap q z1 z2 v1 v2))
  | DOut (x1, x2, y1, y2, p0) ->
    let r1 = mv (x1,x2) (z1,z2) (v1,v2) in
    let r2 = mv (y1,y2) (z1,z2) (v1,v2) in
    DOut ((fst r1), (snd r1), (fst r2), (snd r2),
    (pmap p0 z1 z2 v1 v2))

(** val max : (int*int) list -> int **)

let rec max = function
| [] -> 0
| p::t0 ->
  let _,x = p in let m = max t0 in if Nat.ltb x m then m else x

(** val dep_relabel : dproc -> (int*int) list -> dproc **)

let rec dep_relabel p s =
  match p with
  | DZero -> p
  | DBang (x1, x2, y1, y2, p0) ->
    DBang (x1, x2, y1, y2, (dep_relabel p0 s))
  | DPar (p0, q) -> DPar ((dep_relabel p0 s), (dep_relabel q s))
  | DNu (h, i, p0) ->
    DNu (h, (add i (max s)),
      (pmap (dep_relabel p0 s) h i h (add i (max s))))
  | DInp (x1, x2, y1, y2, p0) ->
    DInp (x1, x2, y1, y2, (dep_relabel p0 s))
  | DOut (x1, x2, y1, y2, p0) ->
    DOut (x1, x2, y1, y2, (dep_relabel p0 s))

type pol =
| Empty
| Inp
| Out
| Io

type mode =
| Lin
| Un

type piType =
| Chan of mode * pol * piType
| Top

type flag =
| Hid
| Ill
| Vis

type typeEnv = (((int*int)*flag)*piType) list

(** val pol_eq : pol -> pol -> bool **)

let rec pol_eq p1 p2 =
  match p1 with
  | Empty -> (match p2 with
              | Empty -> true
              | _ -> false)
  | Inp -> (match p2 with
            | Inp -> true
            | _ -> false)
  | Out -> (match p2 with
            | Out -> true
            | _ -> false)
  | Io -> (match p2 with
           | Io -> true
           | _ -> false)

(** val mode_eq : mode -> mode -> bool **)

let rec mode_eq m1 m2 =
  match m1 with
  | Lin -> (match m2 with
            | Lin -> true
            | Un -> false)
  | Un -> (match m2 with
           | Lin -> false
           | Un -> true)

(** val type_eq : piType -> piType -> bool **)

let rec type_eq t1 t2 =
  match t1 with
  | Chan (m1, p1, t3) ->
    (match t2 with
     | Chan (m2, p2, t4) ->
       if mode_eq m1 m2
       then if pol_eq p1 p2 then type_eq t3 t4 else false
       else false
     | Top -> false)
  | Top -> (match t2 with
            | Chan (_, _, _) -> false
            | Top -> true)

(** val flag_eq : flag -> flag -> bool **)

let rec flag_eq f1 f2 =
  match f1 with
  | Hid -> (match f2 with
            | Hid -> true
            | _ -> false)
  | Ill -> (match f2 with
            | Ill -> true
            | _ -> false)
  | Vis -> (match f2 with
            | Vis -> true
            | _ -> false)

(** val removeEntry :
    (int*int) -> typeEnv -> (((int*int)*flag)*piType) list **)

let rec removeEntry y = function
| [] -> []
| p::tail ->
  let p0,t0 = p in
  let x,f = p0 in
  if pair_eq x y then tail else ((x,f),t0)::(removeEntry y tail)

(** val pol_cup : pol -> pol -> pol **)

let rec pol_cup p1 p2 =
  match p1 with
  | Empty -> p2
  | Inp -> (match p2 with
            | Empty -> Inp
            | Inp -> Inp
            | _ -> Io)
  | Out -> (match p2 with
            | Empty -> Out
            | Inp -> Io
            | x -> x)
  | Io -> Io

(** val domain : typeEnv -> (int*int) list **)

let rec domain = function
| [] -> []
| p::t0 -> let p0,_ = p in let x,_ = p0 in x::(domain t0)

type action =
| AIn of int * int * int * int
| AOut of int * int * int * int
| ATau of int * int

(** val inB :
    (int*int) -> (((int*int)*flag)*piType) list ->
    (flag*piType)*bool **)

let rec inB a = function
| [] -> (Ill,Top),false
| y::m ->
  let y0,t0 = y in
  let b,f = y0 in if pair_eq a b then (f,t0),true else inB a m

(** val newEntries : typeEnv -> (int*int) list -> int -> typeEnv **)

let rec newEntries g l max0 =
  match l with
  | [] -> []
  | p::tail ->
    let a1,a2 = p in
    let _,notNew = inB (a1,a2) g in
    if notNew
    then newEntries g tail max0
    else let pair,_ = inB (a1,(sub a2 max0)) g in
         (((a1,a2),(fst pair)),(snd pair))::(newEntries g tail max0)

type 'a t = 'a option

(** val raise : 'a1 t **)

let raise =
  None

(** val tplus : piType -> piType -> piType option **)

let tplus t1 t2 =
  match t1 with
  | Chan (m, p1, r1) ->
    (match m with
     | Lin ->
       (match t2 with
        | Chan (m0, p2, r2) ->
          (match m0 with
           | Lin ->
             if type_eq r1 r2
             then (match p1 with
                   | Empty -> Some t2
                   | Inp ->
                     (match p2 with
                      | Empty -> Some t1
                      | Out -> Some (Chan (Lin, Io, r1))
                      | _ -> raise)
                   | Out ->
                     (match p2 with
                      | Empty -> Some t1
                      | Inp -> Some (Chan (Lin, Io, r1))
                      | _ -> raise)
                   | Io ->
                     (match p2 with
                      | Empty -> Some t1
                      | _ -> raise))
             else raise
           | Un -> raise)
        | Top -> raise)
     | Un ->
       (match t2 with
        | Chan (m0, p2, r2) ->
          (match m0 with
           | Lin -> raise
           | Un ->
             if type_eq r1 r2
             then Some (Chan (Un, (pol_cup p1 p2), r1))
             else raise)
        | Top -> raise))
  | Top -> (match t2 with
            | Chan (_, _, _) -> raise
            | Top -> Some Top)

(** val tremove : piType -> piType -> piType option **)

let tremove t1 t2 =
  match t1 with
  | Chan (m, p1, r1) ->
    (match m with
     | Lin ->
       (match t2 with
        | Chan (m0, p2, r2) ->
          (match m0 with
           | Lin ->
             if type_eq r1 r2
             then (match p1 with
                   | Empty ->
                     (match p2 with
                      | Empty -> Some t1
                      | _ -> raise)
                   | Inp ->
                     (match p2 with
                      | Empty -> Some t1
                      | Inp -> Some (Chan (Lin, Empty, r1))
                      | _ -> raise)
                   | Out ->
                     (match p2 with
                      | Empty -> Some t1
                      | Out -> Some (Chan (Lin, Empty, r1))
                      | _ -> raise)
                   | Io ->
                     (match p2 with
                      | Empty -> Some t1
                      | Inp -> Some (Chan (Lin, Out, r1))
                      | Out -> Some (Chan (Lin, Inp, r1))
                      | Io -> Some (Chan (Lin, Empty, r1))))
             else raise
           | Un -> raise)
        | Top -> raise)
     | Un ->
       (match t2 with
        | Chan (m0, p2, r2) ->
          (match m0 with
           | Lin -> raise
           | Un ->
             if type_eq r1 r2
             then (match p1 with
                   | Empty ->
                     (match p2 with
                      | Empty -> Some t1
                      | _ -> raise)
                   | Inp ->
                     (match p2 with
                      | Empty -> Some t1
                      | Inp -> Some t1
                      | _ -> raise)
                   | Out ->
                     (match p2 with
                      | Empty -> Some t1
                      | Out -> Some t1
                      | _ -> raise)
                   | Io -> Some t1)
             else raise)
        | Top -> raise))
  | Top -> (match t2 with
            | Chan (_, _, _) -> raise
            | Top -> Some Top)

(** val typeEnv_eq :
    (((int*int)*flag)*piType) list -> (((int*int)*flag)*piType)
    list -> bool **)

let rec typeEnv_eq g1 g2 =
  match g1 with
  | [] -> (match g2 with
           | [] -> true
           | _::_ -> false)
  | p::d1 ->
    let p0,t1 = p in
    let p1,f1 = p0 in
    (match g2 with
     | [] -> false
     | p2::d2 ->
       let p3,t2 = p2 in
       let p4,f2 = p3 in
       andb
         (andb (andb (pair_eq p1 p4) (flag_eq f1 f2))
           (type_eq t1 t2)) (typeEnv_eq d1 d2))

(** val changeVis :
    (int*int) -> typeEnv -> (((int*int)*flag)*piType) list **)

let rec changeVis a = function
| [] -> []
| p::tl ->
  let p0,t0 = p in
  let b,f = p0 in
  if pair_eq a b
  then ((b,Vis),t0)::tl
  else ((b,f),t0)::(changeVis a tl)

(** val changeHid :
    (int*int) -> typeEnv -> (((int*int)*flag)*piType) list **)

let rec changeHid a = function
| [] -> []
| p::tl ->
  let p0,t0 = p in
  let b,f = p0 in
  if pair_eq a b
  then ((b,Hid),t0)::tl
  else ((b,f),t0)::(changeHid a tl)

(** val posB : (int*int) list -> bool **)

let rec posB = function
| [] -> true
| p::tl -> let _,n = p in andb (Nat.ltb 0 n) (posB tl)

(** val inB0 : (int*int) -> (int*int) list -> bool **)

let rec inB0 n = function
| [] -> false
| h::tl -> (||) (pair_eq n h) (inB0 n tl)

(** val inclB : (int*int) list -> (int*int) list -> bool **)

let rec inclB l1 l2 =
  match l1 with
  | [] -> true
  | h::tl -> andb (inB0 h l2) (inclB tl l2)

(** val nodupb : (int*int) list -> bool **)

let rec nodupb = function
| [] -> true
| a::tl -> andb (negb (inB0 a tl)) (nodupb tl)

type bothRedexesChange = bool

(** val elts :
    typeEnv -> dproc -> action -> (int*int) option ->
    bothRedexesChange -> (typeEnv*dproc) option **)

let rec elts g p act tau_arg b =
  match p with
  | DZero -> raise
  | DBang (a1, a2, x1, x2, q) ->
    (match act with
     | AIn (c1, c2, b1, b2) ->
       if pair_eq (a1,a2) (c1,c2)
       then let p0,b0 = inB (a1,a2) g in
            let f0,p1 = p0 in
            (match f0 with
             | Vis ->
               (match p1 with
                | Chan (m, pl, t0) ->
                  (match m with
                   | Lin -> raise
                   | Un ->
                     if b0
                     then let p2,b3 = inB (b1,b2) g in
                          let f,s = p2 in
                          if b3
                          then if andb
                                    ((||) (pol_eq pl Inp)
                                      (pol_eq pl Io))
                                    (negb (flag_eq f Hid))
                               then (match tplus s t0 with
                                     | Some r ->
                                       let rq =
                                         dep_relabel q (domain g)
                                       in
                                       let d =
                                         app
                                           (newEntries g
                                             (secLabs rq)
                                             (max (domain g)))
                                           ((((b1,b2),Vis),r)::
                                           (removeEntry (b1,b2) g))
                                       in
                                       Some (d,(DPar
                                       ((pmap q x1 x2 b1 b2),
                                       (DBang (a1, a2, x1, x2,
                                       rq)))))
                                     | None -> raise)
                               else raise
                          else raise
                     else raise)
                | Top -> raise)
             | _ -> raise)
       else raise
     | _ -> raise)
  | DPar (q1, q2) ->
    (match act with
     | ATau (a1, a2) ->
       if b
       then (match tau_arg with
             | Some p0 ->
               let b1,b2 = p0 in
               if nat_pair_eq_dec (a1,a2) (b1,b2)
               then raise
               else let p1,b0 = inB (a1,a2) g in
                    let f,p2 = p1 in
                    (match f with
                     | Vis ->
                       (match p2 with
                        | Chan (m, p3, t0) ->
                          (match m with
                           | Lin ->
                             (match p3 with
                              | Io ->
                                if b0
                                then let p4,b3 = inB (b1,b2) g in
                                     let f0,s = p4 in
                                     (match f0 with
                                      | Hid ->
                                        if b3
                                        then (match tremove s t0 with
                                              | Some r ->
                                                let g0 =
                                                  removeEntry
                                                    (a1,a2)
                                                    (removeEntry
                                                      (b1,b2) g)
                                                in
                                                let act1 = AOut
                                                  (a1, a2, b1, b2)
                                                in
                                                let d1 =
                                                  (((a1,a2),Vis),(Chan
                                                  (Lin, Out,
                                                  t0)))::((((b1,b2),Hid),s)::g0)
                                                in
                                                let act2 = AIn (a1,
                                                  a2, b1, b2)
                                                in
                                                let d2 =
                                                  (((a1,a2),Vis),(Chan
                                                  (Lin, Inp,
                                                  t0)))::((((b1,b2),Ill),r)::g0)
                                                in
                                                (match elts d1 q1
                                                         act1 None
                                                         false with
                                                 | Some p5 ->
                                                   let d',q' = p5 in
                                                   (match elts d2
                                                          q2 act2
                                                          None false with
                                                    | Some p6 ->
                                                      let d'',q'' =
                                                        p6
                                                      in
                                                      if andb
                                                          (typeEnv_eq
                                                          d'
                                                          ((((a1,a2),Vis),(Chan
                                                          (Lin,
                                                          Empty,
                                                          t0)))::((((b1,b2),Vis),r)::g0)))
                                                          (typeEnv_eq
                                                          d''
                                                          ((((a1,a2),Vis),(Chan
                                                          (Lin,
                                                          Empty,
                                                          t0)))::((((b1,b2),Vis),s)::g0)))
                                                      then 
                                                        let d''' =
                                                          (((a1,a2),Vis),(Chan
                                                          (Lin,
                                                          Empty,
                                                          t0)))::((((b1,b2),Hid),s)::g0)
                                                        in
                                                        Some
                                                        (d''',(DNu
                                                        (b1, b2,
                                                        (DPar (q',
                                                        q'')))))
                                                      else raise
                                                    | None -> raise)
                                                 | None -> raise)
                                              | None -> raise)
                                        else raise
                                      | Ill -> raise
                                      | Vis ->
                                        if b3
                                        then (match tremove s t0 with
                                              | Some r ->
                                                let g0 =
                                                  removeEntry
                                                    (a1,a2)
                                                    (removeEntry
                                                      (b1,b2) g)
                                                in
                                                let act1 = AOut
                                                  (a1, a2, b1, b2)
                                                in
                                                let d1 =
                                                  (((a1,a2),Vis),(Chan
                                                  (Lin, Out,
                                                  t0)))::((((b1,b2),Vis),s)::g0)
                                                in
                                                let act2 = AIn (a1,
                                                  a2, b1, b2)
                                                in
                                                let d2 =
                                                  (((a1,a2),Vis),(Chan
                                                  (Lin, Inp,
                                                  t0)))::((((b1,b2),Vis),r)::g0)
                                                in
                                                (match elts d1 q1
                                                         act1 None
                                                         false with
                                                 | Some p5 ->
                                                   let d',q' = p5 in
                                                   (match elts d2
                                                          q2 act2
                                                          None false with
                                                    | Some p6 ->
                                                      let d'',q'' =
                                                        p6
                                                      in
                                                      if andb
                                                          (typeEnv_eq
                                                          d'
                                                          ((((a1,a2),Vis),(Chan
                                                          (Lin,
                                                          Empty,
                                                          t0)))::((((b1,b2),Vis),r)::g0)))
                                                          (typeEnv_eq
                                                          d''
                                                          ((((a1,a2),Vis),(Chan
                                                          (Lin,
                                                          Empty,
                                                          t0)))::((((b1,b2),Vis),s)::g0)))
                                                      then 
                                                        Some
                                                          (d'',(DPar
                                                          (q',
                                                          q'')))
                                                      else raise
                                                    | None -> raise)
                                                 | None -> raise)
                                              | None -> raise)
                                        else raise)
                                else raise
                              | _ -> raise)
                           | Un ->
                             (match p3 with
                              | Io ->
                                if b0
                                then let p4,b3 = inB (b1,b2) g in
                                     let f0,s = p4 in
                                     (match f0 with
                                      | Hid ->
                                        if b3
                                        then (match tremove s t0 with
                                              | Some r ->
                                                let g0 =
                                                  removeEntry
                                                    (b1,b2) g
                                                in
                                                let act1 = AOut
                                                  (a1, a2, b1, b2)
                                                in
                                                let act2 = AIn (a1,
                                                  a2, b1, b2)
                                                in
                                                let d2 =
                                                  (((b1,b2),Ill),r)::g0
                                                in
                                                (match elts g q1
                                                         act1 None
                                                         false with
                                                 | Some p5 ->
                                                   let d',q' = p5 in
                                                   (match elts d2
                                                          q2 act2
                                                          None false with
                                                    | Some p6 ->
                                                      let d'',q'' =
                                                        p6
                                                      in
                                                      let p7,b4 =
                                                        inB (a1,a2)
                                                          d''
                                                      in
                                                      let f1,ta = p7
                                                      in
                                                      (match f1 with
                                                       | Vis ->
                                                         if b4
                                                         then 
                                                          let p8,b5 =
                                                          inB
                                                          (b1,b2)
                                                          d''
                                                          in
                                                          let f2,tb =
                                                          p8
                                                          in
                                                          (
                                                          match f2 with
                                                          | Vis ->
                                                          if b5
                                                          then 
                                                          if 
                                                          andb
                                                          (andb
                                                          (typeEnv_eq
                                                          d'
                                                          ((((b1,b2),Vis),r)::g0))
                                                          (type_eq
                                                          ta (Chan
                                                          (Un, Io,
                                                          t0))))
                                                          (type_eq
                                                          tb s)
                                                          then 
                                                          let d''' =
                                                          (((b1,b2),Hid),tb)::
                                                          (removeEntry
                                                          (b1,b2)
                                                          d'')
                                                          in
                                                          Some
                                                          (d''',(DNu
                                                          (b1, b2,
                                                          (DPar
                                                          (q',
                                                          q'')))))
                                                          else raise
                                                          else raise
                                                          | _ ->
                                                          raise)
                                                         else raise
                                                       | _ -> raise)
                                                    | None -> raise)
                                                 | None -> raise)
                                              | None -> raise)
                                        else raise
                                      | Ill -> raise
                                      | Vis ->
                                        if b3
                                        then (match tremove s t0 with
                                              | Some r ->
                                                let g0 =
                                                  removeEntry
                                                    (b1,b2) g
                                                in
                                                let act1 = AOut
                                                  (a1, a2, b1, b2)
                                                in
                                                let act2 = AIn (a1,
                                                  a2, b1, b2)
                                                in
                                                let d2 =
                                                  (((b1,b2),Vis),r)::g0
                                                in
                                                (match elts g q1
                                                         act1 None
                                                         false with
                                                 | Some p5 ->
                                                   let d',q' = p5 in
                                                   (match elts d2
                                                          q2 act2
                                                          None false with
                                                    | Some p6 ->
                                                      let d'',q'' =
                                                        p6
                                                      in
                                                      let p7,b4 =
                                                        inB (a1,a2)
                                                          d''
                                                      in
                                                      let f1,ta = p7
                                                      in
                                                      (match f1 with
                                                       | Vis ->
                                                         if b4
                                                         then 
                                                          let p8,b5 =
                                                          inB
                                                          (b1,b2)
                                                          d''
                                                          in
                                                          let f2,tb =
                                                          p8
                                                          in
                                                          (
                                                          match f2 with
                                                          | Vis ->
                                                          if b5
                                                          then 
                                                          if 
                                                          andb
                                                          (andb
                                                          (typeEnv_eq
                                                          d'
                                                          ((((b1,b2),Vis),r)::g0))
                                                          (type_eq
                                                          ta (Chan
                                                          (Un, Io,
                                                          t0))))
                                                          (type_eq
                                                          tb s)
                                                          then 
                                                          Some
                                                          (d'',(DPar
                                                          (q',
                                                          q'')))
                                                          else raise
                                                          else raise
                                                          | _ ->
                                                          raise)
                                                         else raise
                                                       | _ -> raise)
                                                    | None -> raise)
                                                 | None -> raise)
                                              | None -> raise)
                                        else raise)
                                else raise
                              | _ -> raise))
                        | Top -> raise)
                     | _ -> raise)
             | None -> raise)
       else raise
     | _ ->
       (match elts g q1 act tau_arg false with
        | Some p0 -> let d',q' = p0 in Some (d',(DPar (q', q2)))
        | None -> raise))
  | DNu (b1, b2, q) ->
    (match act with
     | AOut (a1, a2, c1, c2) ->
       if pair_eq (b1,b2) (a1,a2)
       then raise
       else if pair_eq (b1,b2) (c1,c2)
            then let p0,b0 = inB (b1,b2) g in
                 let f,t0 = p0 in
                 (match f with
                  | Hid ->
                    if b0
                    then let d1 =
                           (((b1,b2),Vis),t0)::(removeEntry (b1,b2)
                                                 g)
                         in
                         elts d1 q act None false
                    else raise
                  | _ -> raise)
            else let p0,b0 = inB (b1,b2) g in
                 let f,_ = p0 in
                 (match f with
                  | Hid ->
                    if b0
                    then let sl = secLabs p in
                         let dg = domain g in
                         if andb
                              (andb (andb (inclB sl dg) (posB sl))
                                (nodupb sl))
                              ((<=) (max sl) (max dg))
                         then (match elts (changeVis (b1,b2) g) q
                                       act None false with
                               | Some p1 ->
                                 let g2,q' = p1 in
                                 let p2,b3 = inB (b1,b2) g2 in
                                 let f0,_ = p2 in
                                 (match f0 with
                                  | Vis ->
                                    if b3
                                    then Some
                                           ((changeHid (b1,b2) g2),(DNu
                                           (b1, b2, q')))
                                    else raise
                                  | _ -> raise)
                               | None -> raise)
                         else raise
                    else raise
                  | _ -> raise)
     | _ -> raise)
  | DInp (a1, a2, x1, x2, q) ->
    (match act with
     | AIn (c1, c2, b1, b2) ->
       if pair_eq (a1,a2) (c1,c2)
       then let p0,b0 = inB (a1,a2) g in
            let f0,p1 = p0 in
            (match f0 with
             | Vis ->
               (match p1 with
                | Chan (m, pl, t0) ->
                  (match m with
                   | Lin ->
                     (match pl with
                      | Inp ->
                        if b0
                        then let p2,b3 = inB (b1,b2) g in
                             let f,s = p2 in
                             if b3
                             then if negb (flag_eq f Hid)
                                  then (match tplus s t0 with
                                        | Some r ->
                                          let d =
                                            (((a1,a2),Vis),(Chan
                                            (Lin, Empty,
                                            t0)))::((((b1,b2),Vis),r)::
                                            (removeEntry (a1,a2)
                                              (removeEntry (b1,b2)
                                                g)))
                                          in
                                          Some
                                          (d,(pmap q x1 x2 b1 b2))
                                        | None -> raise)
                                  else raise
                             else raise
                        else raise
                      | _ -> raise)
                   | Un ->
                     if b0
                     then let p2,b3 = inB (b1,b2) g in
                          let f,s = p2 in
                          if b3
                          then if andb
                                    ((||) (pol_eq pl Inp)
                                      (pol_eq pl Io))
                                    (negb (flag_eq f Hid))
                               then (match tplus s t0 with
                                     | Some r ->
                                       let d =
                                         (((b1,b2),Vis),r)::
                                         (removeEntry (b1,b2) g)
                                       in
                                       Some (d,(pmap q x1 x2 b1 b2))
                                     | None -> raise)
                               else raise
                          else raise
                     else raise)
                | Top -> raise)
             | _ -> raise)
       else raise
     | _ -> raise)
  | DOut (a1, a2, b1, b2, q) ->
    (match act with
     | AOut (c1, c2, d1, d2) ->
       if andb (pair_eq (a1,a2) (c1,c2)) (pair_eq (b1,b2) (d1,d2))
       then let p0,b0 = inB (a1,a2) g in
            let f,p1 = p0 in
            (match f with
             | Vis ->
               (match p1 with
                | Chan (m, pl, t0) ->
                  (match m with
                   | Lin ->
                     (match pl with
                      | Out ->
                        if b0
                        then let p2,b3 = inB (b1,b2) g in
                             let f0,s = p2 in
                             (match f0 with
                              | Vis ->
                                if b3
                                then (match tremove s t0 with
                                      | Some r ->
                                        let d =
                                          (((a1,a2),Vis),(Chan
                                          (Lin, Empty,
                                          t0)))::((((b1,b2),Vis),r)::
                                          (removeEntry (a1,a2)
                                            (removeEntry (b1,b2) g)))
                                        in
                                        Some (d,q)
                                      | None -> raise)
                                else raise
                              | _ -> raise)
                        else raise
                      | _ -> raise)
                   | Un ->
                     if b0
                     then let p2,b3 = inB (b1,b2) g in
                          let f0,s = p2 in
                          (match f0 with
                           | Vis ->
                             if b3
                             then if (||) (pol_eq pl Out)
                                       (pol_eq pl Io)
                                  then (match tremove s t0 with
                                        | Some r ->
                                          let d =
                                            (((b1,b2),Vis),r)::
                                            (removeEntry (b1,b2) g)
                                          in
                                          Some (d,q)
                                        | None -> raise)
                                  else raise
                             else raise
                           | _ -> raise)
                     else raise)
                | Top -> raise)
             | _ -> raise)
       else raise
     | _ -> raise)

