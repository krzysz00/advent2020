Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinInt.
Require Import Coq.MSets.MSets.
Require Import Coq.MSets.MSetAVL.

Open Scope Z_scope.

Module S := Make (Z_as_OT).

Inductive instr : Set := acc : Z -> instr
                       | jmp : Z -> instr
                       | nop : Z -> instr.

Definition to_optional_nat (z : Z) : option nat :=
  match z with
  | Zneg _ => None
  | Z0 => Some O
  | Zpos p => Some (Pos.to_nat p)
  end.

(* Since for some reason this isn't in the stdlib *)
Definition bind {A B : Type} (v : option A) (f : A -> option B) : option B :=
  match v with
  | Some val => f val
  | None => None
  end.

Inductive status := no_fuel : status
                  | bounds : Z -> status
                  | loop : Z -> status.

Fixpoint interpret (prog : list instr) (ip: Z) (acc : Z) (ip_track : S.t)
         (fuel : nat) : status :=
  match fuel with
    | O => no_fuel
    | S new_fuel =>
      if S.mem ip ip_track then loop acc
      else
        match bind (to_optional_nat ip) (nth_error prog) with
        | Some (acc arg) => interpret prog (Z.succ ip) (acc + arg) (S.add ip ip_track) new_fuel
        | Some (nop arg) => interpret prog (Z.succ ip) acc (S.add ip ip_track) new_fuel
        | Some (jmp arg) => interpret prog (ip + arg) acc (S.add ip ip_track) new_fuel
        | None => bounds acc
        end
  end.

Definition part_a (prog : list instr) : status :=
  interpret prog 0 0 S.empty 1000.

Definition switch_instr (i : instr) : instr :=
  match i with
  | acc a => acc a
  | jmp a => nop a
  | nop a => jmp a
  end.

Import ListNotations.
Fixpoint part_b_int (rev_prefix : list instr) (suffix : list instr) : status :=
  match suffix with
  | [] => no_fuel
  | (acc a) :: instrs => part_b_int ((acc a) :: rev_prefix) instrs
  | i :: instrs =>
    match part_a ((rev rev_prefix) ++ (switch_instr i :: instrs)) with
    | bounds ret => bounds ret
    | no_fuel => no_fuel
    | _ => part_b_int (i :: rev_prefix) (instrs)
    end
  end.

Definition part_b (prog : list instr) : status := part_b_int [] prog.

Definition example : list instr :=
  [nop 0 ;
  acc 1 ;
  jmp 4 ;
  acc 3 ;
  jmp (-3) ;
  acc (-99) ;
  acc (1) ;
  jmp (-4) ;
  acc 6 ].

Compute part_a example.
Compute part_b example.

Definition input08 : list instr :=
  [ (* Preprocess with perl -pe 's/\+(\d+)$/\1 ;/; s/(-\d+)$/(\1) ;/;'
     and copy-paste in, removing last semicolon *)
(* BEGIN INPUT *)

(* END INPUT *)
  ].

Compute part_a input08.
Compute part_b input08.
