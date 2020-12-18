Notation nat_succ := S.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinInt.
Open Scope Z_scope.

Inductive cmd : Set :=
  F : Z -> cmd | L : Z -> cmd | R : Z -> cmd
  | N : Z -> cmd | S : Z -> cmd | W : Z -> cmd | E : Z -> cmd.

Inductive dir : Set :=
  ND : dir | ED : dir | SD : dir | WD : dir.

Fixpoint step_dir (n : nat) (d : dir) : dir :=
  match n with
  | O => d
  | nat_succ n' => step_dir n' match d with ND => ED | ED => SD | SD => WD | WD => ND end
  end.

Definition rotate (angle : Z) (d : dir) : dir :=
  let step: nat := Z.abs_nat (Z.rem (Z.quot angle 90) 4)
  in step_dir step d.

Record state : Set := mkState
                        { cur_dir : dir
                          ; x_coord : Z
                          ; y_coord : Z }.

Definition update (st : state) (c : cmd) : state :=
  match st with
    | {| cur_dir := cd ; x_coord := x; y_coord := y |} =>
    let new_dir: dir := match c with
                        | L arg => rotate (360 - arg) cd
                        | R arg => rotate arg cd
                        | _ => cd
                      end in
    match match c with
          | L arg => (ND, 0)
          | R arg => (ND, 0)
          | F arg => (cd, arg)
          | N arg => (ND, arg)
          | E arg => (ED, arg)
          | W arg => (WD, arg)
          | S arg => (SD, arg)
          end with
      (move_dir, arg) =>
      match match move_dir with
            | ND => (x, y + arg)
            | SD => (x, y - arg)
            | WD => (x - arg, y)
            | ED => (x + arg, y)
            end with
        | (new_x, new_y) =>
          {| cur_dir := new_dir ; x_coord := new_x ; y_coord := new_y |}
      end
    end
  end.

Fixpoint part_a_loop (prog : list cmd) (st : state) : state :=
  match prog with
  | nil => st
  | (cons cmd cmds) => part_a_loop cmds (update st cmd)
  end.

Definition L1_dist (x : Z) (y : Z) : Z :=
  Z.abs x + Z.abs y.

Definition part_a (prog : list cmd) : Z :=
  let ret : state := part_a_loop prog {| cur_dir := ED ; x_coord := 0 ; y_coord := 0 |}
  in L1_dist (x_coord ret) (y_coord ret).

Fixpoint rotate_b (steps : nat) (point : Z * Z) : Z * Z :=
  match point with
  | (x, y) => match steps with
             | O => (x, y)
             | nat_succ O => (y, - x)
             | nat_succ (nat_succ O) => (- x, - y)
             | nat_succ (nat_succ (nat_succ O)) => ( - y, x)
             | nat_succ (nat_succ (nat_succ (nat_succ n'))) => rotate_b n' point
             end
  end.

Definition rotate_b_point (angle : Z) (point : Z * Z) : Z * Z :=
  rotate_b (Z.abs_nat (Z.quot angle 90)) point.

Record state_b : Set := mkStateB {
                            waypoint_coord : Z * Z ;
                            ship_coord : Z * Z
                          }.

Definition update_b (st : state_b) (c : cmd) : state_b :=
  match st with
  | {| waypoint_coord := wp ; ship_coord := s |} =>
    let new_wp : Z * Z :=
        match c with
        | L angle => rotate_b_point (360 - angle) wp
        | R angle => rotate_b_point angle wp
        | N arg => (fst wp, snd wp + arg)
        | S arg => (fst wp, snd wp - arg)
        | W arg => (((fst wp) - arg) , snd wp)
        | E arg => (fst wp + arg, snd wp)
        | F _ => wp
        end in
    let new_s : Z * Z :=
        match c with
        | F factor => (fst s + factor * fst wp, snd s + factor * snd wp)
        | _ => s
        end in
    {| waypoint_coord := new_wp ; ship_coord := new_s |}
  end.

Fixpoint part_b_loop (prog : list cmd) (st : state_b) : state_b :=
  match prog with
  | nil => st
  | (cons cmd cmds) => part_b_loop cmds (update_b st cmd)
  end.

Definition part_b (prog : list cmd) : Z :=
  let ret: state_b := part_b_loop prog {| waypoint_coord := (10, 1) ; ship_coord := (0, 0) |}
  in match ret with
     | {| waypoint_coord := _ ; ship_coord := s |} => L1_dist (fst s) (snd s)
     end.

Require Import Coq.Lists.List.
Import ListNotations.
Definition ex : list cmd := [ F 10 ;
N 3 ;
F 7 ;
R 90 ;
F 11
].

Compute part_a ex.
Compute part_b ex.
