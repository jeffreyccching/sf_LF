Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day 
  | saturday : day
  | sunday : day.

(** The new type is called day, and its members are monday, tuesday, etc.
Having defined day, we can write functions that operate on days.**)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(*Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).*)
(* ==> tuesday : day *)

(*Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
*)

(*Proof. simpl. reflexivity.  Qed.*)

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool)  : bool  :=
  match b with
  | true  =>  false
  | false =>  true
end.


Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.




Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.


Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => negb b2
    | false =>  true
  end.

Example test_nandb1:               (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | true  => andb b2 b3
    | false => false
  end.


Example test_andb31:                 (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true
  : bool.
(*If the expression after Check is followed by a colon and a type, Coq will verify that the type of
 the expression matches the given type and halt with an error if not.*)

(*The types we have defined so far are examples of "enumerated types": their definitions explicitly 
enumerate a finite set of elements, called constructors. Here is a more interesting type definition, 
where one of the constructors takes an argument:*)
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).





(*We can define functions on colors using pattern matching just as we did for day and bool.
*)
Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p  =>false
  end.


(*Modules
Coq provides a module system to aid in organizing large developments. 
We won't need most of its features, but one is useful: If we enclose a collection of declarations between 
Module X and End X markers, then, in the remainder of the file after the End, these definitions are referred to 
by names like X.foo instead of just foo. We will use this feature to limit the scope of definitions, so that we are 
free to reuse names.*)
Module Playground.
  Definition b : rgb := blue.
End Playground.
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.



Module TuplePlayground.
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
  : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.
Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)

End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Inductive nat' : Type :=
  | stop
  | tick (foo : nat').

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.
Check (S (S (S (S O)))).
