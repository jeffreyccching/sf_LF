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


Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Compute (minustwo 4).
(* ===> 2 : nat *)

(*The constructor S has the type nat \u2192 nat, just like functions such as pred and minustwo:*)
Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

(*For most interesting computations involving numbers, simple pattern matching is not enough:
 we also need recursion. For example, to check that a number n is even, we may need to recursively 
check whether n-2 is even. Such functions are introduced with the keyword Fixpoint instead of Definition.*)
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

(*We could define odd by a similar Fixpoint declaration, but here is a simpler way:*)
Definition odd (n:nat) : bool :=
  negb (even n).
Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
(*Adding three to two now gives us five, as we'd expect.*)
Compute (plus 3 2).
(* ===> 5 : nat *)

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' =>  plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.


(*You can match two expressions at once by putting a comma between them:*)
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
End NatPlayground2.
Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

(*Exercise: 1 star, standard (factorial)
Recall the standard mathematical factorial function:
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)
Translate this into Coq.*)
Fixpoint factorial (n:nat) : nat  :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity.  Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity.  Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
(*Similarly, the leb function tests whether its first argument is less than or equal to its 
second argument, yielding a boolean.*)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.
(*We'll be using these (especially eqb) a lot, so let's give them infix notations.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.*)
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.
(*We now have two symbols that look like equality: = and =?. We'll have much more to say about 
the differences and similarities between them later. For now, the main thing to notice is that 
x = y is a logical claim -- a "proposition" -- that we can try to prove, while x =? y is an expression
 whose value (either true or false) we can compute.*)
Definition ltb (n m : nat) : bool :=
  andb  (leb n m) (negb (eqb n m)).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.



