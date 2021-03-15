From mathcomp Require Import ssreflect.

(*| We continue working with our own definitions of Booleans and natural numbers |*)

Module My.

Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 1 : boolean functions *)

(*| 1a. Define `orb` function implementing boolean disjunction
and test it _thoroughly_ using the command `Compute`. |*)

Definition orb (b c : bool) : bool :=
  match b, c with
  | false, false => false
  | _, _ => true
  end.

Compute orb true false.
Compute orb false true.
Compute orb false false.

(*| 1b. Define `addb` function implementing _exclusive_ boolean disjunction.
Try to come up with more than one definition (try to make it interesting
and don't just swap the variables) and explore its reduction behavior
in the presence of symbolic variables. |*)

Definition addb (b c : bool) : bool :=
  match b, c with
  | true, true => false
  | false, false => false
  | _, _ => true
  end.

Definition addb' (b c : bool) : bool :=
  negb (orb (negb (orb b c)) (negb (orb (negb b) (negb c)))).

Variable x : bool.

Compute addb true true.
Compute addb true false.
Compute addb false true.
Compute addb false false.
Compute addb x false.
Compute addb true x.

Compute addb' true true.
Compute addb' true false.
Compute addb' false true.
Compute addb' false false.

Compute addb' false x.
Compute addb' x true.

Eval cbv beta delta in addb' x true.
Eval cbv beta delta iota in addb' x true.

(*| 1c. Define `eqb` function implementing equality on booleans, i.e. `eqb b c`
must return `true` if and only iff `b` is equal to `c`. Add unit tests. |*)

Definition eqb (b c : bool) : bool :=
  match b, c with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

Compute eqb true true.
Compute eqb false false.
Compute eqb false true.
Compute eqb true false.


(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.


(*| 2a. Define `dec2` function of type `nat -> nat` which takes a natural
number and decrements it by 2, e.g. for the number `5` it must return `3`. Write
some unit tests for `dec2`. What should it return for `1` and `0`? |*)

Definition dec2 (n : nat) : nat :=
  if n is S (S n) then n else O.

Compute dec2 (S (S O)).
Compute dec2 (S O).
Compute dec2 O.

(*| 2b. Define `subn` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of subtracting `n` from `m`.
E.g. `subn 5 3` returns `2`. Write some unit tests. |*)

Fixpoint subn (m n : nat) : nat :=
  if m is S m' then
    if n is S n'
    then subn m' n'
    else m
  else m.

Compute subn (S (S O)) O.
Compute subn (S (S (S O))) (S O).
Compute subn (S (S (S O))) (S (S O)).
Compute subn (S (S (S O))) (S (S (S O))).
Compute subn (S O) (S (S (S O))).

(*| 2c. Define an `muln` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of their multiplication.
Write some unit tests. |*)

Fixpoint addn (m n: nat) : nat :=
  match m, n with
  | m', O => m'
  | m', S n' => S (addn m' n')
  end.

Compute addn (S (S (S O))) (S (S O)).

Fixpoint muln (m n : nat) : nat :=
  match m, n with
  | O, _ => O
  | _, O => O
  | S m', S n' => addn m (muln m n')
  end.

Compute muln (S (S (S O))) (S (S O)).
Compute muln (S (S (S O))) (S (S (S O))).
Compute muln (S O) O.
Compute muln O O.

(** 2d. Implement equality comparison function `eqn` on natural numbers of
type `nat -> nat -> bool`. It returns true if and only if the input numbers are
equal. *)

Fixpoint eqn (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | S _, O => false
  | O, S _ => false
  | S m', S n' => eqn m' n'
  end.

Compute eqn (S O) O.
Compute eqn (S (S O)) (S (S (S O))).
Compute eqn O O.
Compute eqn (S (S (S O))) (S (S (S O))).

(** 2e. Implement less-or-equal comparison function `leq` on natural numbers of
type `nat -> nat -> bool`. `leq m n` returns `true` if and only if `m` is less
than or equal to `n`. Your solution must not use recursion but you may reuse any
of the functions you defined in this module so far. *)

Definition leq (m n : nat) : bool :=
  if subn m n is O then true else false.

Compute leq (S O) O.
Compute leq (S (S O)) (S O).
Compute leq (S (S O)) (S (S (S O))).
Compute leq O O.
Compute leq (S O) (S O).

(*| ---------------------------------------------------------------------------- |*)


(*| EXTRA problems: feel free to skip these. If you need to get credit for this
class: extra exercises do not influence your grade negatively if you skip them.
|*)

(*| Ea: implement division (`divn`) on natural numbers and write some unit tests
for it. |*)

Fixpoint divn (m n : nat) : nat :=
  if n is S n' then
    if subn m n' is S m'
    then S (divn m' n)
    else O
  else O.

Compute divn (S (S (S (S O)))) (S (S O)).
Compute divn (S (S (S O))) (S (S (S O))).
Compute divn (S (S (S (S (S (S (S (S O)))))))) (S (S O)).
Compute divn (S (S (S (S (S O))))) (S (S O)).
Compute divn (S O) O.
Compute divn O O.

End My.
