From mathcomp Require Import ssreflect.

(* implement functions with the given signatures *)

Definition prodA (A B C : Type) :
  (A * B) * C -> A * (B * C)
:=
  fun '(a, b, c) => (a, (b, c)).

Compute prodA bool nat nat ((true, 1), 2).

Locate "+".
Print sum.

Definition sumA' (A B C : Type) :
  (A + B) + C -> A + (B + C)
:=
  fun abc =>
    match abc with
    | inl ab =>
      match ab with
      | inl a => inl a
      | inr b => inr (inl b)
      end
    | inr c => inr (inr c)
    end.

Definition sumA (A B C : Type) :
  (A + B) + C -> A + (B + C)
:=
  fun abc =>
    match abc with
    | inl (inl a) => inl a
    | inl (inr b) => inr (inl b)
    | inr c => inr (inr c)
    end.

Compute sumA nat bool nat (inl (inr true)).

Definition prod_sumD (A B C : Type) :
  A * (B + C) -> (A * B) + (A * C)
:=
  fun '(a, bc) =>
    match bc with
    | inl b => inl (a, b)
    | inr c => inr (a, c)
    end.

Definition sum_prodD (A B C : Type) :
  A + (B * C) -> (A + B) * (A + C)
:=
  fun abc =>
    match abc with
    | inl a => (inl a, inl a)
    | inr (b, c) => (inr b, inr c)
    end.

(* function composition *)
Definition comp A B C (f : B -> A) (g : C -> B) : C -> A
:=
  fun c => f (g c).

(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)

Arguments comp [A B C] _ _ _.

Notation "f \o g" := (comp f g) (at level 70).

Compute ((fun x => x + 1) \o (fun x => x * 2)) 3.

(* Introduce empty type, call `void` *)

Inductive void : Type :=.

Definition void_terminal (A : Type) :
  void -> A
:=
  fun x => match x with end.

(* Introduce `unit` type (a type with exactly one canonical form) *)

Inductive unit : Type := tt.

Definition unit_initial (A : Type) :
  A -> unit
:=
  fun _ => tt.

(* Think of some more type signatures involving void, unit, sum, prod *)

(*
   (void + unit) * unit -> unit
   void -> void + void
   void * unit + void -> void * unit
*)
