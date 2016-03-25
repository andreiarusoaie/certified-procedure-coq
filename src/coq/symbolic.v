Require Import String.
Module Symbolic.

  (* symbolic domain *)
  Inductive _nat : Type := 
    | s_nat : nat -> _nat 
    | c_nat : nat -> _nat
    | _plus : _nat -> _nat -> _nat
    | _div : _nat -> _nat -> _nat
    | _mod : _nat -> _nat -> _nat .

  Notation "$ A" := (s_nat A) (at level 100).
  Notation "# A" := (c_nat A) (at level 99).
  Notation "A +nat B" := (_plus A B) (at level 99).
  Notation "A /nat B" := (_div A B) (at level 99).
  Notation "A %nat B" := (_mod A B) (at level 99).


  Inductive _bool : Type :=
  | s_bool : nat -> _bool 
  | c_bool : bool -> _bool
  | _not : _bool -> _bool 
  | _and : _bool -> _bool -> _bool
  | _or : _bool -> _bool -> _bool
  | _le : _nat -> _nat -> _bool
  | _leq : _nat -> _nat -> _bool .

  Notation "$$ B" := (s_bool B) (at level 100).
  Notation "## B" := (c_bool B) (at level 100).
  Notation "!bool B" := (_not B) (at level 99).
  Notation "A &&bool B" := (_and A B) (at level 99).
  Notation "A ||bool B" := (_or A B) (at level 99).
  Notation "A <nat B" := (_le A B) (at level 99).
  Notation "A <=nat B" := (_leq A B) (at level 99).

  Definition _mapitem := (string * _nat)%type.
  Definition _map := list _mapitem.


  (* model *)
  Inductive _stmt :Type := 
    | _assign : string -> _nat -> _stmt
    | _ifelse : _bool -> _stmt -> _stmt -> _stmt
    | _while : _bool -> _stmt -> _stmt
    | _seq : _stmt -> _stmt -> _stmt .

  Definition _cfg := (_stmt * _map)%type.

End Symbolic.
