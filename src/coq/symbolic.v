Module Symbolic .

  Inductive snat : Type := 
    | sym_nat : nat -> snat 
    | c_nat : nat -> snat
    | sym_plus : snat -> snat -> snat
    | sym_div : snat -> snat -> snat
    | sym_mod : snat -> snat -> snat .

  Notation "$ A" := (sym_nat A) (at level 100).
  Notation "# A" := (c_nat A) (at level 99).
  Notation "A +nat B" := (sym_plus A B) (at level 99).
  Notation "A /nat B" := (sym_div A B) (at level 99).
  Notation "A %nat B" := (sym_mod A B) (at level 99).


  Inductive sbool : Type :=
  | sym_bool : nat -> sbool 
  | c_bool : bool -> sbool
  | sym_not : sbool -> sbool 
  | sym_and : sbool -> sbool -> sbool
  | sym_or : sbool -> sbool -> sbool
  | sym_le : snat -> snat -> sbool
  | sym_leq : snat -> snat -> sbool .

  Notation "$$ B" := (sym_bool B) (at level 100).
  Notation "## B" := (c_bool B) (at level 100).
  Notation "!bool B" := (sym_not B) (at level 99).
  Notation "A &&bool B" := (sym_and A B) (at level 99).
  Notation "A ||bool B" := (sym_or A B) (at level 99).
  Notation "A <nat B" := (sym_le A B) (at level 99).
  Notation "A <=nat B" := (sym_leq A B) (at level 99).

End Symbolic.
