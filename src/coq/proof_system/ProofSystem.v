Require Import List.
Require Import Formula.
Require Import Model.

Fixpoint delta_S (phi : Formula) (S : System) : Formula := phi .
Fixpoint delta_G (phi : Formula) (C : Rule) : Formula := phi .
Fixpoint covers (r : Rule) (phi : Formula) := True .
Fixpoint derivable (phi : Formula) (S : System) := True .

Inductive PS : System -> System -> Formula -> Formula -> Prop :=
| ps_ss : forall (S : System) (G : System)
                 (phi : Formula) (phi' : Formula),
            derivable phi S -> PS S G phi (delta_S phi S)
| ps_circ : forall (S : System) (G : System)
                   (phi : Formula) (phi' : Formula) (phi'' : Formula),
              G (phi' => phi'') -> covers (phi' => phi'') phi ->
              PS S G phi (delta_G phi (phi' => phi''))
| ps_impl : forall (S : System) (G : System)
                   (phi : Formula) (phi' : Formula),
            Valid (impliesF phi phi') -> PS S G phi phi'
| ps_ca : forall (S : System) (G : System)
                 (phi : Formula) (phi' : Formula) (phi'' : Formula),
               PS S G phi' phi -> PS S G phi'' phi -> PS S G (orF phi' phi'') phi
| ps_trans : forall (S : System) (G : System)
                 (phi : Formula) (phi' : Formula) (phi'' : Formula),
               PS S G phi phi'' -> PS S G phi'' phi' -> PS S G phi phi' .
