(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import cl.

Set Implicit Arguments.

Section cl_equivalence.

  (* Now the definition of equivalence between the terms
     of combinatory algebras. It is the least equivalence
     relation (reflexive, symmetry and transitive) which
     is congruent with composition o and such that
       I o x ~~ x, K o x o y ~~ x and 
       S o x o y o z ~~ x o z o (y o z)
  *)

  Reserved Notation "x '~cl' y" (at level 70).

  Inductive cl_eq : clterm -> clterm -> Prop :=
  
    | in_cl_eq_I : forall x,               I o x ~cl x 
    
    | in_cl_eq_K : forall x y,         K o x o y ~cl x
    
    | in_cl_eq_S : forall x y z,   S o x o y o z ~cl x o z o (y o z)

    | in_cl_eq_0 : forall x,                   x ~cl x
    
    | in_cl_eq_1 : forall x y,                 x ~cl y 
                              ->               y ~cl x
                             
    | in_cl_eq_2 : forall x y z,               x ~cl y 
                              ->               y ~cl z 
                              ->               x ~cl z
                              
    | in_cl_eq_3 : forall x y z,           x     ~cl y 
                              ->           x o z ~cl y o z
                              
    | in_cl_eq_4 : forall x y z,               y ~cl     z 
                              ->           x o y ~cl x o z
                                
  where "x ~cl y" := (cl_eq x y).
  
  (* Some exercices with cl_term equivalence *)
  
  Fact cl_eq_refl f g : f = g -> f ~cl g.
  Proof.
    intro H.
    destruct H.
    constructor 4.
  Qed.
  
  Definition cl_eq_sym := in_cl_eq_1.

  Definition cl_eq_trans := in_cl_eq_2.
  
  Fact cl_eq_app x y a b : x ~cl y -> a ~cl b -> x o a ~cl y o b.
  Proof.
    induction 2.
    apply (cl_eq_refl)in H.
    apply cl_eq_trans with (1 := in_cl_eq_I _).

    apply in_cl_eq_I with (1 := in_cl_eq_3 _ _ _).


    induction 1.
    intro H.
    apply (in_cl_eq_4 (x)) in H.
    apply cl_eq_trans with (x o a).
admit. exact H.

    intro H.
    apply (in_cl_eq_4 (x)) in H.
    apply in_cl_eq_1.
    apply cl_eq_trans with (x o b).
    apply in_cl_eq_0.
    apply cl_eq_trans with (x o b).
    destruct H.
    apply 
    (*apply in_cl_eq_I with (1 := x o a).*)
admit.
    intro H.
    intros H0 H1.
    destruct H0.
    destruct H1.

    apply 

admit.
admit.
admit.
    apply in_cl_eq_3; auto.
    destruct H1.
    apply in_cl_eq_I.



    apply in_cl_eq_2 with a in H1 .
    apply cl_eq_refl.
    cut (x o a).
    destruct H1.
    destruct H0.
    apply cl_eq_sym.

    apply cl_eq_sym.
    apply in_cl_eq_4 with x0.
    intros.

    simpl.
    rewrite H0 with cl_eq_sym.
    destruct H0.

    apply in_cl_eq_4.

    intro H.
    destruct H.
    apply in_cl_eq_2.
    intros H0 H1.
    constructor 7. 

    destruct H0.
    destruct H1.



  Admitted.
  
  Fact cl_I_prop x : I o x ~cl x.
  Proof.
    apply in_cl_eq_I.
  Qed.
  
  Fact cl_K_prop x y : K o x o y ~cl x.
  Proof.
    apply in_cl_eq_K.
  Qed.
  
  Fact cl_S_prop x y z : S o x o y o z ~cl x o z o (y o z).
  Proof.
    apply in_cl_eq_S.
  Qed. 
  
  Fact cl_SKI_prop x : S o K o I o x ~cl x.
  Proof.
    apply cl_eq_trans with (1 := cl_S_prop _ _ _).
    apply cl_K_prop.
  Qed.
  
  Corollary cl_SKI_I : forall x, S o K o I o x ~cl I o x.
  Proof.
    intros.
    apply cl_eq_trans with (1 := cl_S_prop _ _ _).
    apply cl_eq_trans with (1 := cl_K_prop _ _).
    apply cl_eq_sym.
    constructor 1.
  Qed.

  Definition cl_D := S o I o I.
  
  Notation D := cl_D.
  
  Fact cl_D_prop x : D o x ~cl x o x.
  Proof.
    unfold cl_D.

  Admitted.
  
  Definition cl_B := S o (K o S) o K.
  
  Notation B := cl_B.
  
  Hint Resolve in_cl_eq_0.
  
  Fact cl_B_prop f g x : B o f o g o x ~cl f o (g o x).
  Proof.
    unfold cl_B.
    apply cl_eq_trans with (K  o S o f o (K o f) o g o x).
    do 2 (apply cl_eq_app; auto); apply cl_S_prop.
    apply cl_eq_trans with (S o (K o f) o g o x).
    do 3 (apply cl_eq_app; auto); apply cl_K_prop.
    apply cl_eq_trans with (1 := cl_S_prop _ _ _).
    apply cl_eq_app; auto.
    apply cl_K_prop.
  Qed.
  
  Definition cl_L := D o (B o D o D).
  
  Notation L := cl_L.
  
  Fact cl_L_prop : L ~cl L o L.
  Proof.
    unfold cl_L.
    apply cl_eq_trans with (K o S o D).
    
  Admitted.
  
End cl_equivalence.

Notation "x '~cl' y" := (cl_eq x y) (at level 70).