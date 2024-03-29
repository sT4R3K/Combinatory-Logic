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
    rewrite H.
    constructor 4.
  Qed.
  
  Definition cl_eq_sym := in_cl_eq_1.

  Definition cl_eq_trans := in_cl_eq_2.
  
  Fact cl_eq_app x y a b : x ~cl y -> a ~cl b -> x o a ~cl y o b.
  Proof.
    intros H0 H1; induction H0.
    
    apply cl_eq_trans with (x o a);
      try (apply in_cl_eq_3; constructor 1);
      try (apply in_cl_eq_4; auto).
    
    apply cl_eq_trans with (x o a);
      try (apply in_cl_eq_3; constructor 2);
      try (apply in_cl_eq_4; auto).
    
    apply cl_eq_trans with (x o z o (y o z) o a);
      try (apply in_cl_eq_3; constructor 3);
      try (apply in_cl_eq_4; auto).
    
    apply in_cl_eq_4; auto.
    
    apply cl_eq_trans with (x o a);
      try (apply in_cl_eq_3; apply cl_eq_sym; auto);
      try (apply in_cl_eq_4; auto).
    
    apply cl_eq_trans with (x o b);
      try (apply in_cl_eq_4; auto);
      try (apply in_cl_eq_3; apply cl_eq_trans with y; auto).
    
    apply cl_eq_trans with (y o z o a);
      try (do 2 apply in_cl_eq_3; auto);
      try (apply in_cl_eq_4; auto).
    
    apply cl_eq_trans with (x o z o a);
      try (apply in_cl_eq_3; auto; apply in_cl_eq_4; auto);
      try (apply in_cl_eq_4; auto).
  Qed.
  
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
    apply cl_eq_trans with (I o x o (I o x)).
    apply cl_S_prop.
    apply cl_eq_trans with (x o (I o x));
      try apply in_cl_eq_3;
      try apply in_cl_eq_4;
    constructor 1.
  Qed.
  
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
    apply cl_eq_trans with ((B o D o D) o (B o D o D));
      try apply cl_D_prop.
    do 2 (
      apply cl_eq_trans with (D o (D o (B o D o D)));
        try apply cl_D_prop;
        try (apply cl_B_prop; constructor 4)
    ).
  Qed.
  
End cl_equivalence.

Notation "x '~cl' y" := (cl_eq x y) (at level 70).