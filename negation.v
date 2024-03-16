Section Negation.
  Variables P Q R S T: Prop.

  (* unfold not: expansion de la négation dans le but *)
  (* unfold not in X: expansion de la négation dans l'hypothèse X *)
  (* exfalso: transforme le but courant en False; c'est l'équivalent
     de la règle d'élimination de la contradiction *)

  (* Executez cette preuve en essayant de comprendre le sens de chacune des nouvelles tactiques utilisées. *)
  Lemma absurde_exemple: P -> ~P -> S.
  Proof.
    intros p np.
    unfold not in np.
    (* destruct (np p). *) 
    exfalso.
    apply np.
    assumption.
  Qed.
  
  Lemma triple_neg_e : ~~~P -> ~P.
  Proof.
     intro H. 
     intro H0.
     apply H.
     intro H1.
     apply H1; assumption.
   Restart.  (* Annule la preuve en cours, et en commence un autre *)
   unfold not.
   auto.
   (* auto est une tactique qui est capable de beaucoup, mais qu'on
      s'interdira d'utiliser dans nos preuves *)
   Qed.

  (* Début des exercices *)

  (* QUESTION: Remplacer les Admitted par des scripts de preuve *)
  Lemma absurde: (P -> Q) -> (P -> ~Q) -> (P -> S).
  Proof.
  intros pq pnq p.
  exfalso.
  unfold not in pnq.
  apply pnq.
  - assumption. 
  - apply pq.
    assumption.
  Qed.

  Lemma triple_abs: ~P -> ~~~P.
  Proof.
  intros np dp.
  unfold not in np.
  unfold not in dp.
  apply dp.
  assumption.
  Qed.
  
  Lemma absurd' : (~P -> P) -> ~~P.
  Proof.
    intros npp np.
    unfold not in np.
    unfold not in npp.
    apply np.
    apply npp.
    assumption.
  
  Qed.

  Definition Peirce  := ((P -> Q) -> P) -> P.

  (* On va prouver non-non-Peirce *) (*TODO*)
  Lemma Peirce_2 : ~~ Peirce.
  Proof.
    (* Strategie: sous hypothese ~Peirce [par intro], montrer ~P, puis s'en 
       servir pour montrer Peirce, et on aura une contradiction
       entre Peirce et ~Peirce *)
    intro.
    unfold Peirce in H .
    unfold not in H.
    assert (np: ~P). {
      intro p'.
      apply H.
      intro pq.
      assumption.
    }
    apply H.
    intro pq'.
    apply pq'.
    intro p.
    exfalso.
    apply np.
    assumption.
  Qed. (* À vous de finir *)

  (* Une série de séquents à prouver; à chaque fois, il faut
  l'énoncer, en introduisant les hypothèses au moyen d'une
  sous-section. *)

 
 (* P->Q, R->~Q, P->R |- P->S *)
  Section Q1.

  Hypothesis H: P->Q.
  Hypothesis H1: R->~Q.
  Hypothesis H2: P->R.
 
  Lemma l1 : P->S.

  Proof. 
    intro p.
    unfold not in H1.
    exfalso.
    apply H1.
    - apply H2.
      assumption.
    - apply H.
      assumption.
Qed.

  End Q1. 



  (* ~P->~Q |- ~~Q->~~P *)

Section Q2. 
  Hypothesis H: ~P->~Q.
  Lemma l2 : ~~Q->~~P.
  Proof.
    intros nnq np.
    unfold not in nnq. 
    unfold not in np.
    unfold not in H.
    apply nnq.
    apply H.
    assumption.
  Qed.
End Q2.

  (* P->~P |- ~P *) 
Section Q3. 
  Hypothesis H:P->~P. 
  Lemma l3: ~P. 
  Proof.
    intro p.
    apply H;
    assumption.
          
  Qed.
 
End Q3.

  (* ~~P |- ~P->~Q *)

Section Q4. 
  Hypothesis H: ~~P. 
  Lemma l4: ~P->~Q. 
  Proof.
    intros np q. 
    apply H.
    assumption.
  Qed.

End Q4.

  (* P->~Q, R->Q |- P->~R *)
Section Q5.
  Hypothesis H1:P->~Q. 
  Hypothesis H2: R->Q. 
  Lemma l5:P->~R.
  Proof. 
      intros p r.
      unfold not in H1.
      apply H1.
      - assumption. 
      - apply H2. 
        assumption.
  Qed.
End Q5.

  (* ~(P->Q) |- ~Q *) 
  Section Q6.  

    Hypothesis H: ~(P->Q).
    Lemma l6: ~Q.
    Proof. 
        intro q. 
        apply H.
        intro p.
        assumption.
    Qed.
End Q6.

  (* Séquents proposés en test par le passé *)

  Section Test01.
    
    Hypothesis H: P->Q.

    Lemma Ex01: ~(~Q->~P) -> R.
     Proof. 
      intro nnqnp. 
      unfold not in nnqnp.
      exfalso.
      apply nnqnp.
      intros nq p.
      apply nq.
      apply H.
      assumption.
     Qed.
   
  End Test01.

  Section Test02.
    Hypothesis H: ~(P->R).

    Lemma Ex02: Q->(P->Q->R)->P.
    Proof.
      intros q pqr.
      exfalso.
      apply H.
      intro p.
      apply pqr;
      assumption.
    Qed.
  End Test02.

  Section Test03.
    Hypothesis H: ~(Q->R).

    Lemma Ex03: (P->Q->R)->(P->Q).
    Proof. 
      intros pqr p. 
      exfalso.
      apply H.
      apply pqr.
      assumption.
    Qed.
  End Test03.

  Section Test04.
    Hypothesis H: ~~P.

    Lemma Ex04: Q->(P->Q->False)->P.
    Proof.
      intros q pnq.
      unfold not in H.
      exfalso.
      apply H.
      intro p.
      apply pnq;
      assumption.
    Qed.
  End Test04.
    
End Negation.


