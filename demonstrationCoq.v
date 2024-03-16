(* Ceci est un commentaire *)


  Variables P Q R: Prop.
Section Demo.

  Theorem imp_trans: (P->Q)->(Q->R)->(P->R).
  Proof.
    intro Hpq. (* "règle d'introduction" *)
    intro Hqr.
    intro p. 
    apply Hqr. (* modus ponens *)
    apply Hpq.
    assumption.
  Restart. (* On va refaire la preuve à partir de zéro *)
    intros Hpq Hqr Hp. (* "règle d'introduction généralisée" *)
    (* "intros" fait plusieurs introductions, autant que possible si
       on ne lui donne pas de noms (déconseillé) *)
    apply Hqr;
    apply Hpq;
    assumption.
  Qed.


  Check imp_trans. (* Affiche l'énoncé du théorème *)

  Print imp_trans. (* Affiche le terme de preuve du théorème *)

End Demo.


Section Demo'.

  Variables P Q R S: Prop.

  (* Pour énoncer un séquent avec des hypothèses *)

  Section Avec_hypotheses.

    Hypothesis H: P->Q->R.
    Hypothesis H1: P->Q.
    Hypothesis H2: P.

    Theorem exemple: R.
    (* Correspond au séquent: P->Q->R, P->Q, P |- R *)
    Proof.
      apply H. (* modus ponens généralisé *)
      - assumption. (* Le tiret ne sert qu'à structurer pour les humains *)
      - apply H1.
        assumption.
    Qed.

    Check exemple.

  End Avec_hypotheses.

  Check exemple.
  (* Quand on ferme la section, les théorèmes démontrés sont "exportés"
     avec comme prémisses supplémentaires, les hypothèses de la section *)

End Demo'.

Check exemple.
(* Idem pour les "variables" utilisées, qui sont généralisées sous forme que "pour tout" *)

Section EncoreDesDemos.
  Variables P Q R S T: Prop.

  Theorem douteux: P -> Q. (* Coq accepte tout énoncé bien formé, même invalide *)
  Proof.
    intro Hp.
  Admitted. (* Permet d'abandonner la preuve *)

  Check douteux. (* "P->Q" *) (* L'énoncé du théorème est néanmoins utilisable. *)
  Print douteux.

  (* exemple d'enchainement de tactiques *)
  Theorem impl_comm: (P->Q->R)->(Q->P->R).
  Proof.
    intros Hpqr Hq Hp.
    apply Hpqr.
    - assumption.
    - assumption.
  Restart.
    intros Hpqr Hp Hq.
    apply Hpqr; assumption.
    (* le point-virgule enchaine les tactiques (ne pas en abuser) *)
    (* Ici le "apply Hpqr" génère deux sous-buts (P, et Q), mais grâce au
       point-virgule, chaque sous-but est passé à la tactique
       "assumption" qui les résoud ; du coup un seul "assumption" suffit *)
  Qed.

  Theorem ex_assert: (R->S->T)->(P->P->Q)->(Q->R)->(Q->S)->P->T.
  Proof.
    intros Hrst Hpq Hqr Hqs p.
    apply Hrst.
    - apply Hqr.
      apply Hpq.
      + assumption. (* Indentation des puces fortement recommandées *)
      + assumption.
    - apply Hqs.
      apply Hpq; assumption.
  (* On a prouvé deux fois Q; avec un assert on ne le ferait qu'une fois. *)
  Restart.
    intros H H0 H1 H2 H3.
    assert (Hq:Q).
      apply H0; assumption.
    assert R. (* Pour l'exemple *)
      apply H1.
      assumption.
    assert S. (* Accolades fortement recommandées si plus d'une commande *)
    { (* Focalise sur le premier but *)
      apply H2.
      assumption.
    }
    (* Maintenant on a tout pour appliquer H pour prouver T *)
    apply H; assumption.
  Qed.

  Theorem negation: P -> ~P -> Q.
  Proof.
    intros Hp Hnp.
    exfalso. (* Principe d'explosion *)
    unfold not in Hnp. (* Développe la notation ~ *)
    apply Hnp. (* modus ponens "habituel" *)
    Undo 2.
    apply Hnp. (* modus ponens fonctionne quand même ; ~ n'est qu'une notation *)
    assumption.
  Qed.

End EncoreDesDemos.

Section CurryHoward.

  Variables P Q R: Prop.

  (* Vision "Preuve" *)

  Hypothesis Hpq: P->Q.
  Hypothesis Hqr: Q->R.

  Theorem TheoremPimplR: P->R.
  Proof.
    intro Hp.
    apply Hqr.
    apply Hpq.
    assumption.
  Qed.

  Print TheoremPimplR.
  (*
  TheoremPimplR = fun Hp : P => Hqr (Hpq Hp)
     : P -> R
  *)

  (* Vision "Programmation" *)

  Notation f := Hpq. (* "P->Q" *)
  Notation g := Hqr. (* "Q->R" *)

  Definition g_rond_f := fun p => g (f p).

  Check g_rond_f. (* "P->R" *)

  Print g_rond_f.
  (*
  g_rond_f = fun p : P => g (f p)
      : P -> R
  *)
  Print TheoremPimplR.

  Theorem negation': P -> ~P -> Q.
  Proof.
    intros p Hnp.
    destruct (Hnp p).
    (* Hnp a type P->False, donc (Hnp p) a type False;
      et destruct sur un terme de type False prouve
      n'importe quel but *)
  Qed.

End CurryHoward.

