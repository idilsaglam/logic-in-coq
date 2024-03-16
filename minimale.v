(* Raccourcis clavier de coqide *)
(* CTRL-flèche bas: avancer d'une commande *)
(* CTRL-flèche haut: revenir en arrière d'une commande *)
(* CTRL-flèche droit: avancer ou revenir en arrière jusqu'au curseur *) 

(** premiers pas en Coq *)

(* Logique minimale "pure": pas de négation/contradiction *)

Section Exemples.

  (* Définition de variables propositionnelles *)
  Variables P Q R S T : Prop.

  (* Une Section peut contenir d'autres [sous-]Sections. C'est le bon endroit
     pour definir des hypotheses (et donc prouver des sequents avec hypotheses).
   *)
  
  Lemma imp_dist: (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof.
    intro Hpqr.
    intro Hpq.
    intro Hp.
    apply Hpqr.
    - assumption.
    - apply Hpq.
      assumption.
  Qed.

  (* Explication des tactiques utilisées: *)
  (* intro: utilisation de la regle d'introduction pour changer de but *)
  (* apply: utilisation d'une implication qui a la bonne conclusion
     (il va falloir prouver ses hypotheses) *)
  (* Note: on ne peut faire "apply" que sur une propriété déjà prouvée,
     contrairement au modus ponens des preuves en arbres *)
  (* C'est automatiquement un modus ponens: "apply Hpqr" pour prouver R
     demande à prouver P et Q *)
  (* assumption: utilisation de la regle d'hypothese *)

  (* Autre tactique utile: intros 
     permet de faire plusieurs introductions d'un coup (intro multiple) *)

  Check imp_dist.  (* On voit la formule prouvée *)
  Print imp_dist.  (* Pour voir le "terme de preuve" calculé *)
  (* la syntaxe est très proche de celle de Ocaml *)

  (* exemple de preuve d'un sequent avec hypothèses *)
  (* On crée une section spécifique, sinon les hypothèses
     ajoutées pour ce lemme resteront pour les suivants *)
  Section S1.
    Hypothesis H : P -> Q.
    Hypothesis H0 : P -> Q -> R.

    Lemma L2 : P -> R.
    (* le sequent est: P->Q, P->Q->R |- P->R *)
    Proof.
      intro p.
      apply H0.
      - assumption.
      - apply H.
        assumption.
    Qed.

    Check L2. (* Les hypothèses font partie de la section *)
  End S1.

  (* Quand on ferme la section, ses hypotheses sont "exportees" sous la
     forme d'hypotheses supplementaires pour L2                         *)
  Check L2.
End Exemples.

Check L2.
(* La section Exemples avait des variables P Q R; une
   fois fermée, ces variables sont exportées sous forme
   universelle: cela permet d'appliquer L2 à d'autres
   propositions (théorème de substitution) *)
   
Section Exemple_bis.
  Variables A B C: Prop.

  Lemma L2': (A->B)->(A->B->C)->A-> C.
  Proof.
    apply L2. (* Ici Coq "voit" tout seul qu'il suffit
                 de prendre A pour P, B pour Q et 
                 C pour R, et L2 a alors le bon énoncé *)
  Qed.
End Exemple_bis.

Section Exercices.
  Variables P Q R S T: Prop.

  Section About_cuts.
    Hypothesis H : P -> Q.
    Hypothesis H0 : P -> Q -> R.
    Hypothesis H1 : Q -> R -> S.
    Hypothesis H2 : Q -> R -> S -> T.

    (* preuve sans lemme (coupure) *)
    Lemma L3 : P -> T.
    (* QUESTION: Quel est le séquent qu'on s'apprête à prouver? *)

    (* QUESTION: Faites-en une preuve papier AVANT de continuer *)
    Proof.
      intro p.
      apply H2.

      apply H.
      assumption.

      apply H0.
      assumption.

      apply H.
      assumption.

      apply H1.
      apply H. 
      assumption.

      apply H0.
      assumption.

      apply H. 
      assumption.
    Restart. (* Restart.: recommence une preuve de zéro *)
    (* QUESTION: Réécrivez le script ci-dessus en introduisant des tirets 
       (-, *, +) à chaque fois qu'une tactique engendre plus d'un 
       sous-but *)
    intro p. 
    apply H2. 
  
    - apply H.
      assumption.
    - apply H0. 
      + assumption.
      + apply H. assumption.
    - apply H1. 
      + apply H. assumption.
      + apply H0. 
        * assumption. 
        * apply H. assumption.
    
    Qed. (* À remplacer par "Qed." une fois la preuve faite. *)

    (* preuve avec coupures: on prouve Q et R une seule fois chacun,
       puis on les utilise *)

     Lemma L'3 : P -> T.
     Proof.
       intro p.
       assert (q: Q). { 
         apply H. assumption.
         }
       (* On a fini de prouver Q; on a maintenant une hypothèse (q:Q) *)   
       assert (r: R). {
         apply H0.
         - assumption.
         - assumption.
          }
       (* Pareil: on a maintenant prouvé R, et on a gagné une hypothèse *)
       assert (s : S). {
        apply H1. assumption. assumption.
       }
       apply H2; assumption. (* sans le ; il faut trois "assumption" *)
     Qed.

     (* assert: permet d'ouvrir une nouvelle sous-preuve, *)
     (* dans laquelle on se définit un nouveau but; c'est *)
     (* une coupure. Les accolades sont optionnelles mais *)
     (* facilitent la lecture humaine                     *)
     
     Check L'3.

(* remarquez la différence entre les termes de preuves avec coupure et sans coupure. *)
     Print L'3.
     Print L3.
(* Les coupures deviennent des "let.. in.." similaires à ceux de Ocaml *)

  End About_cuts.


 (* Les exercices commencent ici, à part la preuve admise de L2.  

    Reprendre les exemples vus en TD, en utilisant les tactiques 
    assumption, apply, assert et intro/intros.

    Remplacer chaque commande Admitted par un script correct de preuve,
    suivi de la commande Qed.

  *)

  Lemma IdP : P -> P.
  Proof.
    intro p.
    assumption.
  Qed. 

  Lemma IdPP : (P -> P) -> P -> P.
  Proof.
    intro p. 
    assumption.
  Qed.

  (* sans regarder le fichier de demo, c'est de la triche *)
  Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros pq qr p.
    apply qr.
    apply pq. 
    assumption. 
  Qed.

  Section proof_of_hyp_switch.
    Hypothesis H : P -> Q -> R.
    Lemma hyp_switch : Q -> P -> R.
    Proof.
    intros q p.
    apply H; assumption.

    Qed. 

  End proof_of_hyp_switch.

  Check hyp_switch.

  Section proof_of_add_hypothesis.
    Hypothesis H : P -> R.

    Lemma add_hypothesis : P -> Q -> R.
    Proof.
    intros p q. 
    apply H.
    assumption.
    Qed.

  End proof_of_add_hypothesis.


  Section proof_of_remove_dup_hypothesis.
  (* prouver le sequent (P -> P -> Q) |- P -> Q  
     (il faut l'énoncer, et faire la preuve) *)
  Hypothesis H: P -> P -> Q.
  Lemma l: P -> Q.

  Proof.
    intro p. 
    apply H;
    assumption. 
  Qed.

  End proof_of_remove_dup_hypothesis.


  Section proof_of_dup_hypothesis.
  (* même exercice avec le séquent P->Q |- P->P->Q *)

  Hypothesis H: P -> Q. 
  Lemma l1:  P->P->Q.

  Proof.
    intro p.
    intro p'. 
    apply H.
    assumption.
  Qed.

  End proof_of_dup_hypothesis.

 
  Section proof_of_distrib_impl.
 (* meme exercice avec 
     P -> Q , P -> R , Q -> R -> T |- P -> T  
   *) 
  Hypothesis H: P -> Q.
  Hypothesis H2: P -> R.
  Hypothesis H3: Q -> R -> T.
  Lemma l2: P -> T.
  
  Proof.
  intro p. 
  apply H3.
  - apply H.
  assumption.
- apply H2. 
  assumption.
  Qed.
  
  End proof_of_distrib_impl.


  Section proof_of_ex9.
  (* même exercice, avec 
     P->Q, Q->R, (P->R)->T->Q, (P->R)->T |- Q   
     (ex. 9 de la feuille "Logique minimale")
   *)

  Hypothesis H: P -> Q. 
  Hypothesis H1: Q -> R. 
  Hypothesis H2: (P->R)->T->Q.
  Hypothesis H3: (P->R)->T.
  Lemma l3: Q.

  Proof.
  apply H2.
  - intro p.
    apply H1.
    apply H. 
    assumption.
- apply H3.
  intro p'.
  apply H1.
  apply H.
  assumption.
  Qed. 
  End proof_of_ex9.
  
  (* exercice 10 de la feuille "Logique minimale" *)
  Section Proof_of_weak_Peirce.

    Hypothesis H: (((P->Q)->P)->P)->Q.
    Lemma weak_Peirce : Q.
    Proof.
    apply H. 
    intro pqp.
    apply pqp.
    intro p.
    apply H.
    intro pqp'.
assumption.
    Qed.

  End Proof_of_weak_Peirce.
  Check weak_Peirce.
  Print weak_Peirce. (* Pas facile à déchiffrer *)
  (* QUESTION: si vous n'aviez pas déjà fait cet exercice sur papier, 
     écrivez une preuve papier du même séquent; votre script de preuve
     devrait vous aider à identifier quelle règle utiliser à chaque étape.
  *)

End Exercices.

Section Exercices_bis. (* Les séquents proposés en tests semaine 3 *)  
  Variables P Q R S : Prop.

  Section Test_mercredi_1.
    Hypothesis H: (P->P)->Q->R.

    Lemma Mercredi1: Q->R.
    Proof.
      apply H.
      intro p.
      assumption.
    Qed.
  End Test_mercredi_1.

  Section Test_mercredi_2.
    Hypothesis H: P->Q.

    Lemma Mercredi2: (P->Q->R)->P->R.
    Proof.
      intro pqr.
      intro p.
      apply pqr.
      - assumption.
      - apply H. 
        assumption.
    Qed.
  End Test_mercredi_2.

  Section Jeudi_1.
    Hypothesis H:P.

    Lemma Jeudi1: (P->Q)->Q.
    Proof.
      intro pq.
      apply pq.
      assumption.
    Qed.
  End Jeudi_1.

  Section Jeudi_2.
    Hypothesis H: Q->R.

    Lemma Jeudi2: ((P->R)->S)->(P->Q)->S.
    Proof.
      intros prs pq.
      apply prs.
      intro p.
      apply H.
      apply pq.
      assumption.
    Qed.
  End Jeudi_2.

  Section Vendredi_1.
    Hypothesis H: (P->Q)->R.

    Lemma Vendredi1: P->(Q->R).
    Proof.
       intros p q.
       apply H.
       intro p'.
       assumption.
    Qed.
  End Vendredi_1.

  Section Vendredi_2.
    Hypothesis H: P->R.

    Lemma Vendredi2: (P->Q)->(P->R).
    Proof.
       intro pq.
       intro p.
       apply H.
       assumption.
    Qed.
  End Vendredi_2.
End Exercices_bis.
