(** * Logic: Logic in Coq *)

Require Export MoreProp. 

(** Coq's built-in logic is very small: the only primitives are
    [Inductive] definitions, universal quantification ([forall]), and
    implication ([->]), while all the other familiar logical
    connectives -- conjunction, disjunction, negation, existential
    quantification, even equality -- can be encoded using just these.

    This chapter explains the encodings and shows how the tactics
    we've seen can be used to carry out standard forms of logical
    reasoning involving these connectives. *)

(* ########################################################### *)
(** * Conjunction *)

(** The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(** Note that, like the definition of [ev] in the previous
    chapter, this definition is parameterized; however, in this case,
    the parameters are themselves propositions, rather than numbers. *)

(** The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)

(** Consider the "type" of the constructor [conj]: *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** Notice that it takes 4 inputs -- namely the propositions [P]
    and [Q] and evidence for [P] and [Q] -- and returns as output the
    evidence of [P /\ Q]. *)

(** Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  (* Case "left". *) apply b_0.
  (* Case "right". *) apply b_3.  Qed.

(** Let's take a look at the proof object for the above theorem. *)

Print and_example. 
(* ===>  conj (beautiful 0) (beautiful 3) b_0 b_3
            : beautiful 0 /\ beautiful 3 *)

(** Note that the proof is of the form
    conj (beautiful 0) (beautiful 3) 
         (...pf of beautiful 3...) (...pf of beautiful 3...)
    as you'd expect, given the type of [conj]. *)

(** Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)

Theorem and_example' : 
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.

(** Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and add variables representing
    this evidence to the proof context. *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2) *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  (* SOLUTION: *)
  intros P Q H. 
  inversion H as [HP HQ].
  apply HQ.  Qed.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    (* Case "left". *) apply HQ. 
    (* Case "right".*) apply HP.  Qed.
  
(** Once again, we have commented out the [Case] tactics to make the
    proof object for this theorem easy to understand.  Examining it
    shows that all that is really happening is taking apart a record
    containing evidence for [P] and [Q] and rebuilding it in the
    opposite order: *)

Print and_commut.
(* ===>
   and_commut = 
     fun (P Q : Prop) (H : P /\ Q) =>
     let H0 := match H with
               | conj HP HQ => conj Q P HQ HP
               end 
     in H0
     : forall P Q : Prop, P /\ Q -> Q /\ P *)

(** **** Exercise: 2 stars (and_assoc) *)
(** In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
(* SOLUTION: *)
  split.
    Case "left". split.
      SCase "left". apply HP.
      SCase "right". apply HQ.
    Case "right". apply HR.  Qed.
(** [] *)

(** **** Exercise: 2 stars (even__ev) *)
(** Now we can prove the other direction of the equivalence of [even]
   and [ev], which we left hanging in chapter [Prop].  Notice that the
   left-hand conjunct here is the statement we are actually interested
   in; the right-hand conjunct is needed in order to make the
   induction hypothesis strong enough that we can carry out the
   reasoning in the inductive step.  (To see why this is needed, try
   proving the left conjunct by itself and observe where things get
   stuck.) *)

Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* Hint: Use induction on [n]. *)
  (* SOLUTION: *)
  intros n. induction n as [| n' ].
  Case "n = O". simpl. split.
    SCase "left conjunct". intros eq. apply ev_0.
    SCase "right conjunct". intros eq. inversion eq.
  Case "n = S n'". split. 
    SCase "left conjunct". intros eq. inversion IHn' as [Hn HSn].
      apply HSn. apply eq.
    SCase "right conjunct". intros eq. inversion IHn' as [Hn HSn].
      apply ev_SS. unfold even in eq. simpl in eq. apply Hn. apply eq. Qed. 
(** [] *)

(** **** Exercise: 2 stars, optional (conj_fact) *)
(** Construct a proof object demonstrating the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  (* SOLUTION: *)
  fun P Q R HPQ HQR =>
    match (HPQ,HQR) with
    | (conj HP _, conj _ HR) => conj P R HP HR
    end.
(** [] *)

(* ###################################################### *)
(** ** Iff *)

(** The handy "if and only if" connective is just the conjunction of
    two implications. *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** Exercise: 1 star, optional (iff_properties) *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  (* SOLUTION: *)
  intros P. split.
    Case "->". intros H. apply H.
    Case "<-". intros H. apply H.  Qed.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* SOLUTION: *)
  intros P Q R H G.
  inversion H as [HAB HBA].
  inversion G as [HBC HCB].
  split.
    Case "->". intros HP. apply HBC. apply HAB. apply HP.
    Case "<-". intros HR. apply HBA. apply HCB. apply HR.  Qed.

(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** [] *)

(** **** Exercise: 2 stars, advanced (beautiful_iff_gorgeous) *)

(** We have seen that the families of propositions [beautiful] and
    [gorgeous] actually characterize the same set of numbers.
    Prove that [beautiful n <-> gorgeous n] for all [n].  Just for
    fun, write your proof as an explicit proof object, rather than
    using tactics. (_Hint_: if you make use of previously defined
    theorems, you should only need a single line!) *)

Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
  (* SOLUTION: *)
  fun n => conj _ _ (beautiful__gorgeous n) (gorgeous__beautiful n). 
(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)

(* ############################################################ *)
(** * Disjunction *)

(** Disjunction ("logical or") can also be defined as an
    inductive proposition. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Consider the "type" of the constructor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** It takes 3 inputs, namely the propositions [P], [Q] and
    evidence of [P], and returns, as output, the evidence of [P \/ Q].
    Next, look at the type of [or_intror]: *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)

(** Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. *)

(** Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.



(** **** Exercise: 2 stars, optional (or_commut'') *)
(** Try to write down an explicit proof object for [or_commut] (without
    using [Print] to peek at the ones we already defined!). *)

(* SOLUTION: *)
Definition or_commut'' : forall P Q, P \/ Q -> Q \/ P :=
    fun (P Q : Prop) (H : P \/ Q) =>
      match H with
      | or_introl HP => or_intror Q P HP
      | or_intror HQ => or_introl Q P HQ
      end. 
(** [] *)

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. inversion H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** Exercise: 2 stars (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  (* SOLUTION: *)
  intros P Q R. intros H.
  inversion H as [[HAl | HQ] [HAr | HR]].
    Case "left,left". left. apply HAl.
    Case "left,right". left. apply HAl.
    Case "right,left". left. apply HAr.
    Case "right,right". right. split. apply HQ. apply HR. Qed.
(** [] *)

(** **** Exercise: 1 star, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* SOLUTION: *)
  intros P Q R. split.
    Case "->". apply or_distributes_over_and_1.
    Case "<-". apply or_distributes_over_and_2.  Qed.
(** [] *)

(* ################################################### *)
(** ** Relating [/\] and [\/] with [andb] and [orb] (advanced) *)

(** We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are clearly analogs of the logical connectives [/\] and [\/].
    This analogy can be made more precise by the following theorems,
    which show how to translate knowledge about [andb] and [orb]'s
    behaviors on certain inputs into propositional facts about those
    inputs. *)

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(** **** Exercise: 2 stars, optional (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  (* SOLUTION: *)
  intros b c H.
  destruct b.
  Case "b=true".
    destruct c.
    SCase "c=true".
      simpl in H. inversion H.
    SCase "c=false".
      right. reflexivity.
  Case "b=false".
    left. reflexivity.  Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  (* SOLUTION: *)
  intros b c H.
  destruct b.
  Case "b=true".
    left. reflexivity.
  Case "b=false".    
    destruct c.
    SCase "c=true".
      right. reflexivity.
    SCase "c=false".
      simpl in H. inversion H.  Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  (* SOLUTION: *)
  intros b c H.
  destruct b.
  Case "b=true".
    inversion H.
    split. reflexivity.
  Case "b=false".
    destruct c.
    SCase "c=true".
      inversion H.
    SCase "c=false".
      reflexivity.  Qed.
(** [] *)

(* ################################################### *)
(** * Falsehood *)

(** Logical falsehood can be represented in Coq as an inductively
    defined proposition with no constructors. *)

Inductive False : Prop := . 

(** Intuition: [False] is a proposition for which there is no way
    to give evidence. *)


(** Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)

(** Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)

(* #################################################### *)
(** ** Truth *)

(** Since we have defined falsehood in Coq, one might wonder whether
    it is possible to define truth in the same way.  We can. *)

(** **** Exercise: 2 stars, advanced (True) *)
(** Define [True] as another inductively defined proposition.  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.) *)

(* SOLUTION: *)
Inductive True : Prop :=
 I : True.
(** [] *)

(** However, unlike [False], which we'll use extensively, [True] is
    just a theoretical curiosity: it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. *)

(* #################################################### *)
(** * Negation *)

(** The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)

Definition not (P:Prop) := P -> False.

(** The intuition is that, if [P] is not true, then anything at
    all (even [False]) follows from assuming [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(** It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced (double_neg_inf) *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* SOLUTION: *) Let a proposition [P] be given, and suppose we have
   evidence for [P].  We must show [~~P] -- i.e., [~P -> False], so
   suppose [~P] as well.  Then we have both [P] and [~P], a
   contradiction, so [~~P] holds.
   []
*)

(** **** Exercise: 2 stars (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* SOLUTION: *)
  intros P Q H HNotB HP.
  apply HNotB.  apply H. apply HP.  Qed.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  (* SOLUTION: *)
  intros P H. inversion H as [HP HNA]. apply HNA. apply HP.  Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* SOLUTION: *)
(* _Proof_: Suppose, for some [P], that [(P /\ ~P)] holds.  Recall
  that [~P] is defined as [P -> False].  Given [P] and [P -> False],
  we can prove [False], so [(P /\ ~P) -> False], i.e., [~(P /\ ~P)].
*)
(** [] *)

Theorem five_not_even :  
  ~ ev 5.
Proof. 
  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn]. 
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

(** **** Exercise: 1 star (ev_not_ev_S) *)
(** Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H. (* not n! *)
  (* SOLUTION: *)
    Case "ev_0". intros H. inversion H.
    Case "ev_SS". intros G. inversion G as [| n' HevSn Heqn'].
      apply IHev. apply HevSn.  Qed.
(** [] *)

(** Note that some theorems that are true in classical logic are _not_
    provable in Coq's (constructive) logic.  E.g., let's look at how
    this proof gets stuck... *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H. 
  (* But now what? There is no way to "invent" evidence for [~P] 
     from evidence for [P]. *) 
  Admitted.

(** **** Exercise: 5 stars, advanced, optional (classical_axioms) *)
(** For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

(* SOLUTION: *)
Lemma ito__em :
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or, excluded_middle.
  intros Hito P.
  apply or_commut.
  apply Hito.
  intros HP. apply HP.
Qed.

Lemma em__ito :
  excluded_middle -> implies_to_or.
Proof.
  unfold implies_to_or, excluded_middle.
  intros Hem P Q H.
  assert (P \/ ~P) by apply Hem.
  inversion H0 as [HP | HNP].
    Case "P". right. apply H. apply HP.
    Case "~P". left. apply HNP.
Qed.

Lemma em__demorgan :
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle, de_morgan_not_and_not.
  intros Hem P Q H.
  assert (P \/ ~P) by apply Hem.
  inversion H0 as [HP | HNP].
    Case "P".
      left. apply HP.
    Case "~P".
      assert (Q \/ ~Q) by apply Hem.
      inversion H1 as [HQ | HNQ].
      SCase "Q".
        right. apply HQ.
      SCase "~Q".
        apply ex_falso_quodlibet. apply H.
        split. apply HNP. apply HNQ.
Qed.

Lemma demorgan__em :
  de_morgan_not_and_not -> excluded_middle.
Proof.
  unfold de_morgan_not_and_not, excluded_middle.
  intros Hdm P.
  apply Hdm.
  unfold not. intros Hcontra.
  inversion Hcontra as [HNP HNNP].
  apply HNNP. apply HNP.
Qed.

Lemma em__classic :
  excluded_middle -> classic.
Proof.
  unfold excluded_middle, classic, not.
  intros Hem P.
  assert (P \/ (P -> False)) by apply Hem.
  inversion H as [HP | HNP].
    Case "P". intros H'. apply HP.
    Case "~P". intros H'. apply H' in HNP. inversion HNP.
Qed.

Lemma classic__demorgan :
  classic -> de_morgan_not_and_not.
Proof.
  unfold classic, de_morgan_not_and_not, not.
  intros Hc P Q H.
  apply Hc.
  intros H2.
  apply H.
  split.
    Case "left conjunct". intros HP. apply H2. left. apply HP.
    Case "right conjunct". intros HQ. apply H2. right. apply HQ.
Qed.

(** The above suffices (along with [demorgan__em]), but we can also
    prove it directly this way *)

Lemma classic__em :
  classic -> excluded_middle.
Proof.
  unfold classic, excluded_middle, not.
  intros Hc P.
  apply Hc.
  intros H.
  apply H.
  right.
    intros HP. apply H.
    left. apply HP.
Qed.
  
Lemma em__peirce : 
  excluded_middle -> peirce.
Proof.
  unfold excluded_middle, peirce.
  intros Hem P Q H.
  assert (P \/ ~P) by apply Hem.
  inversion H0 as [HP | HNP].
    Case "P". apply HP.
    Case "~P". 
      assert ((P -> Q) \/ ~(P -> Q)) by apply Hem.
      inversion H1 as [HPQ | HNPQ].
      SCase "P->Q". apply H. apply HPQ.
      SCase "~(P->Q)". assert (P -> Q) as HPQ.
        intros HP.
        apply ex_falso_quodlibet. 
        apply HNP. apply HP.
      apply H. apply HPQ.
Qed.

Lemma peirce__em :
  peirce -> excluded_middle.
Proof.
  unfold peirce, excluded_middle, not.
  intros Hp P. 
  apply Hp with False.
  right.
    intros HP. apply H.
    left. apply HP.
Qed. 

(** [] *)

(* ########################################################## *)
(** ** Inequality *)

(** Saying [x <> y] is just the same as saying [~(x = y)]. *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(** Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.



(** **** Exercise: 2 stars (not_eq_beq_false) *)
Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof. 
  (* SOLUTION: *)
  intros n n' H. unfold not in H. 
   remember (beq_nat n n') as e. destruct e. 
   Case "e = true (contradictory)". 
     apply ex_falso_quodlibet. apply H. 
     apply beq_nat_eq in Heqe. apply Heqe. 
   Case "e = false". 
    reflexivity.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (beq_false_not_eq) *)
Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  (* SOLUTION: *) 
  intros n m H Heq.
  rewrite <- Heq in H. 
  rewrite <- beq_nat_refl in H.
  inversion H. Qed.
  (** [] *)

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

    For example, consider this existentially quantified proposition: *)

Definition some_nat_is_even : Prop := 
  ex nat ev.

(** To prove this proposition, we need to choose a particular number
    as witness -- say, 4 -- and give some evidence that that number is
    even. *)

Definition snie : some_nat_is_even := 
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note, again, that we have to explicitly give the witness. *)

(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* SOLUTION: *)
(* There is some number whose successor is beautiful. *)

(** Complete the definition of the following proof object: *)

Definition p : ex nat (fun n => beautiful (S n)) :=
(* SOLUTION: *)
  ex_intro nat (fun n => beautiful (S n)) 2 b_3.
(** [] *)

(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" and "there is no [x] for
    which [P] does not hold" are equivalent assertions. *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  (* SOLUTION: *)
  intros X P H G. inversion G as [x Hx]. 
  apply Hx. apply H.  Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* SOLUTION: *)
  intros EM X P H x.
  assert (P x \/ ~ P x) as H1 by apply EM.
  inversion H1 as [HPx | HNPx].
  Case "P x".
    apply HPx.
  Case "~P x".
    apply ex_falso_quodlibet. 
    apply H.
    apply ex_intro with (witness:=x).
    apply HNPx.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* SOLUTION: *)
  intros X P Q. split.
  Case "->". intros H. inversion H as [x Hx].
    inversion Hx as [HP | HQ].
    SCase "P x". left. exists x. apply HP.
    SCase "Q x". right. exists x. apply HQ.
  Case "<-". intros H. inversion H as [HPx | HQx]. 
    SCase "exists x, P x". inversion HPx as [x Hx]. exists x. 
      left. apply Hx.
    SCase "exists x, Q x". inversion HQx as [x Hx]. exists x. 
      right. apply Hx.  Qed.
(** [] *)

(* Print dist_exists_or. *)

(* ###################################################### *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  It has (roughly)
    the following inductive definition. *)

(* (We enclose the definition in a module to avoid confusion with the
    standard library equality, which we have used extensively
    already.) *)

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.

(** Standard infix notation: *)

Notation "x = y" := (eq _ x y) 
                    (at level 70, no associativity) 
                    : type_scope.

(** The definition of [=] is a bit subtle.  The way to think about it
    is that, given a set [X], it defines a _family_ of propositions
    "[x] is equal to [y]," indexed by pairs of values ([x] and [y])
    from [X].  There is just one way of constructing evidence for
    members of this family: applying the constructor [refl_equal] to a
    type [X] and a value [x : X] yields evidence that [x] is equal to
    [x]. *)

(** **** Exercise: 2 stars (leibniz_equality) *)
(** The inductive definitions of equality corresponds to _Leibniz equality_: 
   what we mean when we say "[x] and [y] are equal" is that every 
   property on [P] that is true of [x] is also true of [y].  *)

Lemma leibniz_equality : forall (X : Type) (x y: X), 
 x = y -> forall P : X -> Prop, P x -> P y.
Proof.
(* SOLUTION: *)
intros X x y H.
induction H.
intros P H. apply H.
Qed.
(** [] *)

(** We can use
    [refl_equal] to construct evidence that, for example, [2 = 2].
    Can we also use it to construct evidence that [1 + 1 = 2]?  Yes:
    indeed, it is the very same piece of evidence!  The reason is that
    Coq treats as "the same" any two terms that are _convertible_
    according to a simple set of computation rules.  These rules,
    which are similar to those used by [Eval simpl], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.
    
    In tactic-based proofs of equality, the conversion rules are
    normally hidden in uses of [simpl] (either explicit or implicit in
    other tactics such as [reflexivity]).  But you can see them
    directly at work in the following explicit proof objects: *)

Definition four : 2 + 2 = 1 + 3 :=  
  refl_equal nat 4. 

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
  fun (X:Set) (x:X) => refl_equal (list X) [x]. 

End MyEquality.


(* ####################################################### *)
(** ** Inversion, Again (Advanced) *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,
        
      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)

(** _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be the same!  The [inversion] tactic adds this fact to the
   context.  *)


(** **** Exercise: 1 star, optional (dist_and_or_eq_implies_and) *)  
Lemma dist_and_or_eq_implies_and : forall P Q R,
P /\ (Q \/ R) /\ Q = R -> P/\Q.
Proof.
(* SOLUTION: *)
intros P Q R H.
inversion H. inversion H1.
split. 
Case "left". 
apply H0. 
Case "right".
inversion H2. 
SCase "left". apply H4. 
SCase "right".
inversion H3. (* rewrite H3. *)
apply H4.
Qed.
(** [] *)

(* ########################################################### *)
(** * Quantification and Implication *)

(** In fact, the built-in logic is even smaller than it appears, since
    [->] and [forall] are actually the _same_ primitive!

    The [->] notation is actually just a shorthand for a degenerate
    use of [forall]. *)

(** For example, consider this proposition: *)

Definition funny_prop1 := 
  forall n, forall (E : beautiful n), beautiful (n+3).

(** A proof term inhabiting this proposition would be a function
    with two arguments: a number [n] and some evidence [E] that [n] is
    beautiful.  But the name [E] for this evidence is not used in the
    rest of the statement of [funny_prop1], so it's a bit silly to
    bother making up a name for it.  We could write it like this
    instead, using the dummy identifier [_] in place of a real
    name: *)

Definition funny_prop1' := 
  forall n, forall (_ : beautiful n), beautiful (n+3).

(** Or, equivalently, we can write it in more familiar notation: *)

Definition funny_prop1'' := 
  forall n, beautiful n -> beautiful (n+3). 

(** In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* ####################################################### *)
(** * Relations *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.  

(** We've seen an inductive definition of one fundamental relation:
    equality.  Another useful one is the "less than or equal to"
    relation on numbers: *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [~(2 <= 1)].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars (total_relation) *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

(* SOLUTION: *)
Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.
(** [] *)

(** **** Exercise: 2 stars (empty_relation) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(* SOLUTION: *)
Inductive empty_relation : nat -> nat -> Prop := .
(** [] *)

(** **** Exercise: 3 stars (R_provability) *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(* SOLUTION: *)
   - The first proposition is provable and the second is not.
     The proof term for the first is:
       (c3 _ _ _ (c2 _ _ _ c1)).
   - Dropping [c5] would not change the set of provable
     propositions.  [c4] and [c1] don't interact with [c5], since
     they're already symmetric in [m] and [n]; [c2] followed by
     [c5] is equivalent to [c3], and vice versa.

   - Dropping [c4] would not change the set of provable
     propositions.  [c4] is equivalent to undoing an application
     of [c2] and an application of [c3].
[]
*)

(** **** Exercise: 3 stars, optional (R_fact) *)  
(** State and prove an equivalent characterization of the relation
    [R].  That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

(* SOLUTION: *)
Theorem R_plus: forall m n o, R m n o <-> m + n = o.
Proof.
  intros m n o. split.
  Case "->". intros H. induction H.
    SCase "c1". reflexivity.
    SCase "c2". simpl. rewrite IHR. reflexivity.
    SCase "c3". rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
    SCase "c4". simpl in IHR. rewrite <- plus_n_Sm in IHR.
      inversion IHR. reflexivity.
    SCase "c5". rewrite plus_comm. apply IHR.
  Case "<-". generalize dependent n. generalize dependent m. 
    induction o as [|o']. 
    SCase "o = 0". 
      intros m n H.
      destruct m as [|m'].
      SSCase "m = 0". 
        simpl in H. rewrite -> H. apply c1.
      SSCase "m = S m'".
        inversion H.
    SCase "o = S o'".
      intros m n H. destruct m as [|m'].
      SSCase "m = 0".
        simpl in H. rewrite -> H. apply c3. apply IHo'. 
        reflexivity.
      SSCase "m = S m'".
        apply c2. apply IHo'. inversion H. reflexivity.
Qed.

(** [] *)

End R.

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  (* SOLUTION: *)
| all_nil : all X P []
| all_cons : forall x l, P x -> all X P l -> all X P (x::l)
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

(* SOLUTION: *)
Theorem forallb_spec : forall X test l, 
   forallb test l = true <-> all X (fun x => test x = true) l.
Proof.
  intros X test.
  split.
  Case "-> direction". induction l as [|x l'].
    SCase "l = []". simpl. intros. apply all_nil.
    SCase "l = x::l'". simpl. 
      intros H. apply andb_true__and in H. inversion H as [H1 H2].
      apply all_cons. apply H1. apply IHl'. apply H2.
  Case "<- direction". induction l as [|x l'].
    SCase "l = []". simpl. reflexivity.
    SCase "l = x::l'". simpl.
      intros H. inversion H.
      apply and__andb_true. split.
        apply H2.
        apply IHl'. apply H3.
Qed. 

(* This theorem exactly captures the input-output behaviour of [allb]. However, 
   it does not say anything about the running time. *)
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

(* SOLUTION: *)
Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | merge_empty : 
      merge [] [] [] 
  | merge_left : forall l1 l2 l3 x, 
      merge l1 l2 l3 -> 
      merge (x::l1) l2 (x::l3)
  | merge_right : forall l1 l2 l3 x, 
      merge l1 l2 l3 -> 
      merge l1 (x::l2) (x::l3).  

Theorem filter_good : forall {X : Type}, 
                      forall (test : X->bool), 
                      forall (l1 l2 l3 : list X),
  forallb test l1 = true ->
  forallb (fun x => negb (test x)) l2 = true ->
  merge l1 l2 l3 ->
  filter test l3 = l1.
Proof.
  intros X test l1 l2 l3 HT HF HM.
  induction HM.  
  Case "merge_empty". reflexivity.
  Case "merge_left". unfold filter.
    remember (test x) as testx. destruct testx.
    SCase "test x = true". unfold filter in IHHM. rewrite -> IHHM. reflexivity.
      unfold forallb in HT. rewrite <- Heqtestx in HT. apply HT. apply HF.
    SCase "test x = false". unfold forallb in HT. rewrite <- Heqtestx in HT.
      inversion HT.
  Case "merge_right". unfold filter.
    remember (test x) as testx. destruct testx.
    SCase "test x = true". unfold forallb in HF. rewrite <- Heqtestx in HF.
      inversion HF.  
    SCase "test x = false". 
      unfold filter in IHHM. rewrite -> IHHM. reflexivity.
      apply HT. unfold forallb in HF. rewrite <- Heqtestx in HF. apply HF. 
Qed.

(* An alternate solution: *)
Lemma cons_eq : forall X (x:X) l1 l2, l1 = l2 -> x::l1 = x::l2.
Proof. intros. rewrite -> H. reflexivity. Qed.

Lemma negb_true : forall b, negb b = true -> b = false.
Proof. intros b eq. destruct b; [inversion eq | reflexivity]. Qed.

Theorem filter_spec : forall (X:Type) (test:X->bool) (l l1 l2:list X),
 merge l1 l2 l ->
 forallb test l1 = true ->
 forallb (fun x => negb (test x)) l2 = true ->
 l1 = filter test l.
Proof.
 intros X test l1 l2 l3 HM. induction HM.
 Case "merge_empty". intros HT HF. simpl. reflexivity.
 Case "merge_left". intros HT HF. simpl. simpl in HT.
   apply andb_true__and in HT. inversion HT as [HX HL1].
   rewrite -> HX. apply cons_eq. apply IHHM. apply HL1. apply HF.
 Case "merge_right". intros HT HF. simpl. simpl in HF.
   apply andb_true__and in HF. inversion HF as [HX HL2].
   apply negb_true in HX. rewrite -> HX. apply IHHM. apply HT. apply HL2.
Qed.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

(* SOLUTION: *)
(** We reproduce the definition of subseq here, with a different name
    so it doesn't conflict. *)
Inductive subseq' {X:Type} : list X -> list X -> Prop :=
  | sub_nil  : forall l, subseq' [] l
  | sub_take : forall x l1 l2, subseq' l1 l2 -> subseq' (x :: l1) (x :: l2)
  | sub_skip : forall x l1 l2, subseq' l1 l2 -> subseq' l1 (x :: l2).

(** A few lemmas about subseq. *)
Lemma subseq_drop_l : forall (X:Type) (x:X) (l1 l2 : list X),
  subseq' (x :: l1) l2 -> subseq' l1 l2.
Proof.
  intros X x l1 l2 Hsub.
  induction l2 as [|x' l2'].
  Case "l2 = []". inversion Hsub.
  Case "l2 = x' :: l2'".
    inversion Hsub.
    SCase "sub_take". apply sub_skip. apply H0.
    SCase "sub_skip". apply sub_skip. apply IHl2'. apply H1.
Qed.

Lemma subseq_drop : forall (X:Type) (x:X) (l1 l2 : list X),
  subseq' (x :: l1) (x :: l2) -> subseq' l1 l2.
Proof.
  intros X x l1 l2 Hsub.
  inversion Hsub.
    apply H0.
    apply subseq_drop_l with x. apply H1.
Qed.

(** Now for some silly lemmas about [<=], which we need since we
    redefined [<=] ourselves. Of course, these are all in the Coq
    standard library. *)

Lemma le_0_n : forall n, 0 <= n.
Proof.
  induction n as [|n']. 
    apply le_n. 
    apply le_S. apply IHn'.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2.
    apply H1.
    apply le_S. apply IHle.
Qed.

Lemma le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H.
Qed.

Lemma le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  Case "m = n". apply le_n.
  Case "S n <= m". apply le_Sn_le. apply H1.
Qed.

Lemma le_n_S : forall n m, n <= m -> S n <= S m.
Proof.
  intros n m H. induction H.
    apply le_n.
    apply le_S. apply IHle.
Qed.

Lemma Sn_le_n : forall n, ~ (S n <= n).
Proof.
  unfold not. induction n as [|n'].
  Case "n = 0". intros contra. inversion contra.
  Case "n = S n'". intros H. apply IHn'.
  apply le_S_n. apply H.
Qed.

(** A list is _maximal_ with property [P] if it has the property, and
    every other list with the property is at most as long as it is. *)

Definition maximal {X:Type} (lmax : list X) (P : list X -> Prop) := P
lmax /\ forall l', P l' -> length l' <= length lmax.

(** A "good subsequence" for a given list [l] and a [test] is a
    subsequence of [l] all of whose members evaluate to [true] under
    the [test]. *)

Definition good_subseq {X:Type} (test : X -> bool) (l lsub : list X) :=
  subseq' lsub l /\ forallb test lsub = true.

(** Good subsequences can be extended with good elements. *)

Lemma good_subseq_extend : forall (X:Type) (test : X -> bool) 
                                  (l lsub : list X) (x : X),
  good_subseq test l lsub -> 
  test x = true -> 
  good_subseq test (x::l) (x::lsub).
Proof.
  intros X test l lsub x [Hsub Hall] Hx. split.
  Case "subseq". apply sub_take. apply Hsub.
  Case "all". simpl. rewrite Hx. apply Hall.
Qed.

(** If [lmax] is a maximal good subsequence of [x :: l] and [x] is not good,
    then [lmax] is also a maximal good subsequence of [l]. *)

Lemma maximal_strengthening : forall (X:Type) (x:X) 
                                     (lmax l : list X) 
                                     (test : X -> bool),
  maximal lmax (good_subseq test (x::l)) ->
  test x = false ->
  maximal lmax (good_subseq test l).
Proof.
  intros X x lmax l test [[Hsub Hall] Hlen] Hx.
  split. split.
  Case "subseq".
    inversion Hsub.
    SCase "sub_nil". apply sub_nil.
    SCase "sub_take". rewrite H in H0.
      rewrite <- H0 in Hall. simpl in Hall. rewrite Hx in Hall. inversion Hall.
    SCase "sub_skip". apply H1.
  Case "all". apply Hall.
  Case "len". intros l' [Hsub' Hall']. apply Hlen. split.
    SCase "subseq". apply sub_skip. apply Hsub'.
    SCase "all". apply Hall'.
Qed.

(** Some easy lemmas about filter: its result is a good subsequence of
    the original list. *)

Lemma filter_subseq : forall (X:Type) (l : list X) (test : X -> bool),
  subseq' (filter test l) l.
Proof.
  intros X l test. induction l as [|x l'].
  Case "l = []". apply sub_nil.
  Case "l = x :: l'". simpl. destruct (test x).
    SCase "test x = true". apply sub_take. apply IHl'.
    SCase "test x = false". apply sub_skip. apply IHl'.
Qed.

Lemma filter_all : forall (X:Type) (l : list X) (test : X -> bool),
  forallb test (filter test l) = true.
Proof.
  intros X l test. induction l as [|x l'].
  Case "l = []". reflexivity.
  Case "l = x :: l'". simpl. 
    remember (test x) as tx. destruct tx.
    SCase "test x = true". simpl. rewrite <- Heqtx. apply IHl'.
    SCase "test x = false". apply IHl'.
Qed.

(** And now for the main theorem: [lsub] is a maximal good subsequence
    of [l] if and only if [filter test l = lsub]. *)

Theorem filter_spec2 : forall (X:Type) (l lsub:list X) (test : X -> bool),
  maximal lsub (good_subseq test l) <-> filter test l = lsub.
Proof. 
  split.
  Case "->". 
    generalize dependent lsub.
    induction l as [|x l'].
    SCase "l = []". 
      (* lsub = [] since lsub is a subseq of l. *)
      intros lsub [[Hsub _] _].
      inversion Hsub. reflexivity.
    SCase "l = x :: l'".
      intros lsub H. simpl.
      remember (test x) as tx. destruct tx.
      SSCase "test x = true".
        destruct H as [[Hsub Hall] Hlen].
        (* in this case, lsub must begin with x, since otherwise it
           wouldn't be maximal. *)
        destruct lsub as [|x' lsub'].
        SSSCase "lsub = []". (* impossible: contradicts maximality of lsub *)
          assert (length [x] <= length ([] : list X)) as contra.
          SSSSCase "proof of assertion".
            apply Hlen. split. 
              apply sub_take. apply sub_nil.
              simpl. rewrite <- Heqtx. reflexivity.
          inversion contra.
        SSSCase "lsub = x' :: lsub'".
          assert (x = x'). (* because of maximality again *)
          SSSSCase "proof of assertion".
            inversion Hsub. 
            SSSSSCase "sub_take". reflexivity.
            SSSSSCase "sub_skip". (* contradiction, since x :: x' :: lsub' 
                                     would be longer *)
              assert (length (x :: x' :: lsub') <= length (x' :: lsub')).
              SSSSSSCase "proof of assertion".
                apply Hlen. split.
                  apply sub_take. apply H1.
                  simpl. rewrite <- Heqtx. simpl. simpl in Hall.
                  apply Hall.
              simpl in H3. apply Sn_le_n in H3. inversion H3.
          rewrite H.
          rewrite -> (IHl' lsub'). reflexivity.
          split. split. rewrite H in Hsub. apply subseq_drop with x'. apply Hsub.
            simpl in Hall. apply andb_true_elim2 in Hall. apply Hall.
            intros l0 Hgood0. rewrite <- H in Hlen. simpl in Hlen.
            apply le_S_n. 
            apply (Hlen (x :: l0)). apply good_subseq_extend. apply Hgood0.
            symmetry. apply Heqtx.
      SSCase "test x = false".
        apply IHl'. 
        apply maximal_strengthening with x. apply H.
        symmetry. apply Heqtx.
  Case "<-". intros Hfilter.
    split. split.
    SCase "subseq". rewrite <- Hfilter. apply filter_subseq.
    SCase "all". rewrite <- Hfilter. apply filter_all.
    SCase "len". generalize dependent lsub. induction l as [|x l2].
      SSCase "l = []". intros lsub _ l' [Hsub _]. inversion Hsub. apply le_0_n.
      SSCase "l = x :: l2". intros lsub Hfilter l' [Hsub Hall].
        simpl in Hfilter.
        remember (test x) as tx. destruct tx.
        SSSCase "test x = true".
          rewrite <- Hfilter. inversion Hsub.
          SSSSCase "sub_nil". apply le_0_n.
          SSSSCase "sub_take". simpl. apply le_n_S.
            apply IHl2. reflexivity. split. apply H1. rewrite <- H0 in Hall.
              simpl in Hall. apply andb_true_elim2 in Hall. apply Hall.
          SSSSCase "sub_skip". simpl. apply le_S.
            apply IHl2. reflexivity. split. apply H1. apply Hall.
        SSSCase "test x = false".
          apply IHl2. apply Hfilter. split. 
          inversion Hsub. apply sub_nil. rewrite <- H0 in Hall. rewrite H in Hall.
            simpl in Hall. rewrite <- Heqtx in Hall. inversion Hall.
            apply H1.
          apply Hall.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  (* SOLUTION: *)
  intros X xs ys x. 
  Case "->".
    induction xs as [|x' xs']. 
    SCase "xs = nil".
      intros AI. 
      simpl in AI. right. apply AI. 
    SCase "xs = x'::xs'".
      intros AI.
      simpl in AI.  inversion AI as [l | b l]. 
      SSCase "ai_here".
        left. apply ai_here.
      SSCase "ai_later".    
         assert (AI' : appears_in x xs' \/ appears_in x ys). 
            apply IHxs'.  apply H0. 
         destruct AI'. 
         SSSCase "left".
           left.  apply ai_later.  apply H2. 
         SSSCase "right".
           right.  apply H2.  Qed.
  
Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  (* SOLUTION: *)
  intros X xs ys x. 
    induction xs as [|x' xs']. 
    SCase "xs = nil".
      intros [AI1 | AI2].
        SSCase "left".
          inversion AI1.
        SSCase "right".
          apply AI2.
    SCase "xs = x'::xs'".
      intros [AI1 | AI2]. 
        SSCase "left". 
           inversion AI1. 
           SSSCase "ai_here". 
             apply ai_here.
           SSSCase "ai_later". 
             simpl. apply ai_later. apply IHxs'. left. apply H0. 
        SSCase "right". 
          simpl.  apply ai_later.  apply IHxs'. right. apply AI2.  Qed.
  
(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

(* SOLUTION: *)
Definition disjoint {X:Type} (l1 l2: list X) :=
  forall (x:X), appears_in x l1 -> ~ appears_in x l2.

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

(* SOLUTION: *)
Inductive no_repeats {X:Type} : list X -> Prop :=
  | nr_nil : no_repeats nil
  | nr_cons : forall a l, 
              no_repeats l ->
              ~ (appears_in a l) ->
              no_repeats (a::l).

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

(* SOLUTION: *)
(* Here are some possible answers: *)
  
Lemma no_repeats_append : forall {X:Type} (l1 l2: list X),
   no_repeats l1 -> no_repeats l2 -> disjoint l1 l2 -> no_repeats (l1 ++ l2).
Proof.
  intros X l1. induction l1 as [| x l1']. 
  Case "l1 = nil".
    intros l2 NR1 NR2 D.  simpl. apply NR2. 
  Case "l1 = x:l1'".
    intros l2 NR1 NR2 D. simpl.
    apply nr_cons.  apply IHl1'. inversion NR1 as [| ? ? NRl1' NA]. 
    apply NRl1'. apply NR2. 
    unfold disjoint. intros x0 AI.  apply D. apply ai_later.  apply AI.
    intro contra.  apply appears_in_app in contra.  inversion contra. 
    inversion NR1 as [| ? ? NRl1' NA]. apply NA. apply H. 
    unfold disjoint in D.  apply D with x.  
    apply ai_here.
    apply H. 
Qed.

Lemma no_repeats_disjoint : forall {X:Type} (l1 l2: list X), 
                            no_repeats (l1++l2) -> disjoint l1 l2.
Proof.
   unfold disjoint.
   induction l1 as [|x l1']. 
     intros l2 NR x AI.  inversion AI. 
     intros l2 NR x0 AI.  simpl in NR. inversion NR. inversion AI.  
       intro contra. apply H2. 
          apply app_appears_in.  right. apply contra. 
       apply IHl1'.  apply H1. apply H4.
Qed.

(* We can also show the following results about [no_repeats] and [++]
   by themeselves *)
Lemma no_repeats_left : forall {X:Type} (l1 l2: list X),
                        no_repeats (l1++l2) -> no_repeats l1.
Proof.
   induction l1 as [|x l1'].  
       intros l2 NR. apply nr_nil.
       intros l2 NR. inversion NR. apply nr_cons. apply (IHl1' l2).  apply H1.
       intro contra. apply H2. apply app_appears_in.  left. apply contra. 
Qed.
       

Lemma no_repeats_right: forall {X:Type} (l1 l2: list X),
                        no_repeats (l1++l2) -> no_repeats l2.
Proof.
   induction l1 as [|x l1'].
     intros l2 NR. simpl in NR.  apply NR. 
     intros l2 NR. inversion NR. apply IHl1'.  apply H1. 
Qed.

(* This theorem combines the various lemmas to give a complete
   characterization *)
Theorem no_repeats_disjoint_app : forall {X:Type} (l1 l2: list X),
  no_repeats (l1++l2) <->
  (no_repeats l1 /\ no_repeats l2 /\ disjoint l1 l2).
Proof.
  intros X l1 l2. 
  split.
  Case "->".
    intro NR. split.
      apply no_repeats_left with l2. apply NR.
      split.
        apply no_repeats_right with l1. apply NR.
        apply no_repeats_disjoint. apply NR.
  Case "<-".
    intros [NR1 [NR2 DISJ]]. 
    apply no_repeats_append. apply NR1. apply NR2.  apply DISJ. 
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises) *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* SOLUTION: *)
  induction n as [| n'].
  Case "n = 0".
    apply le_n.
  Case "n = S n'".
    apply le_S. apply IHn'.  Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  (* SOLUTION: *)
  intros n m H. induction H.
    apply le_n.
    apply le_S. apply IHle.  Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m.  generalize dependent n.  induction m. 
  (* SOLUTION: *)
   intros n H. 
     destruct n. 
       apply le_n.
       inversion H.  inversion H1. 
   intros n H. 
     inversion H; subst. 
       apply le_n. 
       apply le_S.  apply IHm.  assumption.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  (* SOLUTION: *)
  intros a b. induction a.
    apply O_le_n.
    apply n_le_m__Sn_le_Sm in IHa. assumption.  Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 (* SOLUTION: *)
  intros. induction H; unfold lt.
  split. 
    apply n_le_m__Sn_le_Sm. apply le_plus_l.
    rewrite plus_comm. apply n_le_m__Sn_le_Sm. apply le_plus_l. 
  inversion IHle as [Hn1m Hn2m].
    unfold lt in Hn1m, Hn2m.
    apply le_S in Hn1m. apply le_S in Hn2m.
    split. apply Hn1m. apply Hn2m.  Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* SOLUTION: *)
  unfold lt. intros. apply le_S. assumption. Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* SOLUTION: *)
  intros n.
  induction n as [| n']. 
  Case "n = 0". intros m H.
    apply O_le_n.
  Case "n = S n'". intros m H.
    simpl in H. destruct m as [| m'].
    SCase "m = 0".
      inversion H.
    SCase "m = S m'".
      apply IHn' in H.
      apply n_le_m__Sn_le_Sm.
      assumption.  Qed.

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof. 
  (* SOLUTION: *)
  intros n. induction n as [| n'].
  Case "n = 0". intros m H.
    simpl in H. inversion H.
  Case "n = S n'". intros m H.
    destruct m as [| m'].
    SCase "m = 0".
      reflexivity.
    SCase "m = S m'".
      simpl. apply IHn'. simpl in H. assumption.  Qed.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* Hint: Do the right induction! *)
  (* SOLUTION: *)
  intros.
  unfold not. intro Hle. induction Hle.
    Case "le_n".
      rewrite <- ble_nat_refl in H.  inversion H.
    Case "le_S".
      apply IHHle.
      apply ble_nat_n_Sn_false. assumption.  Qed.
(** [] *)

(** **** Exercise: 3 stars (nostutter) *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
 (* SOLUTION: *)
 | nostutter0: nostutter nil
 | nostutter1: forall n, nostutter (n::nil)
 | nostutter2: forall a b r, a<>b -> nostutter(b::r) -> nostutter (a::b::r)
 .

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3,1,4,1,5,6].
(* SOLUTION: *)
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_2:  nostutter [].
(* SOLUTION: *)
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_3:  nostutter [5].
(* SOLUTION: *)
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_4:      not (nostutter [3,1,1,4]).
(* SOLUTION: *)
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall {X:Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  (* SOLUTION: *)
  intros X l1. induction l1 as [|x l1'].
  Case "l1 = nil". reflexivity.
  Case "l1 = x::l1'". intros l2.  simpl. rewrite -> IHl1'. reflexivity. Qed.
  
Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  (* SOLUTION: *)
  induction l as [|x' l']; intros AI. 
  Case "l = nil". inversion AI. 
  Case "l = x'::l'". inversion AI.  
    SCase "x = x'". exists []. exists l'. reflexivity.
    SCase "appears_in x l'". destruct (IHl' H0) as [l1' [l2' EQ]].
       exists (x'::l1'). exists l2'. rewrite -> EQ.  reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* SOLUTION: *)
  | rep_here : forall a l, appears_in a l -> repeats (a::l)
  | rep_later : forall a l, repeats l -> repeats (a::l)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
   represents a list of pigeonhole labels, and list [l1] represents an
   assignment of items to labels: if there are more items than labels,
   at least two items must have the same label.  You will almost
   certainly need to use the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle -> 
  (forall x, appears_in x l1 -> appears_in x l2) -> 
  length l2 < length l1 -> 
  repeats l1.  
Proof.  intros X l1. induction l1.
  (* SOLUTION: *)
    intros l2 EM INC NR.  simpl in NR. inversion NR. 
    intros l2 EM INC NR. 
    destruct (EM (appears_in x l1)). 
      left. assumption.
      right. destruct (appears_in_app_split x l2) as [l2a [l2b EQ]]. 
        apply INC. left.
        apply (IHl1 (l2a ++ l2b) EM). 
         intros x0 AI.  
          assert (x0 <> x).  intro. subst. apply H. apply AI. 
          assert (appears_in x0 l2).  apply INC. right. assumption.
          rewrite EQ in H1. apply appears_in_app in H1. apply app_appears_in. 
            inversion H1. 
              left. assumption.
              inversion H2; subst. 
                 apply ex_falso_quodlibet.  apply H0. reflexivity. 
                 right.  assumption.
         assert (length l2 = S(length (l2a ++ l2b))).
            rewrite EQ.  
            rewrite app_length. rewrite app_length. rewrite plus_comm. 
            simpl. rewrite plus_comm. reflexivity.
        rewrite H0 in NR. simpl in NR. 
        apply Sn_le_Sm__n_le_m.  apply NR.  Qed. 
(** [] *)

(* $Date: 2013-02-10 18:08:54 -0500 (Dom, 10 Feb 2013) $ *)

