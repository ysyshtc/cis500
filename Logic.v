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
  (* FILL IN HERE *) Admitted.
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
  split.
  Case "P /\ Q".
    split.
    SCase "P". apply HP.
    SCase "Q". apply HQ.
  Case "R". apply HR.
Qed.
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
  intros n.
  induction n as [|n'].
  Case "0".
    split.
    SCase "left". intros. apply ev_0.
    SCase "right".
      intros H.
      unfold even in H.
      simpl in H.
      inversion H.
  Case "n+1".
    inversion IHn' as [IHl IHr].
    split.
    SCase "left". apply IHr.
    SCase "right". 
      intros H.
      apply ev_SS.
      apply IHl.
      unfold even.
      unfold even in H. simpl in H.
      apply H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (conj_fact) *)
(** Construct a proof object demonstrating the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  (* FILL IN HERE *) admit.
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
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.

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
  (* FILL IN HERE *) admit.
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

(* FILL IN HERE *)
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
  intros P Q R H.
  inversion H as [[HP1 | HQ] [HP2 | HR]].
  Case "left-left". left. apply HP1.
  Case "left-right". left. apply HP1.
  Case "right-left". left. apply HP2.
  Case "right-right".
    right.
    split.
    SCase "left". apply HQ.
    SCase "left". apply HR.
Qed.
  (** [] *)

(** **** Exercise: 1 star, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *) Admitted.
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
  (* FILL IN HERE *) Admitted.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  (* FILL IN HERE *) Admitted.
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

(* FILL IN HERE *)
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
(* FILL IN HERE *)
   []
*)

(** **** Exercise: 2 stars (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H HQ HP.
  apply H in HP.
  apply HQ in HP.
  inversion HP.
Qed.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  intros P H.
  apply contradiction_implies_anything with (Q:=False) in H.
  apply H.
Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)
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
  Case "0".
    intros H1.
    inversion H1.
  Case "SSn".
    intros Hn.
    inversion Hn.
    apply IHev in H1.
    apply H1.
Qed.
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

(* FILL IN HERE *)
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
Theorem not_eq_beq_false : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof. Admitted.
(* See below for many attempts at this. *)
(*  intros n m.
  unfold not in H.
  destruct (beq_nat n m ).
  Case "true". apply ex_falso_quodlibet. apply H.
  unfold beq_nat.*)
(*  
  induction n as [|n'].
  Case "0".
    intros m H.
    induction m as [|m'].
    SCase "0". 
      simpl. apply ex_falso_quodlibet. apply H. reflexivity.
    SCase "m'".  reflexivity.
  Case "n'".
    intros m.
    destruct m as [|m'].
    SCase "0". reflexivity.
    SCase "m'". 
      simpl.
      intros H.
      destruct n'.
      apply IHn'.
      inversion H.
      unfold not.
      unfold not in H.
      apply IHn'.
      unfold not.
      unfold not in H.
      
      simpl. apply IHn'.d
      inversion H.
      apply IHm'.
      apply ex_falso_quodlibet.
      apply H.
      apply H.
      unfold not in IHn'.
      unfold not in IHm'.
      apply IHn' in IHm'.


  unfold not in H.
  induction n as [|n'].
  Case "n = 0".
    destruct m as [|m'].
    SCase "m = 0".
      simpl.
      apply ex_falso_quodlibet.
      apply H.
      reflexivity.
    SCase "m = S m'". reflexivity.
  Case "n = S n'".
    induction m as [|m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. destruct (beq_nat n' m'). apply ex_falso_quodlibet.
 
  remember (beq_nat n m).
  unfold not in H.
  destruct b.
  apply ex_falso_quodlibet.
  apply H.
  induction n as [|n'].
    inversion in Heqb.
  unfold not in H.
  apply H.
  inversion b.
(*  unfold not in H.
  destruct (beq_nat n m).
  apply ex_falso_quodlibet.
  apply H.*)
  unfold not in H.
  destruct n as [|n'].
  Case "n=0".
    destruct m as [|m'].
    SCase "m=0".
      simpl.
      apply ex_falso_quodlibet.
      apply H.
      reflexivity.
    SCase "S m'". simpl. reflexivity.
  Case "S n'".
    destruct m as [|m'].
    SCase "m=0". reflexivity.
    SCase "S m'".
      unfold beq_nat.
      inversion H.
*)
(* TODO *)
(** [] *)

(** **** Exercise: 2 stars, optional (beq_false_not_eq) *)
Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  intros n m H1 H2.
  (* FILL IN HERE *) Admitted.
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

(* FILL IN HERE *)

(** Complete the definition of the following proof object: *)

Definition p : ex nat (fun n => beautiful (S n)) :=
(* FILL IN HERE *) admit.
(** [] *)

(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" and "there is no [x] for
    which [P] does not hold" are equivalent assertions. *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  intros X P H1 H2.
  inversion H2 as [w Hw].
  apply Hw in H1.
  apply H1.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  Case "->".
    intros H.
    inversion H as [w [HP | HQ]].
    SCase "left".
      left.
      exists w.
      apply HP.
    SCase "right".
      right.
      exists w.
      apply HQ.
  Case "<-".
    intros H.
    inversion H as [[p HP] | [q HQ]].
    SCase "left".
      exists p.
      left.
      apply HP.
    SCase "right".
      exists q.
      right.
      apply HQ.
Qed.
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
  intros X x y H P H3.
  inversion H.
  rewrite <- H1.
  apply H3.
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
(* FILL IN HERE *) Admitted.
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

Inductive total_relation : nat -> nat -> Prop :=
  alln : forall (n m:nat), total_relation n n.

(** [] *)

(** **** Exercise: 2 stars (empty_relation) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)
Inductive empty_relation : nat -> nat -> Prop :=. 
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

[R 1 1 2] is provable: c2 <- c3 <- c1
[R 2 2 6] is *not* provable

The set of provable propositions *wouldn't* change if we dropped [c5],
becuase [c5] is the identity - it doesn't chance the proposition it's
given and so we can't do anything with it.

It also wouldn't change to drop [c4], since that just recreates things we could've already done with [c1, c2].
[]
*)

(** **** Exercise: 3 stars, optional (R_fact) *)  
(** State and prove an equivalent characterization of the relation
    [R].  That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

(* FILL IN HERE *)
(** [] *)

End R.

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| all_nil  : all X P []
| all_cons : forall (x:X) (l:list X), (P x) -> (all X P l) -> all X P (x::l).

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

Theorem all_forallb :
  forall (X:Type) (l:list X) (P : X -> Prop) (p : X -> bool),
    (forall x:X, (P x) <-> (p x = true)) ->
    (forallb p l = true <-> all X P l).
Proof. Admitted.
(* Also many attempts *)
(*  intros X l P p H.
  split.
  Case "->".
    intros H1.
    induction l as [|h t].
    SCase "[]". apply all_nil.
    SCase "h::t".
      apply all_cons.
      split 
      simpl in H1.
      apply H.
      rewrite <- H1.
      destruct (p h).
      SSCase "p h = true". simpl.
      SSCase "p h = false".
        inversion H1.
        apply IHt.
        simpl in H1.
*)
(* TODO *)
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

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

(* FILL IN HERE *)
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
  (* FILL IN HERE *) Admitted.

Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

(* FILL IN HERE *)

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises) *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m.  generalize dependent n.  induction m. 
  (* FILL IN HERE *) Admitted. 

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 (* FILL IN HERE *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* Hint: Do the right induction! *)
  (* FILL IN HERE *) Admitted.
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
| ns_nil : nostutter []
| ns_one : forall n, nostutter [n]
| ns_two : forall n m l, n <> m -> nostutter (m::l) -> nostutter (n::m::l).

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
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.


Example test_nostutter_2:  nostutter [].
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_3:  nostutter [5].
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_4:      not (nostutter [3,1,1,4]).
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
  (* FILL IN HERE *) Admitted.

Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
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
  (* FILL IN HERE *) Admitted.
(** [] *)

(* $Date: 2013-02-06 20:50:09 -0500 (Wed, 06 Feb 2013) $ *)

