(** * StlcProp: Properties of STLC *)

Require Export Stlc.

Module STLCProp.
Import STLC.

(** In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus -- in particular, the type safety
    theorem. *)

(* ###################################################################### *)
(** * Progress *)

(** As before, the _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take an evaluation step.  The proof is a relatively
    straightforward extension of the progress proof we saw in the
    [Types] chapter. *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

(** _Proof_: by induction on the derivation of [|- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we know immediately that [t] is a value.

    - If the last rule of the derivation was [T_App], then [t = t1
      t2], and we know that [t1] and [t2] are also well typed in the
      empty context; in particular, there exists a type [T2] such that
      [|- t1 \in T2 -> T] and [|- t2 \in T2].  By the induction
      hypothesis, either [t1] is a value or it can take an evaluation
      step.

        - If [t1] is a value, we now consider [t2], which by the other
          induction hypothesis must also either be a value or take an
          evaluation step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation was [T_If], then [t = if t1
      then t2 else t3], where [t1] has type [Bool].  By the IH, [t1]
      either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps
          to [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]).
*)

Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an 
       empty context *)
    inversion H. 

  Case "T_App". 
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a 
       value or steps... *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is also a value".
        (* Since [t1] is a value and has an arrow type, it
           must be an abs. Sometimes this is proved separately 
           and called a "canonical forms" lemma. *) 
        inversion H; subst. exists ([x0:=t2]t)...
        solve by inversion. solve by inversion. 
      SSCase "t2 steps".
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_If".
    right. destruct IHHt1...
    
    SCase "t1 is a value".
      (* Since [t1] is a value of boolean type, it must
         be true or false *)
      inversion H; subst. solve by inversion.
      SSCase "t1 = true". eauto.
      SSCase "t1 = false". eauto.

    SCase "t1 also steps".
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
Qed.

(** **** Exercise: 3 stars, optional (progress_from_term_ind) *)
(** Show that progress can also be proved by induction on terms
    instead of induction on typing derivations. *)

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof.
  intros t.
  t_cases (induction t) Case; intros T Ht; auto.
  (* SOLUTION: *)
  Case "tvar".
    inversion Ht. subst. inversion H1.
  Case "tapp".
    right.
    inversion Ht; clear Ht; subst.
    assert (value t1 \/ (exists t' : tm, t1 ==> t')) by eauto. clear IHt1.
    assert (value t2 \/ (exists t' : tm, t2 ==> t')) by eauto. clear IHt2.
    inversion H.
      SCase "t1 is a value".
        inversion H0. 
        SSCase "... and t2 is a value". inversion H1. 
          eauto. 
          subst. solve by inversion.
          subst. solve by inversion.
        SSCase "... and t2 can step". inversion H3. eauto.
      SCase "t1 can step".
        inversion H1. eauto.
  Case "tif".
    right. 
    inversion Ht; clear Ht; subst. 
    assert (value t1 \/ (exists t' : tm, t1 ==> t')) by eauto. clear IHt1.
    inversion H; clear H.
      SCase "t1 is a value".
        inversion H0; clear H0; subst. 
        solve by inversion. eauto. eauto.
      SCase "t1 can step".
        inversion H0. eauto.
Qed.
(** [] *)

(* ###################################################################### *)
(** * Preservation *)

(** The other half of the type soundness property is the preservation
    of types during reduction.  For this, we need to develop some
    technical machinery for reasoning about variables and
    substitution.  Working from top to bottom (the high-level property
    we are actually interested in to the lowest-level technical lemmas
    that are needed by various cases of the more interesting proofs),
    the story goes like this:

      - The _preservation theorem_ is proved by induction on a typing
        derivation, pretty much as we did in the [Types] chapter.  The
        one case that is significantly different is the one for the
        [ST_AppAbs] rule, which is defined using the substitution
        operation.  To see that this step preserves typing, we need to
        know that the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed)
        term [s] for a variable [x] in a term [t] preserves the type
        of [t].  The proof goes by induction on the form of [t] and
        requires looking at all the different cases in the definition
        of substitition.  This time, the tricky cases are the ones for
        variables and for function abstractions.  In both cases, we
        discover that we need to take a term [s] that has been shown
        to be well-typed in some context [Gamma] and consider the same
        term [s] in a slightly different context [Gamma'].  For this
        we prove a...

      - _context invariance_ lemma, showing that typing is preserved
        under "inessential changes" to the context [Gamma] -- in
        particular, changes that do not affect any of the free
        variables of the term.  For this, we need a careful definition
        of

      - the _free variables_ of a term -- i.e., the variables occuring
        in the term that are not in the scope of a function
        abstraction that binds them.
*)

(* ###################################################################### *)
(** ** Free Occurrences *)

(** A variable [x] _appears free in_ a term _t_ if [t] contains some
    occurrence of [x] that is not under an abstraction labeled [x].  For example: 
      - [y] appears free, but [x] does not, in [\x:T->U. x y] 
      - both [x] and [y] appear free in [(\x:T->U. x y) x] 
      - no variables appear free in [\x:T->U. \y:T. x y]  *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" 
  | Case_aux c "afi_abs" 
  | Case_aux c "afi_if1" | Case_aux c "afi_if2" 
  | Case_aux c "afi_if3" ].

Hint Constructors appears_free_in.

(** A term in which no variables appear free is said to be _closed_. *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(* ###################################################################### *)
(** ** Substitution *)

(** We first need a technical lemma connecting free variables and
    typing contexts.  If a variable [x] appears free in a term [t],
    and if we know [t] is well typed in context [Gamma], then it must
    be the case that [Gamma] assigns a type to [x]. *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.

(** _Proof_: We show, by induction on the proof that [x] appears free
      in [t], that, for all contexts [Gamma], if [t] is well typed
      under [Gamma], then [Gamma] assigns some type to [x].

      - If the last rule used was [afi_var], then [t = x], and from
        the assumption that [t] is well typed under [Gamma] we have
        immediately that [Gamma] assigns a type to [x].

      - If the last rule used was [afi_app1], then [t = t1 t2] and [x]
        appears free in [t1].  Since [t] is well typed under [Gamma],
        we can see from the typing rules that [t1] must also be, and
        the IH then tells us that [Gamma] assigns [x] a type.

      - Almost all the other cases are similar: [x] appears free in a
        subterm of [t], and since [t] is well typed under [Gamma], we
        know the subterm of [t] in which [x] appears is well typed
        under [Gamma] as well, and the IH gives us exactly the
        conclusion we want.

      - The only remaining case is [afi_abs].  In this case [t =
        \y:T11.t12], and [x] appears free in [t12]; we also know that
        [x] is different from [y].  The difference from the previous
        cases is that whereas [t] is well typed under [Gamma], its
        body [t12] is well typed under [(Gamma, y:T11)], so the IH
        allows us to conclude that [x] is assigned some type by the
        extended context [(Gamma, y:T11)].  To conclude that [Gamma]
        assigns a type to [x], we appeal to lemma [extend_neq], noting
        that [x] and [y] are different variables. *)

Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    apply not_eq_beq_id_false in H. 
    rewrite extend_neq in H7; assumption.
Qed.

(** Next, we'll need the fact that any term [t] which is well typed in
    the empty context is closed -- that is, it has no free variables. *)

(** **** Exercise: 2 stars, optional (typable_empty__closed) *)
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
Proof.
  (* SOLUTION: *)
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' Hc].
  inversion Hc.  Qed.
(** [] *)

(** Sometimes, when we have a proof [Gamma |- t : T], we will need to
    replace [Gamma] by a different context [Gamma'].  When is it safe
    to do this?  Intuitively, it must at least be the case that
    [Gamma'] assigns the same types as [Gamma] to all the variables
    that appear free in [t]. In fact, this is the only condition that
    is needed. *)

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.

(** _Proof_: By induction on the derivation of [Gamma |- t \in T].

      - If the last rule in the derivation was [T_Var], then [t = x]
        and [Gamma x = T].  By assumption, [Gamma' x = T] as well, and
        hence [Gamma' |- t \in T] by [T_Var].

      - If the last rule was [T_Abs], then [t = \y:T11. t12], with [T
        = T11 -> T12] and [Gamma, y:T11 |- t12 \in T12].  The induction
        hypothesis is that for any context [Gamma''], if [Gamma,
        y:T11] and [Gamma''] assign the same types to all the free
        variables in [t12], then [t12] has type [T12] under [Gamma''].
        Let [Gamma'] be a context which agrees with [Gamma] on the
        free variables in [t]; we must show [Gamma' |- \y:T11. t12 \in
        T11 -> T12].

        By [T_Abs], it suffices to show that [Gamma', y:T11 |- t12 \in
        T12].  By the IH (setting [Gamma'' = Gamma', y:T11]), it
        suffices to show that [Gamma, y:T11] and [Gamma', y:T11] agree
        on all the variables that appear free in [t12].  

        Any variable occurring free in [t12] must either be [y], or
        some other variable.  [Gamma, y:T11] and [Gamma', y:T11]
        clearly agree on [y].  Otherwise, we note that any variable
        other than [y] which occurs free in [t12] also occurs free in
        [t = \y:T11. t12], and by assumption [Gamma] and [Gamma']
        agree on all such variables, and hence so do [Gamma, y:T11]
        and [Gamma', y:T11].

      - If the last rule was [T_App], then [t = t1 t2], with [Gamma |-
        t1 \in T2 -> T] and [Gamma |- t2 \in T2].  One induction
        hypothesis states that for all contexts [Gamma'], if [Gamma']
        agrees with [Gamma] on the free variables in [t1], then [t1]
        has type [T2 -> T] under [Gamma']; there is a similar IH for
        [t2].  We must show that [t1 t2] also has type [T] under
        [Gamma'], given the assumption that [Gamma'] agrees with
        [Gamma] on all the free variables in [t1 t2].  By [T_App], it
        suffices to show that [t1] and [t2] each have the same type
        under [Gamma'] as under [Gamma].  However, we note that all
        free variables in [t1] are also free in [t1 t2], and similarly
        for free variables in [t2]; hence the desired result follows
        by the two IHs.
*)

Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros; auto.
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. remember (beq_id x0 x1) as e. destruct e...
  Case "T_App".
    apply T_App with T11...  
Qed.

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types.

    Formally, the so-called _Substitution Lemma_ says this: suppose we
    have a term [t] with a free variable [x], and suppose we've been
    able to assign a type [T] to [t] under the assumption that [x] has
    some type [U].  Also, suppose that we have some other term [v] and
    that we've shown that [v] has type [U].  Then, since [v] satisfies
    the assumption we made about [x] when typing [t], we should be
    able to substitute [v] for each of the occurrences of [x] in [t]
    and obtain a new term that still has type [T]. *)

(** _Lemma_: If [Gamma,x:U |- t \in T] and [|- v \in U], then [Gamma |-
    [x:=v]t \in T]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.

(** One technical subtlety in the statement of the lemma is that we
    assign [v] the type [U] in the _empty_ context -- in other words,
    we assume [v] is closed.  This assumption considerably simplifies
    the [T_Abs] case of the proof (compared to assuming [Gamma |- v \in
    U], which would be the other reasonable assumption at this point)
    because the context invariance lemma then tells us that [v] has
    type [U] in any context at all -- we don't have to worry about
    free variables in [v] clashing with the variable being introduced
    into the context by [T_Abs].

    _Proof_: We prove, by induction on [t], that, for all [T] and
    [Gamma], if [Gamma,x:U |- t \in T] and [|- v \in U], then [Gamma |-
    [x:=v]t \in T].
 
      - If [t] is a variable, there are two cases to consider, depending
        on whether [t] is [x] or some other variable.

          - If [t = x], then from the fact that [Gamma, x:U |- x \in T] we
            conclude that [U = T].  We must show that [[x:=v]x = v] has
            type [T] under [Gamma], given the assumption that [v] has
            type [U = T] under the empty context.  This follows from
            context invariance: if a closed term has type [T] in the
            empty context, it has that type in any context.

          - If [t] is some variable [y] that is not equal to [x], then
            we need only note that [y] has the same type under [Gamma,
            x:U] as under [Gamma].

      - If [t] is an abstraction [\y:T11. t12], then the IH tells us,
        for all [Gamma'] and [T'], that if [Gamma',x:U |- t12 \in T']
        and [|- v \in U], then [Gamma' |- [x:=v]t12 \in T'].

        The substitution in the conclusion behaves differently,
        depending on whether [x] and [y] are the same variable name.

        First, suppose [x = y].  Then, by the definition of
        substitution, [[x:=v]t = t], so we just need to show [Gamma |-
        t \in T].  But we know [Gamma,x:U |- t : T], and since the
        variable [y] does not appear free in [\y:T11. t12], the
        context invariance lemma yields [Gamma |- t \in T].

        Second, suppose [x <> y].  We know [Gamma,x:U,y:T11 |- t12 \in
        T12] by inversion of the typing relation, and [Gamma,y:T11,x:U
        |- t12 \in T12] follows from this by the context invariance
        lemma, so the IH applies, giving us [Gamma,y:T11 |- [x:=v]t12 \in
        T12].  By [T_Abs], [Gamma |- \y:T11. [x:=v]t12 \in T11->T12], and
        by the definition of substitution (noting that [x <> y]),
        [Gamma |- \y:T11. [x:=v]t12 \in T11->T12] as required.

      - If [t] is an application [t1 t2], the result follows
        straightforwardly from the definition of substitution and the
        induction hypotheses.

      - The remaining cases are similar to the application case.

    Another technical note: This proof is a rare case where an
    induction on terms, rather than typing derivations, yields a
    simpler argument.  The reason for this is that the assumption
    [extend Gamma x U |- t \in T] is not completely generic, in
    the sense that one of the "slots" in the typing relation -- namely
    the context -- is not just a variable, and this means that Coq's
    native induction tactic does not give us the induction hypothesis
    that we want.  It is possible to work around this, but the needed
    generalization is a little tricky.  The term [t], on the other
    hand, _is_ completely generic. *)

Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T. 
  t_cases (induction t) Case; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. remember (beq_id x y) as e. destruct e.
    SCase "x=y".
      apply beq_id_eq in Heqe. subst.
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
      eapply context_invariance...
      apply beq_id_eq in Heqe. subst.
      intros x Hafi. unfold extend.
      destruct (beq_id y x)...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...  
Qed.

(** The substitution lemma can be viewed as a kind of "commutation"
    property.  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [x:=v] t ] -- the result is the same either
    way. *)

(* ###################################################################### *)
(** ** Main Theorem *)

(** We now have the tools we need to prove preservation: if a closed
    term [t] has type [T], and takes an evaluation step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    evaluation relation preserves types.
*)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.

(** _Proof_: by induction on the derivation of [|- t \in T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as the final rules in the derivation, since in each of
      these cases [t] cannot take a step.

    - If the last rule in the derivation was [T_App], then [t = t1
      t2].  There are three cases to consider, one for each rule that
      could have been used to show that [t1 t2] takes a step to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then by the IH [t1'] has the same type as [t1], and
          hence [t1' t2] has the same type as [t1 t2].

        - The [ST_App2] case is similar.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T11.t12] and [t1 t2] steps to [[x:=t2]t12]; the
          desired result now follows from the fact that substitution
          preserves types.

    - If the last rule in the derivation was [T_If], then [t = if t1
      then t2 else t3], and there are again three cases depending on
      how [t] steps.

        - If [t] steps to [t2] or [t3], the result is immediate, since
          [t2] and [t3] have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired conclusion
          follows directly from the induction hypothesis.
*)

Proof with eauto.
  remember (@empty ty) as Gamma. 
  intros t t' T HT. generalize dependent t'.   
  has_type_cases (induction HT) Case;
       intros t' HE; subst Gamma; subst; 
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and [eauto] takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...  
Qed.

(** **** Exercise: 2 stars (subject_expansion_stlc) *)
(** An exercise in the [Types] chapter asked about the subject
    expansion property for the simple language of arithmetic and
    boolean expressions.  Does this property hold for STLC?  That is,
    is it always the case that, if [t ==> t'] and [has_type t' T],
    then [empty |- t \in T]?  If so, prove it.  If not, give a
    counter-example not involving conditionals.

(* SOLUTION: *) 
    Subject expansion does not hold in STLC either.  For example,
    [((\a:Bool->Bool. \y:Bool. y) true)] is ill typed, but it evaluates
    to the well-typed term [\y:Bool. y].
[]
*)


(* ###################################################################### *)
(** * Type Soundness *)

(** **** Exercise: 2 stars, optional (type_soundness) *)

(** Put progress and preservation together and show that a well-typed
    term can _never_ reach a stuck state.  *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  (* SOLUTION: *)
  Case "multi_refl".
    apply progress in Hhas_type.
    inversion Hhas_type; auto.
  Case "multi_step".
    eapply preservation in Hhas_type.
      apply IHHmulti; try eassumption.
      assumption. Qed.

(* ###################################################################### *)
(** * Uniqueness of Types *)

(** **** Exercise: 3 stars (types_unique) *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)
(** Formalize this statement and prove it. *)

(* SOLUTION: *)
Theorem unique_types : forall Gamma e T T',
  Gamma |- e \in T ->
  Gamma |- e \in T' ->
  T = T'.
Proof.
  intros Gamma e T T' Htyp. generalize dependent T'.
  has_type_cases (induction Htyp) Case; intros T' Htyp';
    inversion Htyp'; subst; auto.
  Case "T_Var".
    rewrite H in H2. inversion H2. reflexivity.
  Case "T_Abs".
    apply IHHtyp in H4. subst. reflexivity.
  Case "T_App".
    apply IHHtyp1 in H2. inversion H2. reflexivity.
Qed.
(** [] *)

(* ###################################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 1 star (progress_preservation_statement) *)
(** Without peeking, write down the progress and preservation
    theorems for the simply typed lambda-calculus. *)
(** [] *)


(** **** Exercise: 2 stars (stlc_variation1) *)
(** Suppose we add a new term [zap] with the following reduction rule:
                         ---------                  (ST_Zap)
                         t ==> zap
and the following typing rule:
                      ----------------               (T_Zap)
                      Gamma |- zap : T
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

        - Becomes false. For instance [(if true then false else true) ==> false]
          and [(if true then false else true) ==> zap].
      - Progress

        - Remains true. [zap] can have any type.
      - Preservation

        - Remains true. Every term (including [zap]) can take a step to [zap].
[]
*)

(** **** Exercise: 2 stars (stlc_variation2) *)
(** Suppose instead that we add a new term [foo] with the following reduction rules:
                       -----------------                (ST_Foo1)
                       (\x:A. x) ==> foo 

                         ------------                   (ST_Foo2)
                         foo ==> true
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

        - Remains true. [(\x:A. x)] didn't reduce before and now
          reduces in just one way (this breaks the "values are normal
          forms" property, but it doesn't break determinism.
      - Progress

        - Remains true. We are only adding to the step relation, and
          this can never damage progress.
      - Preservation

        - Becomes false. For example,
          [|- \x:Bool.x \in Bool->Bool] and [(\x:Bool.x) ==> foo] by (ST_Foo1),
          but, since we have no typing rules for foo, we cannot prove that
          [|- foo \in Bool->Bool].
[]
*)

(** **** Exercise: 2 stars (stlc_variation3) *)
(** Suppose instead that we remove the rule [ST_App1] from the [step]
    relation. Which of the following properties of the STLC remain
    true in the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

        - Remains true. Removing reduction rules can only make [step]
          more deterministic.
      - Progress

        - Becomes false. For example,
          [((\x:Bool->Bool. \y:Bool->Bool. x) (\z:Bool.z)) (\z:Bool.z)] 
          is well typed, but stuck.
      - Preservation

        - Remains true. Removing reduction rules can't break preservation.
[]
*)

(** **** Exercise: 2 stars, optional (stlc_variation4) *)
(** Suppose instead that we add the following new rule to the reduction relation:
            ----------------------------------        (ST_FunnyIfTrue)
            (if true then t1 else t2) ==> true
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

        - Becomes false, for instance:
          [(if true then false else false) ==> false] and
          [(if true then false else false) ==> true]
      - Progress

        - Remains true. We are only adding to the step relation, and
          this can never damage progress.
      - Preservation

        - Becomes false. For example,
          [|- if true then (\x:Bool.x) else (\x:Bool.x) \in Bool->Bool]
          and [(if true then (\x:Bool.x) else (\x:Bool.x)) ==> true]
          but it's not the case that [|- true \in Bool -> Bool].
*)

(** **** Exercise: 2 stars, optional (stlc_variation5) *)
(** Suppose instead that we add the following new rule to the typing relation:
                 Gamma |- t1 \in Bool->Bool->Bool
                     Gamma |- t2 \in Bool
                 ------------------------------          (T_FunnyApp)
                    Gamma |- t1 t2 \in Bool
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

        - Remains true. We are only adding to the typing relation, and
          this can never damage determinism of [step].
      - Progress

        - Remains true. Since the new rule still requires that [t1] is
          a function we can still apply ST_AppAbs to show progress.
      - Preservation

        - Becomes false. For example,
          [|- \x:Bool. \y:Bool. x true \in Bool]
          and [(\x:Bool. \y:Bool. x) true ==> \y:Bool. true]
          but it's not the case that [|- \y:Bool. true \in Bool]
*)

(** **** Exercise: 2 stars, optional (stlc_variation6) *)
(** Suppose instead that we add the following new rule to the typing relation:
                     Gamma |- t1 \in Bool
                     Gamma |- t2 \in Bool
                    ---------------------               (T_FunnyApp')
                    Gamma |- t1 t2 \in Bool
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

        - Remains true. We are not changing the [step] relation.
      - Progress

        - Becomes false. For instance, [true true] is a term that
          becomes typable (at type [Bool]), but which is stuck.
      - Preservation

        - Remains true. There are 3 ways [t1 t2] can reduce. For
          [ST_App1] and [ST_App2] we can still apply the induction
          hypothesis. In order to reduce [t1 t2] using [ST_AppAbs]
          [t1] would need to be a function, but functions don't have
          type [Bool].
*)

(** **** Exercise: 2 stars, optional (stlc_variation7) *)
(** Suppose we add the following new rule to the typing
    relation of the STLC:
                         ------------------- (T_FunnyAbs)
                         |- \x:Bool.t \in Bool
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

        - Remains true. We're not changing the [step] relation.
      - Progress

        - Becomes false. For instance [if (\x:Bool.false) then false
          else false] is a term that would become typable, although it
          is stuck.
      - Preservation

        - Remains true. [\x:Bool.t] doesn't step.
[]
*)

End STLCProp.

(* ###################################################################### *)
(* ###################################################################### *)
(** ** Exercise: STLC with Arithmetic *) 

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.

(** To types, we add a base type of natural numbers (and remove
    booleans, for brevity) *)

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat   : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing... *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tnat  : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "tnat" 
  | Case_aux c "tsucc" | Case_aux c "tpred"
  | Case_aux c "tmult" | Case_aux c "tif0" ].

(** **** Exercise: 4 stars (stlc_arith) *)
(** Finish formalizing the definition and properties of the STLC extended
    with arithmetic.  Specifically:

    - Copy the whole development of STLC that we went through above (from
      the definition of values through the Progress theorem), and
      paste it into the file at this point.

    - Extend the definitions of the [subst] operation and the [step]
      relation to include appropriate clauses for the arithmetic operators.

    - Extend the proofs of all the properties (up to [soundness]) of
      the original STLC to deal with the new syntactic forms.  Make
      sure Coq accepts the whole file. *)

(* SOLUTION: *)

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y => 
      if beq_id x y then s else t
  | tabs y T t1 => 
      tabs y T (if beq_id x y then t1 else (subst x s t1))
  | tapp t1 t2 => 
      tapp (subst x s t1) (subst x s t2)
  (* nothing special... *)
  | tnat n => 
      tnat n
  | tsucc t1 => 
      tsucc (subst x s t1)
  | tpred t1 => 
      tpred (subst x s t1)
  | tmult t1 t2 => 
      tmult (subst x s t1) (subst x s t2)
  | tif0 t1 t2 t3 => 
      tif0 (subst x s t1) (subst x s t2) (subst x s t3)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  (* numbers are values *)
  | v_nat : forall n,
      value (tnat n).

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1 t2')
  | ST_Succ : forall t t',
         t ==> t' ->
         (tsucc t) ==> (tsucc t')
  | ST_SuccNat : forall n,
         (tsucc (tnat n)) ==> (tnat (S n))
  | ST_Pred : forall t t',
         t ==> t' ->
         (tpred t) ==> (tpred t')
  | ST_PredNat : forall n,
         (tpred (tnat n)) ==> (tnat (pred n))
  | ST_MultNats : forall n1 n2,
         (tmult (tnat n1) (tnat n2)) ==> (tnat (mult n1 n2))
  | ST_Mult1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tmult t1 t2) ==> (tmult t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tmult v1 t2) ==> (tmult v1 t2')
  | ST_If0 : forall t1 t1' t2 t3,
         t1 ==> t1' ->
         (tif0 t1 t2 t3) ==> (tif0 t1' t2 t3)
  | ST_If0_Zero : forall t2 t3,
         (tif0 (tnat 0) t2 t3) ==> t2
  | ST_If0_Nonzero : forall n t2 t3,
         (tif0 (tnat (S n)) t2 t3) ==> t3

where "t1 '==>' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

(* ########################################### *)
(* Evaluation example: *)

(* FIX : something to replace fact *)

(* ########################################### *)

(* Typing *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall Gamma t1 T1 T2 t2,
      Gamma |- t1 \in TArrow T1 T2 -> 
      Gamma |- t2 \in T1 -> 
      Gamma |- tapp t1 t2 \in T2
  (* typing rules for arithmetic expressions *)
  | T_Nat : forall Gamma n,
      Gamma |- tnat n \in TNat
  | T_Succ : forall Gamma t1,
      Gamma |- t1 \in TNat ->
      Gamma |- tsucc t1 \in TNat
  | T_Pred : forall Gamma t1,
      Gamma |- t1 \in TNat ->
      Gamma |- tpred t1 \in TNat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in TNat ->
      Gamma |- t2 \in TNat ->
      Gamma |- tmult t1 t2 \in TNat
  | T_If0 : forall Gamma t1 t2 t3 T,
      Gamma |- t1 \in TNat ->
      Gamma |- t2 \in T ->
      Gamma |- t3 \in T ->
      Gamma |- tif0 t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Nat" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Mult" | Case_aux c "T_If0" ].

Hint Constructors has_type.

(* ########################################### *)
(* Free variables *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (tabs y T11 t12)
  (* free variables for arithmetic expressions *)
  | afi_succ : forall x t1,
        appears_free_in x t1 ->
        appears_free_in x (tsucc t1)
  | afi_pred : forall x t1,
        appears_free_in x t1 ->
        appears_free_in x (tpred t1)
  | afi_mult1 : forall x t1 t2,
        appears_free_in x t1 ->
        appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
        appears_free_in x t2 ->
        appears_free_in x (tmult t1 t2)
  | afi_if01 : forall x t1 t2 t3,
        appears_free_in x t1 ->
        appears_free_in x (tif0 t1 t2 t3)
  | afi_if02 : forall x t1 t2 t3,
        appears_free_in x t2 ->
        appears_free_in x (tif0 t1 t2 t3)
  | afi_if03 : forall x t1 t2 t3,
        appears_free_in x t3 ->
        appears_free_in x (tif0 t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" | Case_aux c "afi_abs"
  | Case_aux c "afi_succ" | Case_aux c "afi_pred"
  | Case_aux c "afi_mult1" | Case_aux c "afi_mult2"
  | Case_aux c "afi_if01" | Case_aux c "afi_if02" | Case_aux c "afi_if03" ].

Hint Constructors appears_free_in.

(* ########################################### *)
(* Substitution *)

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'. 
  has_type_cases (induction H) Case; intros Gamma' Heqv; auto.
  Case "T_Var".
    apply T_Var. rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs. apply IHhas_type. intros x0 Hafi.
    (* tricky step... the Gamma' we use to instantiate is 
       [extend ty Gamma x T1] *)
    unfold extend. remember (beq_id x x0) as e.
    destruct e...
  Case "T_App".
    apply T_App with T1...
  Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi. 
  generalize dependent Gamma. generalize dependent T.
  afi_cases (induction Hafi) Case; intros T Gamma Htyp;
    inversion Htyp; subst...
  Case "afi_abs".
    destruct (IHHafi _ _ H5) as [T Hctx]. exists T.
    unfold extend in Hctx.
    apply not_eq_beq_id_false in H. rewrite H in Hctx.
    assumption.  Qed.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     extend Gamma x U |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in S.
Proof with eauto.
  intros Gamma x U v t S Ht Hv. 
  generalize dependent Gamma.  generalize dependent S. 
  t_cases (induction t) Case; intros S Gamma H;
    simpl; inversion H; subst...
  Case "tvar".
    rename i into y. remember (beq_id x y) as e. destruct e.
    SCase "x=y".
      apply beq_id_eq in Heqe. subst. unfold extend in H2.
      rewrite <- beq_id_refl in H2. inversion H2; subst. clear H2.
      eapply context_invariance. apply Hv.
      intros x Hcontra.
      destruct (free_in_context _ _ _ _ Hcontra Hv) as [T Hctx].
      inversion Hctx.
    SCase "x<>y".
      unfold extend in H2. rewrite <- Heqe in H2...
  Case "tabs".
    apply T_Abs. rename i into y.
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
      apply beq_id_eq in Heqe. subst.
      eapply context_invariance. apply H5.
      intros. unfold extend.
      destruct (beq_id y x); reflexivity.
    SCase "x<>y".
      apply IHt. eapply context_invariance. apply H5.
      intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...  Qed.

(* ############################################ *)
(* Preservation *)

Theorem preservation : forall t t' T,
  empty |- t \in T  ->
  t ==> t'  ->
  empty |- t' \in T.
Proof with eauto.
  remember (@empty ty) as Gamma. 
  intros t t' T HT. generalize dependent t'.   
  has_type_cases (induction HT) Case; intros t' HE; subst;
    inversion HE; subst...
  Case "T_App".
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T1...
      inversion HT1...  
Qed.

(* ############################################### *)
(* Progress *)

Theorem progress : forall t T, 
  empty |- t \in T ->
  value t \/ exists t', t ==> t'. 
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    inversion H. 
  Case "T_App".
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t1 is a value".
        (* since t1 is a value and has an arrow type, 
           it must be an abs *)
        inversion H; subst...
        (* and therefore can't be a nat *)
        inversion Ht1.
      SSCase "t2 steps".
        inversion H0 as [t2' Hstp].
        exists (tapp t1 t2')...
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tapp t1' t2)...
  Case "T_Succ".
    right. destruct IHHt...
    SCase "t is a value".
      inversion H; subst. inversion Ht. exists (tnat (S n))...
    SCase "t steps".
      inversion H as [t' Hstp]. exists (tsucc t')...
  Case "T_Pred".
    right. destruct IHHt...
    SCase "t is a value".
      inversion H; subst. inversion Ht. exists (tnat (pred n))...
    SCase "t steps".
      inversion H as [t' Hstp]. exists (tpred t')...
  Case "T_Mult".
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is a value".
        inversion H; subst. inversion Ht1. 
        inversion H0; subst. inversion Ht2.
        exists (tnat (mult n n0))...
      SSCase "t2 steps".
        inversion H0 as [t' Hstp]. exists (tmult t1 t')...
    SCase "t1 steps".
      inversion H as [t' Hstp]. exists (tmult t' t2)...
  Case "T_If0".
    right. destruct IHHt1...
    SCase "t1 is a value".

      inversion H; subst. inversion Ht1. destruct n as [|n'].
      SSCase "n = 0". exists t2...
      SSCase "n = S n'". exists t3...
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tif0 t1' t2 t3)...  Qed.

(** [] *)

End STLCArith.

(* $Date$ *)

