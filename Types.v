(** * Types: Type Systems *)

Require Export Auto.

(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of a very simple
    language with just booleans and numbers, to introduce the basic
    ideas of types, typing rules, and the fundamental theorems about
    type systems: _type preservation_ and _progress_.  Then we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq). *)

(* ###################################################################### *)
(** * Typed Arithmetic Expressions *)

(** To motivate the discussion of type systems, let's begin as
    usual with an extremely simple toy language.  We want it to have
    the potential for programs "going wrong" because of runtime type
    errors, so we need something a tiny bit more complex than the
    language of constants and addition that we used in chapter
    [Smallstep]: a single kind of data (just numbers) is too simple,
    but just two kinds (numbers and booleans) already gives us enough
    material to tell an interesting story.

    The language definition is completely routine.  The only thing to
    notice is that we are _not_ using the [asnum]/[aslist] trick that
    we used in chapter [HoareList] to make all the operations total by
    forcibly coercing the arguments to [+] (for example) into numbers.
    Instead, we simply let terms get stuck if they try to use an
    operator with the wrong kind of operands: the [step] relation
    doesn't relate them to anything. *)

(* ###################################################################### *)
(** ** Syntax *)

(** Informally:
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
    Formally:
*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

(** _Values_ are [true], [false], and numeric values... *)

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.  
Hint Unfold beq_id beq_nat extend.

(* ###################################################################### *)
(** ** Operational Semantics *)

(** Informally: *)
(**
                    ------------------------------                  (ST_IfTrue)
                    if true then t1 else t2 ==> t1

                   -------------------------------                 (ST_IfFalse)
                   if false then t1 else t2 ==> t2

                              t1 ==> t1'
                      -------------------------                         (ST_If)
                      if t1 then t2 else t3 ==>
                        if t1' then t2 else t3

                              t1 ==> t1'
                         --------------------                         (ST_Succ)
                         succ t1 ==> succ t1'

                             ------------                         (ST_PredZero)
                             pred 0 ==> 0

                           numeric value v1
                        ---------------------                     (ST_PredSucc)
                        pred (succ v1) ==> v1

                              t1 ==> t1'
                         --------------------                         (ST_Pred)
                         pred t1 ==> pred t1'

                          -----------------                     (ST_IszeroZero)
                          iszero 0 ==> true

                           numeric value v1
                      --------------------------                (ST_IszeroSucc)
                      iszero (succ v1) ==> false

                              t1 ==> t1'
                       ------------------------                     (ST_Iszero)
                       iszero t1 ==> iszero t1'
*)

(** Formally: *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" 
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred" 
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.

(** Notice that the [step] relation doesn't care about whether
    expressions make global sense -- it just checks that the operation
    in the _next_ reduction step is being applied to the right kinds
    of operands.  

    For example, the term [succ true] (i.e., [tsucc ttrue] in the
    formal syntax) cannot take a step, but the almost as obviously
    nonsensical term
       succ (if true then true else true) 
    can take a step (once, before becoming stuck). *)

(* ###################################################################### *)
(** ** Normal Forms and Values *)

(** The first interesting thing about the [step] relation in this
    language is that the strong progress theorem from the Smallstep
    chapter fails!  That is, there are terms that are normal
    forms (they can't take a step) but not values (because we have not
    included them in our definition of possible "results of
    evaluation").  Such terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(** **** Exercise: 2 stars (some_term_is_stuck) *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  (* SOLUTION: *)
  exists (tsucc tfalse).
  unfold stuck. split.
    Case "normal form".
      unfold normal_form. intros contra. inversion contra as [t' Hstp].
      solve by inversion 2.
    Case "not a value".
      intros H. solve by inversion 3.  Qed.
(** [] *)

(** However, although values and normal forms are not the same in this
    language, the former set is included in the latter.  This is
    important because it shows we did not accidentally define things
    so that some value could still take a step. *)

(** **** Exercise: 3 stars, advanced (value_is_nf) *)
(** Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* SOLUTION: *)
  intros t H.
  (* Here is the easier way: *)
  unfold normal_form.
  inversion H; clear H.
  Case "boolean value". inversion H0.
    SCase "ttrue". intros Contra. inversion Contra as [t' P]. 
      inversion P.
    SCase "tfalse". intros Contra. inversion Contra as [t' P]. 
      inversion P.
  Case "numeric value".
    induction H0.
    SCase "nv_zero". intros Contra. inversion Contra as [t' P]. 
      inversion P.
    SCase "nv_succ". intros Contra. inversion Contra as [t' P]. 
      inversion P. subst. apply IHnvalue. 
      exists t1'. auto.  Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (step_deterministic) *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  (* SOLUTION: *)
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  step_cases (induction Hy1) Case; 
        intros y2 Hy2; inversion Hy2; subst; auto; 
        try (solve by inversion).
    Case "ST_If".
      SCase "Hy2 by ST_If". f_equal... 
    Case "ST_Succ". 
      SCase "Hy2 by ST_Succ". f_equal... 
    Case "ST_PredSucc".
      SCase "Hy2 by ST_Pred".
        inversion H1; subst. 
        apply ex_falso_quodlibet.
        apply value_is_nf with t1...
    Case "ST_Pred".
      SCase "Hy2 by ST_PredSucc". 
        inversion Hy1; subst.
        apply ex_falso_quodlibet. 
        apply value_is_nf with y2... 
      SCase "Hy2 by ST_Pred". 
        f_equal... 
    Case "ST_IszeroSucc".
      SCase "Hy2 by ST_Iszero". 
        inversion H1; subst.
        apply ex_falso_quodlibet.
        apply value_is_nf with t1...
    Case "ST_Iszero".
      SCase "Hy2 by ST_IszeroSucc". 
        inversion Hy1; subst.
        apply ex_falso_quodlibet. 
        apply value_is_nf with t0...
      SCase "Hy2 by ST_Iszero".
        f_equal... Qed. 
(** [] *)



(* ###################################################################### *)
(** ** Typing *)

(** The next critical observation about this language is that,
    although there are stuck terms, they are all "nonsensical", mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type := 
  | TBool : ty
  | TNat : ty.

(** In informal notation, the typing relation is often written
    [|- t \in T], pronounced "[t] has type [T]."  The [|-] symbol is
    called a "turnstile".  (Below, we're going to see richer typing
    relations where an additional "context" argument is written to the
    left of the turnstile.  Here, the context is always empty.) *)
(** 
                           ----------------                            (T_True)
                           |- true \in Bool

                          -----------------                           (T_False)
                          |- false \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------                (T_If)
                    |- if t1 then t2 else t3 \in T

                             ------------                              (T_Zero)
                             |- 0 \in Nat
                              
                            |- t1 \in Nat
                          ------------------                           (T_Succ)
                          |- succ t1 \in Nat

                            |- t1 \in Nat
                          ------------------                           (T_Pred)
                          |- pred t1 \in Nat

                            |- t1 \in Nat
                        ---------------------                        (T_IsZero)
                        |- iszero t1 \in Bool
*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue \in TBool
  | T_False : 
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero : 
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

(* ###################################################################### *)
(** *** Examples *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not calculate
    the type of the normal form of a term. *)

Example has_type_1 : 
  |- tif tfalse tzero (tsucc tzero) \in TNat.
Proof. 
  apply T_If. 
    apply T_False.
    apply T_Zero.
    apply T_Succ.
      apply T_Zero.  
Qed.

(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

Example has_type_not : 
  ~ (|- tif tfalse tzero ttrue \in TBool).
Proof.
  intros Contra. solve by inversion 2.  Qed.

(** **** Exercise: 1 star, optional (succ_hastype_nat__hastype_nat) *)
Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.  
Proof.
  (* SOLUTION: *)
  intros t H. inversion H. subst. assumption.  Qed.
(** [] *)

(* ###################################################################### *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

(** **** Exercise: 3 stars (finish_progress) *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)

Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value". inversion H; clear H.
      SSCase "t1 is a bvalue". inversion H0; clear H0.
        SSSCase "t1 is ttrue".
          exists t2...
        SSSCase "t1 is tfalse". 
          exists t3...
      SSCase "t1 is an nvalue".
        solve by inversion 2.  (* on H and HT1 *)
    SCase "t1 can take a step".
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  (* SOLUTION: *)
  Case "T_Succ". 
    inversion IHHT; clear IHHT.
    SCase "t1 is a value". inversion H...
      SSCase "t1 is a bvalue". solve by inversion 2.
    SCase "t1 can take a step".
      right. inversion H as [t1' H1]. 
      exists (tsucc t1')...
  Case "T_Pred". 
    inversion IHHT; clear IHHT.
    SCase "t1 is a value". inversion H; clear H.
      SSCase "t1 is a bvalue". solve by inversion 2.
      SSCase "t1 is an nvalue". right. 
        inversion H0; subst.
        SSSCase "t1 is zero".
          exists (tzero)... 
        SSSCase "t1 is nonzero".
          exists t...
    SCase "t1 can take a step".
      right. inversion H as [t1' H1].
      exists (tpred t1')...
  Case "T_Iszero". 
    inversion IHHT; clear IHHT.
    SCase "t1 is a value". inversion H; clear H.
      SSCase "t1 is a bvalue". solve by inversion 2.
      SSCase "t1 is an nvalue". right.
        inversion H0; subst.
        SSSCase "t1 is zero".
          exists ttrue...
        SSSCase "t1 is nonzero".
          exists tfalse...
    SCase "t1 can take a step". 
      right. inversion H as [t1' H1]. 
      exists (tiszero t1')...  Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_progress_informal) *)
(** Complete the corresponding informal proof: *)

(** _Theorem_: If [|- t \in T], then either [t] is a value or else 
    [t ==> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
        \in T].  By the IH, either [t1] is a value or else [t1] can step
        to some [t1'].  

            - If [t1] is a value, then it is either an [nvalue] or a
              [bvalue].  But it cannot be an [nvalue], because we know
              [|- t1 \in Bool] and there are no rules assigning type
              [Bool] to any term that could be an [nvalue].  So [t1]
              is a [bvalue] -- i.e., it is either [true] or [false].
              If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
              while if [t1 = false], then [t] steps to [t3] by
              [ST_IfFalse].  Either way, [t] can step, which is what
              we wanted to show.

            - If [t1] itself can take a step, then, by [ST_If], so can
              [t].

    (* SOLUTION: *)

      - If the last rule in the derivation is [T_True], then [t =
        true], which is a boolean value and hence a value.  The cases
        for [T_False] and [T_Zero] are similar.

      - If the last rule in the derivation is [T_Succ], then [t = succ
        t1], with [|- t1 \in Nat].  By the IH, either [t1] is a value or
        else [t1] can step to some [t1'].

            - If [t1] is a value, then it is either an [nvalue] or a
              [bvalue].  But it cannot be an [bvalue], because we know
              [|- t1 \in Nat] and there are no rules assigning type
              [Bool] to any term that could be a [bvalue].  So [t1] is
              a [nvalue], and hence [t] is also an [nvalue] (and hence
              a value) by [nv_succ].

            - If [t1] can take a step, then by [ST_Succ], so can [t].

      - If the last rule in the derivation is [T_Pred], then [t =
        pred t1], with [|- t1 \in Nat].   By the IH, either [t1] is a
        value or else [t1] can step to some [t1'].

            - If [t1] is a value, then (by the same argument as in the
              previous case) it must be an [nvalue].  By inversion on
              the [nvalue] judgement, there are two cases:
 
                - If [t1 = zero], then [t] can take a step by
                  [ST_PredZero].

                - Otherwise, [t1 = succ t1'], with [t1'] an [nvalue].
                  Hence [t] can again take a step, this time by
                  [ST_PredSucc].

            - Finally, if [t1] can take a step, then by [ST_Pred], so
              can [t].

      - If the last rule in the derivation is [T_IsZero], then [t =
        iszero t1], with [|- t1 \in Nat].  By the IH, either [t1] is a
        value or else [t1] steps to some [t1'].

            - If [t1] is a value, it must be an [nvalue], and there
              are two cases to consider:

                - If [t1 = zero], then [t] can take a step by
                  [ST_IsZeroZero].

                - Otherwise, [t1 = succ t1'] where [t1'] is an
                  [nvalue].  Hence [t] can take a step by
                  [ST_IsZeroSucc].

            - If [t1] can take a step, then so can [t], by [ST_IsZero].
      
    []
*)

(** This is more interesting than the strong progress theorem that we
    saw in the Smallstep chapter, where _all_ normal forms were
    values.  Here, a term can be stuck, but only if it is ill
    typed. *)

(** **** Exercise: 1 star (step_review) *)
(** Quick review.  Answer _true_ or _false_.  In this language...
      - Every well-typed normal form is a value.

            TRUE: This is the content of the progress theorem.
      - Every value is a normal form.

            TRUE: This can proved by induction on values.
      - The single-step evaluation relation is
        a partial function (i.e., it is deterministic).

            TRUE: This is the determinism theorem.
      - The single-step evaluation relation is a _total_ function.

            FALSE: normal forms do not evaluate to anything + can get stuck.
*)
(** [] *)

(* ###################################################################### *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term.

    This theorem is often called the _subject reduction_ property,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

(** **** Exercise: 2 stars (finish_preservation) *)
(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case; 
         (* every case needs to introduce a couple of things *)
         intros t' HE; 
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
    Case "T_If". inversion HE; subst.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
    (* SOLUTION: *)
    Case "T_Succ". inversion HE; subst...
    Case "T_Pred". inversion HE; subst...
      SCase "ST_PredSucc". inversion HT...
    Case "T_Iszero". inversion HE; subst...  Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_preservation_informal) *)
(** Complete the following proof: *)

(** _Theorem_: If [|- t \in T] and [t ==> t'], then [|- t' \in T]. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
        \in T].  

        Inspecting the rules for the small-step reduction relation and
        remembering that [t] has the form [if ...], we see that the
        only ones that could have been used to prove [t ==> t'] are
        [ST_IfTrue], [ST_IfFalse], or [ST_If].

           - If the last rule was [ST_IfTrue], then [t' = t2].  But we
             know that [|- t2 \in T], so we are done.

           - If the last rule was [ST_IfFalse], then [t' = t3].  But we
             know that [|- t3 \in T], so we are done.

           - If the last rule was [ST_If], then [t' = if t1' then t2
             else t3], where [t1 ==> t1'].  We know [|- t1 \in Bool] so,
             by the IH, [|- t1' \in Bool].  The [T_If] rule then gives us
             [|- if t1' then t2 else t3 \in T], as required.

    (* SOLUTION: *)

      - If the last rule in the derivation were [T_True], then [t =
        true].  However, [true] does not step to anything, so this
        case cannot actually occur.

      - Similarly, neither [T_False] nor [T_Zero] could not be the
        final rule in the derivation.

      - If the last rule in the derivation is [T_Succ], then [t = succ
        t1] with [|- t1 \in Nat] and [T = Nat]. The only rule which
        could have been used to show that [t] steps is [ST_Succ], in
        which case [t1] steps to some [t1'].  So, by the IH, [|- t1' \in
        Nat], and hence [t' = succ t1'] also has type [Nat] by
        [T_Succ].

      - If the last rule in the derivation is [T_Pred], then [t = pred
        t1] with [|- t1 \in Nat].  There are only three rules which could
        have been the last rule in the derivation of [pred t1 ==> t'].

          - If the last rule was [ST_PredZero], then [t' = zero] which
            has type [Nat].

          - If the last rule was [ST_PredSucc], then [t1 = succ t'];
            by inversion on the fact that [|- t1 \in Nat] it follows
            that [|- t' \in Nat] as well.

          - If the last rule was [ST_Pred], then [t1] steps to some
            [t1']; by the IH [|- t1' \in Nat], and so [pred t1'] has
            type [Nat] as well by [T_Pred].
  
      - If the last rule in the derivation is [T_IsZero], then [t =
        iszero t1] with [|- t1 \in Nat] and [T = Bool].  There are only
        three rules which could have been the last rule in the
        derivation of [iszero t1 ==> t'].
 
          - If the last rule was [ST_IsZeroZero], then [t' = true]
            which has type [Bool].

          - If the last rule was [ST_IsZeroSucc], then [t' = false]
            which has type [Bool].

          - If the last rule was [ST_IsZero], then [t1] steps to some
            [t1'].  By the IH, [|- t1' \in Nat] as well, and hence [t' =
            iszero t1'] has type [Bool] by [T_IsZero].

    []
*)

(** **** Exercise: 3 stars (preservation_alternate_proof) *)
(** Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proof to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  (* SOLUTION: *)
  intros t t' T HT HE.
  generalize dependent T.
  step_cases (induction HE) Case;
         (* in each case, invert the given typing derivation *)
         intros T HT; inversion HT; subst; 
         (* deal with several easy or contradictory cases 
            all at once *)
         try solve [assumption; solve by inversion]...
    Case "ST_PredSucc". 
      inversion HT. subst. inversion H2. subst...  Qed.
(** [] *)

(* ###################################################################### *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we can see that a
    well-typed term can _never_ reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof. 
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.   
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.

(* ###################################################################### *)
(** ** Additional Exercises *)

(** **** Exercise: 2 stars (subject_expansion) *)
(** Having seen the subject reduction property, it is reasonable to
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t ==> t']
    and [|- t' \in T], then [|- t \in T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so if you like.)

    (* SOLUTION: *) 
       Subject expansion does not hold in this language (or most
       interesting languages).  For example, [tif tfalse
       ttrue tzero] is ill typed, but it evaluates to the
       well-typed term [tzero].  
    []
*)




(** **** Exercise: 2 stars (variation1) *)
(** Suppose, that we add this new rule to the typing relation: 
      | T_SuccBool : forall t,
           |- t \in TBool ->
           |- tsucc t \in TBool
   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]

            Remains true
      - Progress

            Becomes false:  [tsucc ttrue] is well typed, but stuck.
      - Preservation

            Remains true            
[]
*)

(** **** Exercise: 2 stars (variation2) *)
(** Suppose, instead, that we add this new rule to the [step] relation: 
      | ST_Funny1 : forall t2 t3,
           (tif ttrue t2 t3) ==> t3
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

       - Determinism becomes false: [tif ttrue
         tzero (tsucc tzero)] can now evaluate in one step
         to either [tzero] or [tsucc tzero].
[]
*)

(** **** Exercise: 2 stars, optional (variation3) *)
(** Suppose instead that we add this rule:
      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 ==> t2' ->
           (tif t1 t2 t3) ==> (tif t1 t2' t3)
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

       - Determinism again becomes false: [tif
         tfalse (tpred tzero) (tsucc tzero)] can now
         evaluate in one step to either [tsucc tzero] or
         [tif tfalse tzero (tsucc tzero)].  (There are
         several other correct counter-examples.)
[]
*)

(** **** Exercise: 2 stars, optional (variation4) *)
(** Suppose instead that we add this rule:
      | ST_Funny3 : 
          (tpred tfalse) ==> (tpred (tpred tfalse))
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

   All remain true
[]
*)

(** **** Exercise: 2 stars, optional (variation5) *)
(** Suppose instead that we add this rule:
   
      | T_Funny4 : 
            |- tzero \in TBool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

       - Progress becomes false: [tif tzero ttrue ttrue]
         has type [TBool], is a normal form, and is not a
         value.
[]
*)

(** **** Exercise: 2 stars, optional (variation6) *)
(** Suppose instead that we add this rule:
   
      | T_Funny5 : 
            |- tpred tzero \in TBool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

       - Preservation becomes false: [tpred tzero] has type
         [TBool] and evaluates in one step to [tzero], which
         does not have type [TBool].
[]
*)

(** **** Exercise: 3 stars, optional (more_variations) *)
(** Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
    [] 
*)

(** **** Exercise: 1 star (remove_predzero) *)
(** The evaluation rule [E_PredZero] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of zero to
    be undefined, rather than being defined to be zero.  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere? 

(* SOLUTION: *) 
    Yes, but doing this would break the progress property.
    A better way would be to raise an exception in this case, but this
    requires that we add exceptions to the language we're formalizing!
[] *)

(** **** Exercise: 4 stars, advanced (prog_pres_bigstep) *)
(** Suppose our evaluation relation is defined in the big-step style.
    What are the appropriate analogs of the progress and preservation
    properties?

(* SOLUTION: *) The type preservation property for the big-step
    semantics is similar to the one we gave for the small-step
    semantics: if a well-typed term evaluates to some final value,
    then this value has the same type as the original term.  The proof
    is similar to the one we gave.

    The situation with the progress property is more interesting.  A
    direct analog (if a term is well typed then it evaluates to some
    other term) makes a much stronger claim than the progress theorem
    we have given: it says that every well-typed term can be evaluated
    to some final value---that is, that evaluation always terminates
    on well-typed terms.  For arithmetic expressions, this happens to
    be the case, but for more interesting languages (languages
    involving general recursion, for example) it will often not be
    true.  For such languages, we simply have no progress property in
    the big-step style: in effect, there is no way to tell the
    difference between reaching an error state and failing to
    terminate.  This is one reason that language theorists generally
    prefer the small-step style.
[]
*)

(* $Date$ *)
