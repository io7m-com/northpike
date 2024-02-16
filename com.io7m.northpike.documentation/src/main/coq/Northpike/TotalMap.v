Require Import Coq.Lists.List.

Module Type KeyT.
  Parameter t     : Set.
  Parameter eqDec : forall (t0 t1 : t), {t0 = t1}+{t0 <> t1}.
End KeyT.

Module Type S (K : KeyT).

  Parameter t   : Set -> Set.
  Definition kt := K.t.

  Parameter init : forall {V : Set}, (forall k : kt, V) -> t V.
  Parameter get  : forall {V : Set}, t V -> kt -> V.
  Parameter put  : forall {V : Set}, t V -> kt -> V -> t V.
  Parameter puts : forall {V : Set}, t V -> list (kt * V) -> t V.

  (** An inserted key/value can be found afterwards. *)
  Parameter putGet : forall
    {V   : Set}
    (m   : t V)
    (k   : kt)
    (v   : V),
    v = get (put m k v) k.

  (** An inserted key/value does not affect other keys. *)
  Parameter putRemains : forall
    {V     : Set}
    (m     : t V)
    (k0 k1 : kt)
    (v     : V),
    k0 <> k1 ->
      get m k0 = get (put m k1 v) k0.

  (** An otherwise empty map always returns the default. *)
  Parameter initGet : forall
    {V   : Set}
    (k   : kt)
    (f   : kt -> V),
    get (init f) k = f k.

  (** A redundantly inserted key/value is redundant. *)
  Parameter putPut : forall
    {V     : Set}
    (m     : t V)
    (k     : kt)
    (v0 v1 : V),
    put m k v1 = put (put m k v0) k v1.

End S.

Module TotalMapList (K : KeyT) : S K.

  Inductive totalMap (V : Set) : Set :=
    TotalMap : (K.t -> V) -> list (K.t * V) -> totalMap V.

  Definition t := totalMap.
  Definition kt := K.t.

  Definition init
    {V : Set}
    (f : kt -> V)
  : t V :=
    TotalMap V f nil.

  Definition matches
    {V : Set}
    (k : K.t)
    (p : K.t * V)
  : bool :=
    match p with
    | (pk, _) =>
      match K.eqDec k pk with
      | left _  => true
      | right _ => false
      end
    end.

  Lemma matchesEq0 : forall V k0 k1 v,
    @matches V k0 (k1, v) = true -> k0 = k1.
  Proof.
    intros V k0 k1 v Hm.
    unfold matches in Hm.
    destruct (K.eqDec k0 k1) as [HL|HR].
      - auto.
      - contradict Hm; discriminate.
  Qed.

  Lemma matchesEq1 : forall V k0 k1 v,
    k0 = k1 -> @matches V k0 (k1, v) = true.
  Proof.
    intros V k0 k1 v Hm.
    unfold matches.
    destruct (K.eqDec k0 k1) as [HL|HR].
      - auto.
      - contradiction.
  Qed.

  Lemma matchesEq : forall V k0 k1 v,
    @matches V k0 (k1, v) = true <-> k0 = k1.
  Proof.
    intros V k0 k1.
    split.
    apply matchesEq0.
    apply matchesEq1.
  Qed.

  Lemma matchesNEq0 : forall V k0 k1 v,
    @matches V k0 (k1, v) = false -> k0 <> k1.
  Proof.
    intros V k0 k1 v Hm.
    unfold matches in Hm.
    destruct (K.eqDec k0 k1) as [HL|HR].
      - contradict Hm; discriminate.
      - auto.
  Qed.

  Lemma matchesNEq1 : forall V k0 k1 v,
    k0 <> k1 -> @matches V k0 (k1, v) = false.
  Proof.
    intros V k0 k1 v Hm.
    unfold matches.
    destruct (K.eqDec k0 k1) as [HL|HR].
      - contradiction.
      - auto.
  Qed.

  Lemma matchesNEq : forall V k0 k1 v,
    @matches V k0 (k1, v) = false <-> k0 <> k1.
  Proof.
    intros V k0 k1.
    split.
    apply matchesNEq0.
    apply matchesNEq1.
  Qed.

  Definition listFind
    {V  : Set}
    (es : list (K.t * V))
    (k  : K.t)
  : option (K.t * V) :=
    find (matches k) es.

  Fixpoint listPut
    {V  : Set}
    (es : list (K.t * V))
    (k  : K.t)
    (v  : V)
  : list (K.t * V) :=
    match es with
    | nil           => cons (k, v) nil
    | (ek, ev) :: rs =>
      match K.eqDec k ek with
      | left _  => (ek, v) :: rs
      | right _ => (ek, ev) :: (listPut rs k v)
      end
    end.

  (** An inserted key/value can be found afterwards. *)
  Theorem listPutFind : forall
    {V  : Set}
    (es : list (K.t * V))
    (k  : K.t)
    (v  : V),
    Some (k, v) = listFind (listPut es k v) k.
  Proof.
    induction es as [|z zs]. {
      intros k v.
      simpl.
      destruct (K.eqDec k k) as [HL|HR].
        - reflexivity.
        - contradiction.
    } {
      intros k v.
      destruct z as [zk0 zv0].
      simpl.
      destruct (K.eqDec k zk0) as [HL0|HR0]. {
        subst.
        simpl.
        destruct (K.eqDec zk0 zk0) as [HK0|HK1].
          - reflexivity.
          - contradiction.
      } {
        simpl.
        destruct (K.eqDec k zk0) as [HL1|HR1].
          - subst; contradiction.
          - auto.
      }
    }
  Qed.

  Lemma listFindFold : forall (V : Set) r k xs,
    r = find (matches k) xs <-> r = @listFind V xs k.
  Proof.
    intros V r k xs.
    split; intros; unfold listFind in *; auto.
  Qed.

  (** An inserted key/value does not affect other keys. *)
  Theorem listPutRemains : forall
    {V     : Set}
    (es    : list (K.t * V))
    (k0 k1 : K.t)
    (v     : V),
      k0 <> k1 ->
        listFind es k0 = listFind (listPut es k1 v) k0.
  Proof.
    intros V es.
    induction es as [|y ys]. {
      intros k0 k1 ? ?.
      destruct (K.eqDec k0 k1).
        - subst; contradiction.
        - simpl.
          destruct (K.eqDec k0 k1).
          * subst; contradiction.
          * reflexivity.
    } {
      intros k0 k1 v Hneq.
      simpl.
      destruct y as [yk yv].
      simpl.
      destruct (K.eqDec k0 yk). {
        subst.
        destruct (K.eqDec k1 yk). {
          subst; contradiction.
        } {
          simpl.
          destruct (K.eqDec yk yk).
            - reflexivity.
            - contradiction.
        }
      } {
        destruct (K.eqDec k1 yk). {
          simpl.
          destruct (K.eqDec k0 yk).
            - subst; contradiction.
            - reflexivity.
        } {
          simpl.
          destruct (K.eqDec k0 yk).
            - subst; contradiction.
            - apply IHys; auto.
        }
      }
    }
  Qed.

  Theorem listPutPut : forall
    {V     : Set}
    (es    : list (K.t * V))
    (k     : K.t)
    (v0 v1 : V),
    listPut es k v1 = listPut (listPut es k v0) k v1.
  Proof.
    intros V es.
    induction es as [|y ys]. {
      intros k v0 v1.
      simpl.
      destruct (K.eqDec k k).
      - reflexivity.
      - contradiction.
    } {
      intros k v0 v1.
      simpl.
      destruct y as [yk yv].
      destruct (K.eqDec k yk). {
        subst.
        simpl.
        destruct (K.eqDec yk yk).
        - reflexivity.
        - contradiction.
      } {
        simpl.
        destruct (K.eqDec k yk). {
          subst.
          contradiction.
        } {
          pose proof (IHys k v0 v1) as Heq.
          rewrite <- Heq.
          reflexivity.
        }
      }
    }
  Qed.

  Fixpoint listPutsF
    {V  : Set}
    (ks : list (kt * V))
    (xs : list (kt * V))
    {struct ks}
  : list (kt * V) :=
    match ks with
    | nil             => nil
    | cons (k, v) kss => listPutsF kss (listPut xs k v)
    end.

  Definition listPuts
    {V  : Set}
    (ks : list (kt * V))
    (xs : list (kt * V))
  : list (kt * V) :=
    listPutsF ks xs.

  Definition get
    {V : Set}
    (m : totalMap V)
    (k : kt)
  : V :=
    match m with
    | TotalMap _ f xs =>
      match listFind xs k with
      | Some (_, v) => v
      | None        => f k
      end
    end.

  Definition put
    {V : Set}
    (m : t V)
    (k : kt)
    (v : V)
  : t V :=
    match m with
    | TotalMap _ f xs => TotalMap _ f (listPut xs k v)
    end.

  Definition puts
    {V  : Set}
    (m  : t V)
    (ks : list (kt * V))
  : t V :=
    match m with
    | TotalMap _ f xs => TotalMap _ f (listPuts ks xs)
    end.

  Theorem putGet : forall
    {V   : Set}
    (m   : t V)
    (k   : kt)
    (v   : V),
    v = get (put m k v) k.
  Proof.
    destruct m as [d xs].
    unfold put, get.
    intros k r.
    rewrite <- (listPutFind xs k r).
    reflexivity.
  Qed.

  Theorem putRemains : forall
    {V     : Set}
    (m     : t V)
    (k0 k1 : kt)
    (v     : V),
    k0 <> k1 ->
      get m k0 = get (put m k1 v) k0.
  Proof.
    destruct m as [d xs].
    unfold put, get.
    intros k0 k1 v Hneq.
    rewrite <- listPutRemains.
    reflexivity.
    auto.
  Qed.

  Theorem initGet : forall
    {V   : Set}
    (k   : kt)
    (f   : kt -> V),
    get (init f) k = f k.
  Proof.
    intros V k f.
    unfold init, get.
    reflexivity.
  Qed.

  Theorem putPut : forall
    {V     : Set}
    (m     : t V)
    (k     : kt)
    (v0 v1 : V),
    put m k v1 = put (put m k v0) k v1.
  Proof.
    intros V m k v0 v1.
    unfold put.
    destruct m; rewrite <- listPutPut; reflexivity.
  Qed.

End TotalMapList.
