Require Import Accessors.Spec.
Require Import Bottom.Spec.
Require Import CommonDeps.
Require Import DataTypes.
Require Import GlobalDefs.
Require Import LayerSem.Libs.Zutils.div_mod_to_equations.
Require Import S2PTTreeOps.Layer.
Require Import S2PTTreeOps.RefineRel.
Require Import S2PTTreeOps.Spec.
Require Import S2PTWalk.Layer.
Require Import S2PTWalk.Spec.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.sub Z.land Z.lor Z.lxor Z.shiftl Z.shiftr Z.quot Z.rem.

Require Import LayerSem.Libs.Zutils.BitOps.
Require Import LayerSem.Libs.Zutils.hardcode_rewrite.

(* custom comparison vresion *)

(* Pair Index Type *)
Definition alpair := prod Z Z.

(* Custom eq *)
Definition eq_rel (x y : alpair) : Prop :=
  let '(x1, x2) := x in
  let '(y1, y2) := y in
  if Z.eqb x2 y2 && Z.eqb x2 2 then
    x1 / 4096 / 512  = y1 / 4096 / 512
  else if Z.eqb x2 2 || Z.eqb y2 2 then
    False
  else
    x1 / 4096 = y1 / 4096.
Notation "x '$=' y" := (eq_rel x y) (at level 70).
Notation "x '$<>' y" := (~ eq_rel x y) (at level 70).

(* decidable for eq_rel *)
Lemma al_eqdec : forall x y : alpair, {x $= y} + {x $<> y}.
Proof.
  intros [x1 x2] [y1 y2].
  unfold eq_rel; simpl.
  destruct ((x2 =? y2) && (x2 =? 2));
  [|destruct ((x2 =? 2) || (y2 =? 2))];
  match goal with
  | [|- {?x = ?y} + {?x <> ?y}] => destruct (Z.eq_dec x y); auto
  | [|- {False} + {~ False}] => right; auto
  end.
Qed.

Definition pte_mask (pte: Z) : Z :=
  pte |' (1 << 55) |' (1 << 56).

Definition rel_pte (pte1 pte2 : Z) : Prop :=
  pte_mask pte1 = pte_mask pte2.

Lemma lor_swap : forall a b c,
  a |' b |' c = a |' c |' b.
Proof.
  intros. repeat rewrite <- Z.lor_assoc.
  rewrite Z.lor_comm with (b := b). reflexivity.
Qed.

Ltac solve_pte_mask :=
  match goal with
  | [|- pte_mask (?p |' ?c) = pte_mask ?p] =>
    symmetry;
    unfold pte_mask;
    repeat rewrite lor_swap with (b := c);
    rewrite <- Z.lor_assoc with (b := c);
    rewrite Z.lor_diag; reflexivity
  | [|- pte_mask ?p = pte_mask (?p |' ?c)] =>
    unfold pte_mask;
    repeat rewrite lor_swap with (b := c);
    rewrite <- Z.lor_assoc with (b := c);
    rewrite Z.lor_diag; reflexivity
  end.

Definition fst_option {X Y : Type} (o : option (X * Y)) : option X :=
  match o with
  | Some (x, _) => Some x
  | None => None
  end.

Definition refrel_pte (ref1 ref2 : Z -> Z -> Prop) (pte1 pte2 : Z) : Prop :=
  exists v, ref1 pte1 v /\ ref2 pte2 v.

Record refrel
  {X : Type}
  (vmid : Z)
  (hst : RData)
  (walk : Z -> Z -> X -> option (Z * X))
  (mem : X)
  (rel : Z -> Z -> Prop)
: Prop :=
  {
    id_same:
      forall addr,
        let npt := hst.(shared).(e_s2pts) @ vmid in
        let r1 := walk vmid addr mem in
        let r2 :=
          (match npt.(e_lv2pt) @ (addr / 4096 / 512) with
          | (Some v_pte) => Some v_pte
          | None =>
            match npt.(e_lv3pt) @ (addr / 4096) with
            | (Some v_pte) => Some v_pte
            | None => None
            end
          end) in
        match r1, r2 with
        | Some (v1, _), Some v2 =>
          refrel_pte rel rel_pte v1 v2
        | None, None => True
        | _, _ => False
        end
  }.

Theorem set_refine :
  forall {X : Type} vmid addr level pte pte' mem mem' mem'' hst hst'
      (walk : Z -> Z -> X -> option (Z * X))
      (set : Z -> Z -> Z -> Z -> X -> option X)
      (rel: Z -> Z -> Prop)
    (* array propery *)
    (Haneq: forall addr' level',
        (addr', level') $<> (addr, level)->
        walk vmid addr' mem' = 
        walk vmid addr' mem)
    (Haeq: forall addr' level', 
      (addr', level') $= (addr, level)->
      walk vmid addr' mem' = Some (pte', mem'') /\ rel pte' pte),
    (* goal *)
    refrel vmid hst walk mem rel ->
    set_npt_spec vmid addr level pte hst = Some hst' ->
    set vmid addr level pte mem = Some mem' ->
    refrel vmid hst' walk mem' rel.
Proof.
  intros X vmid addr level pte pte' mem mem' mem'' gst gst' walk set rel
  Haneq Haeq Hrel Hspec Hspec2.
  inv Hrel. constructor. intros.
  rename addr0 into addr'.
  (* specialize (id_same0 addr' level') as id_same'. *)
  unfold set_npt_spec in *.
  unfold walk_npt_spec in *.
  repeat autounfold with sem in *.
  repeat simpl_hyp Hspec;
  repeat simpl_hyp Hspec2.
  repeat extract_prop.
  clear Prop0 Prop2 Prop1 Prop3.
  subst npt r1 r2.
  inv Hspec. simpl.
  rewrite ZMap.gsspec. rewrite zeq_true.
  simpl_func C3; repeat extract_prop. simpl.
  - simpl_func C1; repeat extract_prop.
    clear Prop0 Prop1 Prop2. simpl.
    destruct (al_eqdec (addr', level) (addr, level)) as [eq|neq].
    (* addr = addr' *)
    + specialize (Haeq _ _ eq) as [Haeq rel_low]. simpl in eq.
      rewrite Z.eqb_refl in eq. rewrite C in eq. simpl in eq.
      rewrite eq. rewrite ZMap.gsspec. rewrite zeq_true. rewrite Haeq.
      unfold refrel_pte. simpl. exists pte. unfold rel_pte.
      split; [assumption|solve_pte_mask].
    (* addr <> addr' *) 
    + specialize (Haneq _ _ neq) as Haneq. simpl in neq.
      rewrite Z.eqb_refl in neq. rewrite C in neq. simpl in neq.
      rewrite ZMap.gsspec. rewrite zeq_false; [|assumption].
      rewrite Haneq. apply id_same0.
  - simpl_func C0; repeat extract_prop. simpl.
    clear Prop1.
    destruct (al_eqdec (addr', level) (addr, level)) as [eq|neq].
    (* addr = addr' *)
    + specialize (Haeq _ _ eq) as [Haeq rel_low]. simpl in eq.
      rewrite Z.eqb_refl in eq. rewrite C in eq. simpl in eq.
      simpl in Prop0. rewrite eq in *. rewrite Prop0.
      rewrite ZMap.gsspec. rewrite zeq_true. rewrite Haeq.
      unfold refrel_pte. simpl. exists pte. unfold rel_pte.
      split; [assumption|solve_pte_mask].
    (* addr <> addr' *)
    + specialize (Haneq _ _ neq) as Haneq. simpl in neq.
      rewrite Z.eqb_refl in neq. rewrite C in neq. simpl in neq.
      rewrite ZMap.gsspec. rewrite zeq_false; [|assumption].
      rewrite Haneq. apply id_same0.
Qed.

Theorem walk_refine:
  forall {X : Type} vmid addr mem mem' hst hst' v1 v2
    (walk : Z -> Z -> X -> option (Z * X))
    (rel: Z -> Z -> Prop)
    (* array theory *)
    (Haeq: forall addr',
        fst_option (walk vmid addr' mem) = 
        fst_option (walk vmid addr' mem')),
    (* goal *)
    refrel vmid hst walk mem rel ->
    walk_npt_spec vmid addr hst = Some (v1, hst') ->
    walk vmid addr mem = Some (v2, mem') ->
    refrel vmid hst' walk mem' rel.
Proof.
  intros X vmid addr mem mem' hst hst' v1 v2 walk rel Haeq Hrel Hspec Hspec2.
  unfold walk_npt_spec in *.
  repeat autounfold with sem in *.
  repeat simpl_hyp Hspec;
  repeat extract_prop.
  clear Prop0 Prop1 Prop2 Prop3.
  inv Hspec.
  (* refine rel *)
  inv Hrel. constructor. intros.
  rename id_same0 into id_same', addr0 into addr'.
  specialize (id_same' addr').
  subst npt r1 r2. simpl in id_same'.
  remember (
    match (e_lv2pt (e_s2pts (shared hst')) @ vmid) @ (addr' / 4096 / 512) with
      | Some v_pte => Some v_pte
      | None =>
          match (e_lv3pt (e_s2pts (shared hst')) @ vmid) @ (addr' / 4096) with
          | Some v_pte => Some v_pte
          | None => None
          end
      end
  ) as r2.
  specialize (Haeq addr').
  destruct (walk vmid addr' mem) as [p1|] eqn:Hg1;
  destruct (walk vmid addr' mem') as [p2|] eqn:Hg2;
  try (destruct p1);
  try (destruct p2);
  simpl in Haeq;
  destruct r2;
  try congruence.
Qed.
