Require Import Accessors.Spec.
Require Import Bottom.Spec.
Require Import CommonDeps.
Require Import DataTypes.
Require Import GlobalDefs.
Require Import LayerSem.Libs.Zutils.div_mod_to_equations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.sub Z.land Z.lor Z.lxor Z.shiftl Z.shiftr Z.quot Z.rem.

Require Import LayerSem.Libs.Zutils.BitOps.
Require Import LayerSem.Libs.Zutils.hardcode_rewrite.

Definition lshl (n digit : Z) : Z :=
  n * (2 ^ digit).

Definition lshr (n digit : Z) : Z :=
  n / (2 ^ digit).

Definition substr (n head tail : Z) : Z :=
  lshr (n mod (2 ^ (head + 1))) tail.

Definition substr_eq : forall z,
  is_addr z -> substr z 47 21 = z / 4096 / 512.
Proof.
  intros.
  unfold substr. unfold lshr. unfold is_addr, MAX_ADDR in H.
  change (2 ^ (47 + 1)) with (1 << 48).
  assert (0 <= z < 1 << 48) by lia.
  rewrite (Z.mod_small _ _ H0).
  rewrite Zdiv_Zdiv; [|lia|lia].
  reflexivity.
Qed.
