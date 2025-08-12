import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Grassmannian


/-!
# Gaussian Binomial Coefficients

This file defines Gaussian binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).

## Main definition and results

## Tags

gaussian binomial coefficient
-/

/-
Note: I don't think this is possible to do via quotients. Or at least, I'm having a lot of trouble
trying to figure out how to do it.
-/

universe u v

variable {V W : Type v} {K : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

namespace Submodule
open LinearMap QuotientAddGroup

section quot_bijectionOne

/-
Do I need this?
-/
noncomputable def quotientEquiv : (fst K V W) ≃ₗ[K] ((V × W) ⧸ (snd K V W)) := by
  apply ((Submodule.quotientEquivOfIsCompl (snd K V W) (fst K V W)) _).symm
  have h := @isCompl_range_inl_inr K V W _ _ _ _ _
  rw [range_inl, range_inr] at h
  constructor
  · exact (_root_.id (IsCompl.symm h)).disjoint
  · exact (_root_.id (IsCompl.symm h)).codisjoint

end quot_bijectionOne

section prod_bijectionOne

lemma oneDimDisjoint (X : Submodule K (V × K))
(hX : ¬ (snd K V K) ≤ X) : X ⊓ (snd K V K) = ⊥ := by
  simp_all only [snd, comap_bot]
  ext x;
  constructor
  · norm_num
    intros hx hx2
    by_contra
    apply hX
    intros y hy
    have h4 := Submodule.smul_mem _ (y.2 * x.2⁻¹) hx
    aesop
  · simp_all only [mem_bot, zero_mem, implies_true]

lemma injMap (X : Submodule K (V × K))
(hX : ¬ (snd K V K) ≤ X) :
  Function.Injective ((LinearMap.fst K V K).domRestrict X) := by
  apply injective_domRestrict_iff.2 (oneDimDisjoint X hX)

def reconstructMap (V : Type v) (K : Type*) [Field K] [AddCommGroup V] [Module K V] :
(X : Submodule K V) × (X →ₗ[K] K) → Submodule K (V × K) :=
  fun ⟨X, φX⟩ => Submodule.map (LinearMap.prod X.subtype φX) ⊤

/-
This corresponds to q^r(m - 1 gauss r)
-/
lemma reconstructMapInjective : Function.Injective (reconstructMap V K) := by
  intros RφR SφS h
  obtain ⟨R, φR⟩ := RφR
  obtain ⟨S, φS⟩ := SφS
  unfold reconstructMap at h
  simp only [map_top] at h
  have hRS : R = S := by
    ext x;
    have h2 := LinearMap.mem_range_self (LinearMap.prod (Submodule.subtype S) φS)
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have h2 := LinearMap.mem_range_self (LinearMap.prod (Submodule.subtype R) φR) ⟨x, hx⟩
      simp only [h, prod_apply, Pi.prod, subtype_apply, mem_range, Prod.mk.injEq, Subtype.exists,
        exists_and_left, exists_eq_left] at h2
      apply h2.1
    · have h2 := LinearMap.mem_range_self (LinearMap.prod (Submodule.subtype S) φS) ⟨x, hx⟩
      rw [←h] at h2
      simp only [prod_apply, Pi.prod, subtype_apply, mem_range, Prod.mk.injEq, Subtype.exists,
        exists_and_left, exists_eq_left] at h2
      apply h2.1
  subst hRS
  simp_all only [Sigma.mk.injEq, heq_eq_eq, true_and]
  apply LinearMap.ext (fun x => ?_)
  have hRx : ⟨x, φR x⟩ ∈ range (R.subtype.prod φR) := by
    simp only [mem_range, prod_apply, Pi.prod, subtype_apply, Prod.mk.injEq, SetLike.coe_eq_coe,
      exists_eq_left]
  rw [h] at hRx
  simp only [mem_range, prod_apply, Pi.prod, subtype_apply, Prod.mk.injEq, SetLike.coe_eq_coe,
    exists_eq_left] at hRx
  rw [hRx]

/-
Embedding
-/
def reconstructMapEmbed : (X : Submodule K V) × (X →ₗ[K] K) ↪ Submodule K (V × K) where
  toFun := reconstructMap V K
  inj' := reconstructMapInjective

/-
First direction of equivalence
-/
lemma oneDimDisjoint_ofMemRange (X : Submodule K (V × K)) (Y : Submodule K V) (f : Y →ₗ[K] K)
  (hXY : (reconstructMap V K) ⟨Y, f⟩ = X) :
   ¬ (snd K V K) ≤ X := by
    by_contra h2
    simp only [reconstructMap, map_top] at hXY
    rw [←hXY] at h2
    obtain ⟨a, ha0⟩ := (nontrivial_iff_exists_ne (0 : K)).1 Field.toNontrivial
    apply ha0
    have ha : ⟨0, a⟩ ∈ (snd K V K) := by exact rfl
    have h4 := h2.subset ha
    simp only [SetLike.mem_coe, mem_range, prod_apply, Pi.prod, subtype_apply, Prod.mk.injEq,
      ZeroMemClass.coe_eq_zero, exists_eq_left, map_zero] at h4
    rw [h4]

/-
Second direction of equivalence
-/
lemma memRange_ofOneDimDisjoint (X : Submodule K (V × K)) (hX : ¬ (snd K V K) ≤ X) :
  ∃ Y f, (reconstructMap V K) ⟨Y, f⟩ = X := by
  let φ1 := ((LinearMap.snd K V K).domRestrict X)
  let φ2 := (LinearEquiv.ofInjective
      ((LinearMap.fst K V K).domRestrict X) (injMap X hX))
  use range ((LinearMap.fst K V K).domRestrict X), φ1 ∘ₗ φ2.symm.toLinearMap
  ext x
  --simp_all only [reconstructMap']
  unfold reconstructMap
  simp only [map_top, mem_range, prod_apply, Pi.prod, subtype_apply,
    coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Subtype.exists, range_domRestrict, mem_map,
    fst_apply, Prod.exists, exists_and_right, exists_eq_right]
  constructor
  · intros ha
    obtain ⟨a, ⟨⟨b, hab⟩, rfl⟩⟩ := ha
    have h2 : φ2.symm ⟨a, (by aesop)⟩ = ⟨(a, b), hab⟩ := by
      apply (Function.Injective.eq_iff φ2.injective).1
        (LinearEquiv.apply_symm_apply φ2 ⟨a, (by aesop)⟩)
    rw [h2]
    apply hab
  · intros hx
    use x.1
    apply Exists.intro (by use x.2)
    have h2 : φ2.symm ⟨x.1, (by aesop)⟩ = ⟨(x.1, x.2), hx⟩ := by
      apply (Function.Injective.eq_iff φ2.injective).1
        (LinearEquiv.apply_symm_apply φ2 ⟨x.1, (by aesop)⟩)
    rw [h2, LinearMap.domRestrict_apply]
    simp only [Prod.mk.eta, snd_apply]

/-
Equivalence
-/
lemma memRangereconstructMapIff (X : Submodule K (V × K)) :
  ¬ (snd K V K) ≤ X ↔ X ∈ Set.range (reconstructMap V K) := by
  refine ⟨fun hR => ?_, fun hM => ?_⟩
  · obtain ⟨Y, ⟨f, rfl⟩⟩ := memRange_ofOneDimDisjoint X hR
    simp only [Set.mem_range]
    aesop
  · obtain ⟨S, hS⟩ := hM
    apply oneDimDisjoint_ofMemRange X S.1 S.2 hS

/-
First bijection complete
-/
noncomputable def equiv_ofOneDimDisjoint :
  {X : Submodule K (V × K) // ¬ (snd K V K) ≤ X} ≃ (X : Submodule K V) × (X →ₗ[K] K) := by
  simp_rw [memRangereconstructMapIff]
  apply (Equiv.ofInjective (reconstructMap V K) reconstructMapInjective).symm

end prod_bijectionOne

section prod_bijectionTwo

/-
Second bijection complete
-/
def equiv_ofOneDimSubmodule (V W : Type*) (K : Type*) [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] :
  {X : Submodule K (V × W) // (snd K V W) ≤ X} ≃ Submodule K V where
    toFun := fun s => Submodule.map (LinearMap.fst K V W) s
    invFun := fun r => ⟨r.prod ⊥ ⊔ (snd K V W), le_sup_right⟩
    left_inv := fun ⟨s, s2⟩ => by
      simp_all only [snd, comap_bot]
      ext x;
      simp_rw [mem_sup, mem_ker, fst_apply]
      simp only [mem_prod, mem_map, fst_apply, Prod.exists, exists_and_right, exists_eq_right,
        mem_bot, exists_and_left, exists_eq_left, Prod.mk_add_mk, add_zero, existsAndEq, and_true,
        zero_add]
      refine ⟨fun ⟨a, ⟨⟨b, hb⟩, ⟨c, hc⟩⟩⟩ => ?_, fun hx => ?_⟩
      · rw [←hc]
        specialize s2 (mem_ker.2 (fst_apply (0, - b + c)))
        have h2 := (add_mem hb s2)
        simp only [Prod.mk_add_mk, add_zero, add_neg_cancel_left] at h2
        apply h2
      · refine ⟨x.1, ?_⟩
        refine ⟨?_, ?_⟩
        · use x.2
        · use x.2
    right_inv := fun r => by
      simp only [map_sup, prod_map_fst, sup_eq_left]
      intros x hx
      obtain ⟨a, ⟨ha1, rfl⟩⟩ := hx
      exact (Quotient.mk_eq_zero r).mp (congrArg Quotient.mk ha1)

end prod_bijectionTwo

section disjointSum

--variable [DecidableEq K] [DecidableEq V] [Decidable (snd K V K ≤ (x : Submodule (V × K)))]
/-
What decidability do we need?
-/
open Classical in noncomputable def mapDisjointSum (V : Type v) (K : Type*) [Field K]
[AddCommGroup V] [Module K V] :
  Submodule K (V × K) ≃ (Submodule K V ⊕ ((X : Submodule K V) × (X →ₗ[K] K))) where
    toFun := fun X => if h : (snd K V K) ≤ X
      then Sum.inl (equiv_ofOneDimSubmodule V K K ⟨X, h⟩)
      else Sum.inr (equiv_ofOneDimDisjoint.toFun ⟨X, h⟩)
    invFun := sorry
    left_inv := sorry
    right_inv := sorry

end disjointSum

section Grassmannian

open Module Grassmannian

variable [Module.Finite K V]

lemma grassmannianFinrank (k : ℕ) (X : G(k, V; K)) :
  Module.finrank K X = (Module.finrank K V) - k := by
  have h2 := Module.Grassmannian.rankAtStalk_eq X
  simp only [rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id, forall_const] at h2
  simp_rw [← h2]
  rw [Submodule.finrank_quotient, Nat.sub_sub_self]
  apply Submodule.finrank_le

lemma grassmannianFinrank' (k : ℕ) (X : G((Module.finrank K V) - k, V; K))
 (hk : k ≤ Module.finrank K V) : Module.finrank K X = k := by
  rw [grassmannianFinrank, Nat.sub_sub_self hk]

end Grassmannian

section dimension

/-
If (snd K V K) is not a submodule of X, then the projection preserves its dimension
(i.e. there is a bijection between X and its image in the projection)
-/
noncomputable def submoduleEquiv_ofOneDimDisjoint (X : Submodule K (V × K))
  (hX : ¬ (snd K V K) ≤ X) :
    X ≃ₗ[K] Submodule.map (LinearMap.fst K V K) X := by
  rw [← range_domRestrict]
  apply LinearEquiv.ofInjective ((LinearMap.fst K V K).domRestrict X) (injMap X hX)

/-
If ¬ (snd K V K) ≤ X, the dimension will be equal to that of its image
-/
lemma subspaceDim_ofOneDimDisjoint (X : Submodule K (V × K)) (hX : ¬ (snd K V K) ≤ X) :
  Module.finrank K X = Module.finrank K (Submodule.map (LinearMap.fst K V K) X) :=
  LinearEquiv.finrank_eq (submoduleEquiv_ofOneDimDisjoint X hX)

variable [FiniteDimensional K V] [FiniteDimensional K W]

/-
If (snd K V K) ≤ X, we can break up the dimension of X
-/
lemma subspaceDim_ofOneDimSubspace (X : Submodule K (V × W)) (hX : (snd K V W) ≤ X) :
  Module.finrank K X =
  Module.finrank K (Submodule.map (LinearMap.fst K V W) X) + Module.finrank K W := by
    rw [snd, comap_bot] at hX
    rw [← LinearMap.finrank_range_add_finrank_ker ((LinearMap.fst K V W).domRestrict X),
      range_domRestrict, Nat.add_left_cancel_iff, ker_domRestrict,
      LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hX), ker_fst,
      LinearEquiv.finrank_eq (LinearEquiv.ofInjective (inr K V W) inr_injective)]

/-

-/
--lemma finrankRelation (X : Submodule K (V × W)) : Fintype.card


/-lemma fintypeCard_SubspaceDim : Fintype.card (Submodule K (V × K))
  = Fintype.card -/

end dimension

end Submodule
