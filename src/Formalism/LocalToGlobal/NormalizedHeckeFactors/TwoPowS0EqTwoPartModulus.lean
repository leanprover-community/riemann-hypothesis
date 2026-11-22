module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.Gal

namespace Formalism.L2

section Points

variable {O X : Type} [CommRing O] [IsDomain O] [Fintype X]

@[simp] theorem evPt_apply (T : Subalgebra O (X → O)) (x : X) (f : T) : evPt T x f = (f : X → O) x := rfl

end Points

section Record

variable (D : D7)

theorem zgoodSub : D.nd.ZgoodSub := fun i x hx =>
  (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1

end Record

section Good

open Polynomial

end Good

section Tame

end Tame

def latRel {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V) :
    Set (L.gen → O) :=
  {r | ∑ g : L.gen, φ (r g) • (g : V) = 0}

def latRelSub {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V) :
    Submodule O (L.gen → O) where
  carrier := latRel L
  zero_mem' := by simp [latRel]
  add_mem' := by
    intro a b ha hb
    simp only [latRel, Set.mem_ofPred_eq, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [latRel, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at ha ⊢
    rw [← Finset.smul_sum, ha, smul_zero]

@[simp] theorem mem_latRelSub {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : Rows.OLat O φ V) (r : L.gen → O) : r ∈ latRelSub L ↔ r ∈ latRel L := Iff.rfl

theorem embK_OtoLL_mem (D : D7) (i : D.nd.Loc) (y : D.what₂.O) :
    D.nd.embK i (D.what₂.OtoLL y) ∈ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range := by
  rw [← D.nd.embK_w i]
  by_cases h0 : D.what₂.OtoLL y = 0
  · rw [h0, AddValuation.map_zero]; exact le_top
  · rw [D.val_eq _ _ h0]
    have hint := D.O_int y
    set x : 𝓞 D.what₂.LL := ⟨D.what₂.OtoLL y, hint⟩
    have hx : (x : D.what₂.LL) = D.what₂.OtoLL y := rfl
    have hle := (D.plEq (D.nd.w i)).valuation_le_one (K := D.what₂.LL) x
    have hne : (D.plEq (D.nd.w i)).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL x) ≠ 0 := by
      simpa [hx] using h0
    unfold vAdd
    have : WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y)) ≤ 0 := by
      have hne' : (D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y) ≠ 0 := by simpa [hx] using hne
      have hle' : (D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y) ≤ 1 := by simpa [hx] using hle
      have h2 : WithZero.exp (WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y))) ≤
          WithZero.exp (0 : ℤ) := by
        rw [WithZero.exp_log hne']; simpa using hle'
      exact WithZero.exp_le_exp.mp h2
    exact_mod_cast (by omega : (0:ℤ) ≤ -WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y)))

def fracRangeEquiv (O : Type) [CommRing O] [IsDomain O] :
    O ≃+* (algebraMap O (FractionRing O)).range :=
  RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
     (algebraMap O (FractionRing O)).rangeRestrict_surjective⟩

def sOf (D : D7) (i : D.nd.Loc) : D.what₂.O →+* D.nd.O i :=
  (fracRangeEquiv (D.nd.O i)).symm.toRingHom.comp
    (((D.nd.embK i).comp D.what₂.OtoLL).codRestrict _ (embK_OtoLL_mem D i))

theorem sOf_spec (D : D7) (i : D.nd.Loc) (y : D.what₂.O) :
    algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (sOf D i y) = D.nd.embK i (D.what₂.OtoLL y) := by
  have h := (fracRangeEquiv (D.nd.O i)).apply_symm_apply
    (((D.nd.embK i).comp D.what₂.OtoLL).codRestrict _ (embK_OtoLL_mem D i) y)
  exact congrArg Subtype.val h

structure NormalizedDataCompatibility (D : D7) where
  bj : ∀ i, (D.what₂.MjLat (D.nd.j i)).gen → D.nd.Bj i
  bj_span : ∀ i, Submodule.span (D.nd.O i) (Set.range (bj i)) = ⊤
  bj_rel : ∀ i (c : (D.what₂.MjLat (D.nd.j i)).gen → D.nd.O i), ∑ g, c g • bj i g = 0 ↔
    c ∈ Submodule.span (D.nd.O i) ((fun r => (sOf D i) ∘ r) '' latRel (D.what₂.MjLat (D.nd.j i)))

end Formalism.L2
