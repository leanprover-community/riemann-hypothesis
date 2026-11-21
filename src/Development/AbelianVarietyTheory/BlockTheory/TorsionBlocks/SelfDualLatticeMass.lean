import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass

open NumberField Formalism.BasicNotions

def PosDefAtRealPlaces {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) : Prop :=
  ∀ (τ : E →+* ℂ) (x : W.V), x ≠ 0 → 0 < (τ (W.hD x x)).re

def SelfDualMass : Prop :=
  ∀ D : D7,
    letI := D.host.cmStar
    ∀ W : HSpace D.host.E, PosDefAtRealPlaces W →
      Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.MainNotions.StandardLattice.massI D W.rank


section Std

variable (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)

open Formalism.MainNotions.StandardLattice

omit [NumberField E] in
theorem stdForm_apply (x y : Fin M → E) : stdForm E M x y = ∑ i, star (x i) * y i := rfl

omit [StarRing E] in
theorem mem_stdLat_iff (x : Fin M → E) : x ∈ stdLat E M ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro i
      by_cases hij : i = j
      · subst hij; simpa using isIntegral_one
      · simpa [hij] using isIntegral_zero
    | zero => intro i; simpa using isIntegral_zero
    | add a b _ _ ha hb => intro i; exact (ha i).add (hb i)
    | smul a y _ hy =>
      intro i
      have : (a • y) i = (a : E) * y i := by simp [Algebra.smul_def]
      rw [this]
      exact a.isIntegral_coe.mul (hy i)
  · intro hx
    have : x = ∑ i, (⟨x i, hx i⟩ : 𝓞 E) • (Pi.single i 1 : Fin M → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [NumberField E] [StarRing E] in
theorem mem_one_iff (a : E) : a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩

def stdSpace : HSpace E where
  V := Fin M → E
  hT := stdForm E M
  herm := ⟨fun x y => by
    simp [stdForm_apply, starRingEnd_apply, mul_comm]⟩
  nondeg := by
    constructor
    · intro x hx
      ext i
      have := hx (Pi.single i 1)
      simpa [stdForm_apply, Pi.single_apply] using this
    · intro x hx
      ext i
      have := hx (Pi.single i 1)
      simpa [stdForm_apply, Pi.single_apply, apply_ite star] using this
  rank := M
  rank_eq := by simp
  frame := Pi.basisFun E (Fin M)
  sig := fun _ => (M, 0)
  L0 := stdLat E M
  standardTuple_isLattice :=
    { fg := Submodule.fg_span (Set.finite_range _)
      span_eq_top := by
        rw [eq_top_iff, ← (Pi.basisFun E (Fin M)).span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, by simp⟩ }
  baseLattice_isUnimodular := by
    ext x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, mem_one_iff, stdForm_apply, mem_stdLat_iff]
    constructor
    · intro h i
      have := h (Pi.single i 1) ((mem_stdLat_iff E M _).1 (Submodule.subset_span ⟨i, rfl⟩))
      simpa [Pi.single_apply, apply_ite star] using this
    · intro hx y hy
      exact IsIntegral.sum _ fun i _ => ((hy i).map (starRingEnd E).toIntAlgHom).mul (hx i)


end Std


end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass
