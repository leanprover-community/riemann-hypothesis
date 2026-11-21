import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ChainIdeals

theorem host_ne_zero (D : D7) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ≠ 0 ∧ D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ dI D ≠ 0 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
  · rw [h, zero_mul, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul] at hP; exact zero_ne_one hP
  · rw [dI] at h; rw [h, zero_mul] at hP; exact zero_ne_one hP

theorem step (D : D7) {j : ℕ} (h : j + 1 + 1 ≤ D.R.m) :
    D.host.AA⁻¹ * (dI D * cI D j) = D.host.AA * cI D (j + 1 + 1) ∧
    D.host.AA⁻¹ * (dI D * cI D j) = FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j := by
  obtain ⟨-, hA, hB, -⟩ := host_ne_zero D
  have e1 : D.host.AA⁻¹ * (dI D * cI D j) = FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j := by
    rw [dI]
    calc D.host.AA⁻¹ * (FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AA * D.host.AAbar * cI D j)
        = (D.host.AA⁻¹ * D.host.AA) * (FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hA, one_mul]
  refine ⟨?_, e1⟩
  rw [e1]
  have hs := cI_step D h
  calc FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j
      = D.host.AAbar * (FractionalIdeal.spanSingleton _ D.host.xi0 * cI D j) := by ring
    _ = D.host.AAbar * (D.host.AA * D.host.AAbar⁻¹ * cI D (j + 1 + 1)) := by rw [hs]
    _ = (D.host.AAbar * D.host.AAbar⁻¹) * (D.host.AA * cI D (j + 1 + 1)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hB, one_mul]

end GlobalTheory.SeeSaw.ChainIdeals
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.AdaptFBIdeals

variable {D : D7}

theorem supp_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (v : Pl D) (i : Fin ρ) (a : AE D)
    (h : colMul d.jX i a ∈ latV S L (· = v)) : a ∈ idAt D (· = v) := by
  have h1 : (d.pX ⬝ d.jX) i i = 1 := by rw [d.pX_jX]; exact Matrix.one_apply_eq i
  rw [Matrix.mul_apply] at h1
  have h2 : a = ∑ k, d.pX i k * colMul d.jX i a k := by
    calc a = a * ∑ k, d.pX i k * d.jX k i := by rw [h1, mul_one]
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; simp only [colMul]; ring
  rw [h2]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.latV_supp h k)

theorem idV_supp (𝔞 : FI D) (v : Pl D) {a : AE D} (h : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, x, -, rfl⟩ := hy
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem j_zero_mul_mem_lattice_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : Pl D) (hL : MonoAt d L M v)
    (w : Fin S₀.rank → AE D) : d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
  have hc : ∀ {n : ℕ} (x : Mx D S.rank n) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  rw [hL]
  simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
    zero_mem, implies_true, true_and]

end GlobalTheory.SeeSaw.AdaptFBIdeals

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw
end
end
