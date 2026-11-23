module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.AestronglyMeasurablePsiInner
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF

@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def ob3PsiCoef (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (ξ c) (∑ d, (cond dual ((g⁻¹) d c) (g c d)) • Ψ g (ζ d))

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem psi_weighted_memLp {v₀ : T.V} (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (v w : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) := by
  have hC : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h := datumEmbedding_highest_ne_zero hgap hP hv₀
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  have hmem : ∀ u, (⟨uniformisationL2 ε Ψ v₀ u, datumEmbedding_mem_smooth hP v₀ u⟩ : smD ε (rreg ε)) ∈
      genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) := fun u =>
    Submodule.mem_sInf.2 (fun S hS => hS.1 (Submodule.mem_comap.2 (Submodule.subset_span ⟨u, rfl⟩)))
  have h := (hW _ (hmem v) _ (hmem w)).const_mul (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)⁻¹)
  refine h.congr_norm ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact h.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun g => by
      simp only
      rw [formulaF hgap hP hv₀ (g := Formalism.MainNotions.S.umat g) g.2 v w]
      field_simp)
  · simp only
    rw [formulaF hgap hP hv₀ (g := Formalism.MainNotions.S.umat g) g.2 v w]
    congr 1
    field_simp

end Psi

theorem norm_unitary_inv_entry {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖(Formalism.MainNotions.S.umat g)⁻¹ d c‖ = ‖Formalism.MainNotions.S.umat g c d‖ := by
  apply ReciprocityTheory.ChartRestriction.DS.norm_unitary_inv_entry <;> assumption

theorem norm_unitary_entry_le_sqrt_hs {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖Formalism.MainNotions.S.umat g c d‖ ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := by
  apply ReciprocityTheory.ChartRestriction.DS.norm_unitary_entry_le_sqrt_hs <;> assumption

theorem norm_dual_entry_le_sqrt_hs (dual : Bool) {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)‖ ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := by
  cases dual
  · exact norm_unitary_entry_le_sqrt_hs g c d
  · simp only [cond]; rw [norm_unitary_inv_entry]; exact norm_unitary_entry_le_sqrt_hs g c d

theorem continuous_dual_entry (dual : Bool) {ε : Fin n → Bool} (c d : Fin n) :
    Continuous (fun g : Formalism.REAL.UJ ε => cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)) := by
  apply ReciprocityTheory.ChartRestriction.DS.continuous_dual_entry <;> assumption

section Psi2

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem aestronglyMeasurable_psi_inner (hP : IsPsiFor ε lam T Ψ) (x y : T.V) :
    AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)) (Formalism.REAL.muG ε) := by
  have hΨm : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) (Formalism.REAL.muG ε) :=
    (hP.2.2.2.2 (Formalism.REAL.muG ε) (Formalism.REAL.instIsHaarMuG n ε)).aestronglyMeasurable
  exact (continuous_const.inner (continuous_id.clm_apply continuous_const)).comp_aestronglyMeasurable hΨm

theorem psi_inner_memLp (hP : IsPsiFor ε lam T Ψ) (x y : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)) 2 (Formalism.REAL.muG ε) := by
  apply ReciprocityTheory.ChartRestriction.DS.psi_inner_memLp <;> assumption

theorem psi_coef_memLp_of_weighted (dual : Bool) (hP : IsPsiFor ε lam T Ψ)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  apply ReciprocityTheory.ChartRestriction.DS.psi_coef_memLp_of_weighted <;> assumption

theorem psi_pairing_integrable (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) (u' v' : T'.V) :
    Integrable (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
      inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')) (Formalism.REAL.muG ε) :=
  (psi_coef_memLp_of_weighted dual hP hWT ξ ζ).star.integrable_mul (psi_inner_memLp hP' u' v')

end Psi2

theorem clm_mul_apply_eq_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A B : E →L[ℂ] E) (x : E) :
    (A * B) x = A (B x) := rfl

theorem dual_entry_mul_sum (dual : Bool) (K H : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    cond dual ((K * H)⁻¹ d c) ((K * H) c d) =
      ∑ e, cond dual (K⁻¹ e c) (K c e) * cond dual (H⁻¹ d e) (H e d) := by
  cases dual
  · simp only [cond, Matrix.mul_apply]
  · simp only [cond, Matrix.mul_inv_rev, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _

section Psi3

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem psi_k_left_equivariant {Λ : Fin n → ℝ} {T : S7.KType ε Λ} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hK : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂) (k : S7.KG ε) (h : Formalism.REAL.UJ ε) :
    Ψ (S7.toMK k * Formalism.MainNotions.S.umat h) = T.op k * Ψ (Formalism.MainNotions.S.umat h) := by
  have e := hK k 1 (Formalism.MainNotions.S.umat h) h.2
  have h1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
  have h2 : T.op 1 = 1 := by simp [S7.KType.op]
  rwa [h1, mul_one, h2, mul_one] at e

theorem psi_coef_k_left_translate (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (k : S7.KG ε) (h : Formalism.REAL.UJ ε)
    (ξ ζ : Fin n → T.V) :
    ob3PsiCoef dual Ψ ξ ζ (S7.toMK k * Formalism.MainNotions.S.umat h) =
      ob3PsiCoef dual Ψ (fun e => ∑ c, starRingEnd ℂ (cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e)) •
        (ContinuousLinearMap.adjoint (T.op k)) (ξ c)) ζ (Formalism.MainNotions.S.umat h) := by
  apply ReciprocityTheory.ChartRestriction.DS.psi_coef_k_left_translate <;> assumption

theorem psi_pairing_vanishing_spread (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') {v₀' : T'.V} (hv₀' : v₀' ≠ 0)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (h0 : ∀ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0) :
    ∀ (ξ ζ : Fin n → T.V) (u' v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.psi_pairing_vanishing_spread <;> assumption

end Psi3

end ReciprocityTheory.ChartRestriction.DS.G2
