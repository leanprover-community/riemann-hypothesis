module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CuspProjectionOrthogonality
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PosSemidefWeightedInnerNonneg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaFA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix

@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem psi_coef_expand (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) :
    ob2PsiCoef dual Ψ ξ ζ g = ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (ξ c) (Ψ g (ζ d)) := by
  simp only [ob2PsiCoef, inner_sum, inner_smul_right, oa1Phi]

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem continuous_spherical_psi (hP : IsPsiFor ε lam T Ψ) :
    Continuous (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) :=
  (ffa_continuousOn hP.2.2.1).comp_continuous continuous_umat' (fun g => g.2)

theorem psi_twist_coef_memLp (dual : Bool) (hP : IsPsiFor ε lam T Ψ)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  apply ReciprocityTheory.ChartRestriction.DS.psi_twist_coef_memLp <;> assumption

theorem psi_term_integrable (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) (u v : T'.V) :
    Integrable (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
      inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) (Formalism.REAL.muG ε) := by
  have h1 := (psi_twist_coef_memLp dual hP hWT ξ ζ).star
  have h2 : MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) :=
    memLp_muG_of_haar ε (fun x => inner ℂ u (Ψ' x v)) 2
      (fun μ hμ => (pdA_coef u v).comp_memLp' (hP'.2.2.2.2 μ hμ))
  exact h1.integrable_mul h2

end Psi

theorem psi_twist_at_one (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (hΨ : Ψ 1 = 1) (u : Fin n → T.V) :
    ob2B dual Ψ 1 u = u := by
  apply ReciprocityTheory.ChartRestriction.DS.psi_twist_at_one <;> assumption

section Main

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

def ob2Fij (dual : Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V))
    (Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)) (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V))
    (i j : Fin (Module.finrank ℂ T'.V)) (g : Formalism.REAL.UJ ε) : ℂ :=
  starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
    (Formalism.MainNotions.S.umat g)) *
  inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))

theorem psi_pairing_at_one_re_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0) :
    0 < (∑ i, ∑ j, ob2Fij (ε := ε) dual Ψ Ψ' ι₀ i j 1).re := by
  apply ReciprocityTheory.ChartRestriction.DS.psi_pairing_at_one_re_pos <;> assumption

theorem continuous_psi_pairing_sum (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) :
    Continuous (fun g : Formalism.REAL.UJ ε => ∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) := by
  apply ReciprocityTheory.ChartRestriction.DS.continuous_psi_pairing_sum <;> assumption

theorem psi_pairing_trace_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0)
    (hK : ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = ob2TauF dual T k (ι₀ v)) :
    0 < (∑ i, ∑ j, ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
        (Formalism.MainNotions.S.umat g)) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))
        ∂(Formalism.REAL.muG ε)).re := by
  apply ReciprocityTheory.ChartRestriction.DS.psi_pairing_trace_pos <;> assumption

end Main

end ReciprocityTheory.ChartRestriction.DS.G2
