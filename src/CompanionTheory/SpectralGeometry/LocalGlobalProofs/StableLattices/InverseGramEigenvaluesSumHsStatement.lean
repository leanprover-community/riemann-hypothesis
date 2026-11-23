module

public import Formalism.RealPlaceAnalysis.Complexify
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix ReciprocityTheory.ChartRestriction.DS

open scoped ComplexOrder in
theorem GlobalTheory.T.inverse_gram_eigenvalues_sum_hs (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε)
    (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) :
    (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) := by
  have hmul : S7.toM g * S7.toM g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = 1
    simp
  have hinj : Function.Injective (S7.toM g⁻¹).mulVec := by
    intro x y hxy
    have h := congrArg (S7.toM g).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hmul] using h
  have hpd : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ hinj
  refine ⟨fun i => hpd.eigenvalues_pos i, ?_⟩
  have hre : ∑ i, hT.eigenvalues i = (Matrix.trace ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹)).re := by
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
      (congrArg Complex.re hT.trace_eq_sum_eigenvalues).symm
  have hs_ct (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs Mᴴ = Formalism.REAL.hs M := by
    delta Formalism.REAL.hs
    simp only [Matrix.conjTranspose_apply, norm_star]
    exact Finset.sum_comm
  have hs_j_left (M : Matrix (Fin n) (Fin n) ℂ) :
      Formalism.REAL.hs (Formalism.REAL.Jm ε * M) = Formalism.REAL.hs M := by
    have h : ∀ a, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
    delta Formalism.REAL.hs Formalism.REAL.Jm
    simp only [Matrix.diagonal_mul, norm_mul, h, one_mul]
  have hs_j_right (M : Matrix (Fin n) (Fin n) ℂ) :
      Formalism.REAL.hs (M * Formalism.REAL.Jm ε) = Formalism.REAL.hs M := by
    rw [← hs_ct, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose, hs_j_left, hs_ct]
  have hhs : Formalism.REAL.hs (S7.toM g⁻¹) = Formalism.REAL.hs (S7.toM g) := by
    rw [S7.toM_inv]
    show Formalism.REAL.hs (Formalism.REAL.Jm ε * (S7.toM g)ᴴ * Formalism.REAL.Jm ε) = _
    rw [hs_j_right, hs_j_left, hs_ct]
  rw [hre, ← Formalism.REAL.f1auxiliary_hs_eq, hhs]

theorem GlobalTheory.CompanionTheory.UGeo.specpos_inv_eigenvalues (n : ℕ) (ε : Fin n → Bool)
    (g : S7.UJ ε) (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) :
    (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) :=
  GlobalTheory.T.inverse_gram_eigenvalues_sum_hs n ε g hT
