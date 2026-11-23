module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KFourier

theorem orth_translate_lowV {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (p κ : KG ε → ℂ) (hκ : κ ∈ lowV ε i)
    (h : ∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) (k : KG ε) :
    ∫ x, star (p x) * κ (x⁻¹ * k) ∂(muK ε) = 0 := by
  cases i with
  | zero =>
    have h0 : κ = 0 := by simpa [lowV] using hκ
    subst h0
    simp
  | succ i =>
    have hq : (fun x : KG ε => star (κ (x⁻¹ * k))) ∈ lowV ε (i + 1) := by
      have h1 : κ ∈ polyV ε i := hκ
      have h2 := mul_right_mem k h1
      have h3 := inv_mem h2
      exact star_mem h3
    have h4 := h _ hq
    have h5 : ∫ x, star (star (κ (x⁻¹ * k)) * p x) ∂(muK ε) = 0 := by
      have := congrArg star h4
      rw [star_zero] at this
      rw [← this]
      exact integral_conj
    rw [← h5]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [star_mul', star_star]
    ring

end GlobalTheory.KFourier
