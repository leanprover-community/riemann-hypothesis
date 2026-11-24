module

public import Formalism.HermitianCurvature.StatementG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.RealPlaceAnalysis.StatementA

@[expose] public section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem norm_eq_of_pow_eq_same {s : ℕ} (hs : 0 < s) {a z z₀ : ℂ} (hz : z ^ s = a) (hz₀ : z₀ ^ s = a) : ‖z‖ = ‖z₀‖ := by
  have h : ‖z‖ ^ s = ‖z₀‖ ^ s := by rw [← norm_pow, ← norm_pow, hz, hz₀]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hs.ne').mp h

theorem mem_rootSet_iff_pow_eq {s : ℕ} (hs : 0 < s) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by
  rw [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots hs]

theorem germ_leading_term_root_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Ψ : G.Mat (m + 1 + 1) → V) (t Dd z₀ : ℂ) (hz₀ : z₀ ^ (m + 2) = (-1) ^ (m + 3) * Dd) :
    G.mainTerm β m (fun _ => 1) Ψ t Dd =
      (((m : ℂ) + 2)⁻¹ * ((‖z₀‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ)) •
        ∑ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dd), G.psi β (((m : ℂ) + 2) * z / t) • G.OmLong β (m + 1) Ψ z := by
  unfold G.mainTerm
  rw [mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [mem_rootSet_iff_pow_eq (by omega)] at hz
  rw [norm_eq_of_pow_eq_same (by omega) hz hz₀, mul_one, mul_smul]

end Formalism.FourierDecayAlt.P
