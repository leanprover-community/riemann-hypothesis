module

public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.ExpOneParam

theorem continuous_expG_and_toM_inv :
    ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Z →
      Continuous (fun t : ℝ => Formalism.REAL.expG ε Z t) ∧
        ∀ t : ℝ, Formalism.REAL.toM (Formalism.REAL.expG ε Z t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
  intro n ε Z hZ
  obtain ⟨h0, hadd, hcont, -⟩ := Formalism.REAL.group_exponential_facts n ε Z hZ
  refine ⟨hcont, fun t => ?_⟩
  have hinv : (Formalism.REAL.expG ε Z t)⁻¹ = Formalism.REAL.expG ε Z (-t) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← hadd, neg_add_cancel, h0]
  rw [hinv, Formalism.REAL.toM_expG ε Z (-t) hZ, Complex.ofReal_neg, neg_smul]

end GlobalTheory.CompanionTheory.ExpOneParam
