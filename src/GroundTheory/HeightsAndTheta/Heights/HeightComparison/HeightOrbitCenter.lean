module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def ratioField (x : Cone n (AlgebraicClosure ℚ)) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ
    (Set.range fun p : (k : ι) × Fin (n k + 1) × Fin (n k + 1) ↦ x p.1 p.2.1 / x p.1 p.2.2)

theorem ratioField_le_coordField (x : Cone n (AlgebraicClosure ℚ)) :
    ratioField x ≤ coordField x := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨p, rfl⟩
  exact div_mem (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.1⟩, rfl⟩)
    (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.2⟩, rfl⟩)

theorem div_mem_ratioField (x : Cone n (AlgebraicClosure ℚ)) (k : ι) (i j : Fin (n k + 1)) :
    x k i / x k j ∈ ratioField x :=
  IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i, j⟩, rfl⟩

variable [Fintype ι]

instance (x : Cone n (AlgebraicClosure ℚ)) : FiniteDimensional ℚ (ratioField x) :=
  IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral_algebraicClosure_rat y

instance (x : Cone n (AlgebraicClosure ℚ)) : NumberField (ratioField x) := {}

def orbitCenter (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x)) :
    Ideal (MvPolynomial (Coord n) ℤ) :=
  Ideal.span {F | ∃ d : ι → ℕ, Geo.IsMultiHomog (ι := blockIdx n) F d ∧
    v (evalCone (coordVec x) F) < ∏ k, (⨆ i, v (coordVec x k i)) ^ d k}

variable [DecidableEq ι]

theorem X_mem_orbitCenter (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x))
    (k : ι) (i : Fin (n k + 1)) (hi : v (coordVec x k i) < ⨆ j, v (coordVec x k j)) :
    (X ⟨k, i⟩ : MvPolynomial (Coord n) ℤ) ∈ orbitCenter x v := by
  refine Ideal.subset_span ⟨coordDeg n ⟨k, i⟩, (geoMultiHomog_iff _ _).mpr
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, i⟩), ?_⟩
  simpa [evalCone, coordDeg, Pi.single_apply, pow_ite] using hi

end

end GroundTheory.Heights₂.Heights
