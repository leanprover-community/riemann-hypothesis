module

public import Development.EtaleCohomology.TateTwists.EtaleCohomologyOperationCompOfImageSpec
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_semilinear_cohomology_operation_image_spec_of_hyp
    (hImage₂ : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
      (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
      ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
        ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β) :
    EtaleSemilinearCohomologyOperationImageSpec :=
  hImage₂

end LateralTheory.EtaleFoundations
