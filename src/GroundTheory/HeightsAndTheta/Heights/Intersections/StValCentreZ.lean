module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def IsValCentre {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) [P.IsPrime]
    (R : ValuationSubring (FractionRing (MRing ι ⧸ P))) (y : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime y ∧ P ≤ y ∧
    ∀ (b : K → ℕ) (f g : MRing ι), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) ∈ R ∧
        (f ∈ y ↔ algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) ∈ R.nonunits)

def ValCentreZ.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (hP : IsMultiProjPrime P),
    haveI := hP.1
    ∀ R : ValuationSubring (FractionRing (MRing ι ⧸ P)), ∃ y : Ideal (MRing ι), IsValCentre P R y

end GroundTheory.Heights₂.Heights.Inter
