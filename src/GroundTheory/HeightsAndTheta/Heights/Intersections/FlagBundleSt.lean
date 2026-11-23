module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
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

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Gen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_comp_X {σ A B : Type} [CommRing A] [CommRing B] {_ : Algebra ℤ B}
    (φ : MvPolynomial σ ℤ →+* A) (e : A →+* B) (f : MvPolynomial σ ℤ) :
    aeval (fun q => e (φ (X q))) f = e (φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (eq_intCast (algebraMap ℤ B) a).trans (eq_intCast ((e.comp φ).comp C) a).symm
  | add p q hp hq => rw [map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p q hp => rw [map_mul, hp, aeval_X, map_mul, map_mul]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_genPt (P : Ideal (MRing ι)) {_ : Algebra ℤ (FnField P)} (f : MRing ι) :
    aeval (genPt P) f = algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f) :=
  aeval_comp_X (Ideal.Quotient.mk P) (algebraMap (MRing ι ⧸ P) (FnField P)) f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ker_algebraMap_comp_mk (P : Ideal (MRing ι)) :
    RingHom.ker ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) = P := by
  rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (MRing ι ⧸ P) (FnField P)), Ideal.mk_ker]

end Gen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
