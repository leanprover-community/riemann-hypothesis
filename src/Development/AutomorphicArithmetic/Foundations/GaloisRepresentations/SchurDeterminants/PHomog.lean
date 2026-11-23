module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMulOfIsHomogeneous
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurHomogeneous
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem aeval_mul_of_isHomogeneous {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℚ R]
    {P : MvPolynomial σ ℚ} {d : ℕ} (hP : P.IsHomogeneous d) (y : R) (g : σ → R) :
    aeval (fun k => y * g k) P = y ^ d * aeval g P :=
  _root_.UpperTheory.Reformulated.B.Qh65.aeval_mul_of_isHomogeneous hP y g

theorem schurHomog : SchurHomog := by
  intro R _ _ n lam g y
  unfold sch
  exact aeval_mul_of_isHomogeneous
    (GroundTheory.Heights₂.Heights.RestTerms.SchSchurHomogeneous.proof (Fin n) n lam) y g

end UpperTheory.Gal.Schur
