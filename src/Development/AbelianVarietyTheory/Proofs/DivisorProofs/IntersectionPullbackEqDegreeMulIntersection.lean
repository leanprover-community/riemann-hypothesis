module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackNotSurjectiveEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackIsogenyEqDegreeMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_eq_deg_mul_inter : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left,
      inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  intro K _ A B f hd J _ hJ c
  by_cases hi : IsIsogeny f
  · exact GlobalTheory.T.intersection_pullback_isogeny_eq_degree_mul K A B f hi J hJ c
  · have hs : ¬ Surjective f.hom.left := by
      intro hs
      exact hi ⟨GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq K A B f hd hs, hs⟩
    rw [GlobalTheory.T.intersection_number_pullback_not_surjective_eq_zero K A B f hd hs J hJ c, deg, if_neg hi]
    simp

end GlobalTheory.AV.AbVar
