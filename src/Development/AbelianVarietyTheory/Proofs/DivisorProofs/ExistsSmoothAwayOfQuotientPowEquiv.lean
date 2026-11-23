module

public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSmoothAtOfSmoothModIdealPowers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SmoothAdic

open TensorProduct

theorem exists_smooth_away_of_quotient_pow_equiv : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (O C : Type) [CommRing O] [Algebra R O] [CommRing C] [Algebra R C], Algebra.Smooth R O → Algebra.FiniteType R C → (∀ e : ℕ, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)))) → ∀ q : Ideal C, q.IsPrime → q.comap (algebraMap R C) = maximalIdeal R → ∃ g : C, g ∉ q ∧ Algebra.Smooth R (Localization.Away g) := by
  intro R _ _ _ O C _ _ _ _ hO hC hiso q hq hqm
  have hsm : ∀ e : ℕ, Algebra.Smooth (R ⧸ maximalIdeal R ^ (e + 1))
      (TensorProduct R (R ⧸ maximalIdeal R ^ (e + 1)) C) := by
    intro e
    obtain ⟨φ⟩ := hiso e
    let J := maximalIdeal R ^ (e + 1)
    let φ' : (O ⧸ J.map (algebraMap R O)) ≃ₐ[R ⧸ J] (C ⧸ J.map (algebraMap R C)) :=
      AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective φ
    let ψ : ((R ⧸ J) ⊗[R] O) ≃ₐ[R ⧸ J] ((R ⧸ J) ⊗[R] C) :=
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor O J).symm.trans φ').trans
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C J)
    exact Algebra.Smooth.of_equiv ψ
  haveI := hq
  haveI : Algebra.IsSmoothAt R q :=
    isSmoothAt_of_smooth_quotient_pow R (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top C hsm q hqm
  haveI : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.mp hC
  obtain ⟨g, hg, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R q
  exact ⟨g, hg, hs⟩

end GlobalTheory.SmoothAdic
