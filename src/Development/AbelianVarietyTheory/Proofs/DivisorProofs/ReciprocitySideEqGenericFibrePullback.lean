module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalPrimeDivisorIntegralEqGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibreStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem side_bc_eq : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv G), (∀ x, Δ'.mult x = Δ.mult (j x)) → ∀ (N : MLine p (τ.comp (algebraMap k K))) (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f g : CxPts p (τ.comp (algebraMap k K)) → ℝ), side (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) (fun y => g (bcPt hp.w τ y)) Δ' = side N L f g Δ := by
  intro k K _ _ _ _ X G _ _ _ _ p q j hp τ e hA Δ Δ' hΔ N L f g
  obtain ⟨_, _, _, _, _, hinj, _, hcoh, hemp⟩ := GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) hA
  have hcons : (Fin.cons (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) : Fin (e + 1) → MLine q τ) =
      fun i => ((Fin.cons N L : Fin (e + 1) → MLine p (τ.comp (algebraMap k K))) i).bc hp.w τ := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have h1 := ((GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K X G p q j hp τ (e + 1) hA (Fin.cons N L)).2 f).2
  have hzero : ∀ z : X, z ∉ Set.range j → cycInt L g z = 0 := by
    intro z hz
    haveI := hemp z hz (τ.comp (algebraMap k K))
    simp [cycInt, Mix.int, MeasureTheory.integral_of_isEmpty]
  unfold side
  rw [hcons, h1]
  congr 1
  calc ∑ᶠ x, (Δ'.mult x : ℝ) * cycInt (fun i => (L i).bc hp.w τ) (fun y => g (bcPt hp.w τ y)) x
      = ∑ᶠ x, (Δ.mult (j x) : ℝ) * cycInt L g (j x) := by
        refine finsum_congr fun x => ?_
        rw [hΔ]
        by_cases h : Δ.mult (j x) = 0
        · simp [h]
        · rw [GlobalTheory.T.horizontal_prime_divisor_integral_eq_generic_fibre k K X G p q j hp τ e hA L g x
            (by rw [← hcoh]; exact CartierDiv.coheight_eq_one_of_mult_ne_zero h)]
    _ = ∑ᶠ z ∈ Set.range j, (Δ.mult z : ℝ) * cycInt L g z := (finsum_mem_range (f := fun z => (Δ.mult z : ℝ) * cycInt L g z) hinj).symm
    _ = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L g z := by
        rw [finsum_mem_def]
        refine finsum_congr fun z => ?_
        by_cases hz : z ∈ Set.range j
        · simp [hz]
        · simp [hz, hzero z hz]

end GlobalTheory.Mix
