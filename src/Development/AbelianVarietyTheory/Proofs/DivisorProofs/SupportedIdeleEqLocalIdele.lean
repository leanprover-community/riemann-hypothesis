module

public import ReciprocityTheory.NeutralLocalFields.Reciprocity
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.Div.SuppIdele

theorem snd_apply_mul {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : AdeleRing (𝓞 K) K) : (a * b).2 v = a.2 v * b.2 v := rfl

theorem supported_eq_localIdele : ∀ {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {a : Ideles K},
    IsSupportedAt K a v → ∃ x : (v.adicCompletion K)ˣ, (x : v.adicCompletion K) = (a : AdeleRing (𝓞 K) K).2 v ∧
      localIdele K v x = a := by
  intro K _ _ v a ha
  classical
  let x : (v.adicCompletion K)ˣ :=
    { val := (a : AdeleRing (𝓞 K) K).2 v
      inv := ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v
      val_inv := by
        rw [← snd_apply_mul, Units.mul_inv]; rfl
      inv_val := by
        rw [← snd_apply_mul, Units.inv_mul]; rfl }
  refine ⟨x, rfl, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext w
    exact (ha.1 w).symm
  · apply RestrictedProduct.ext
    intro w
    by_cases hw : w = v
    · subst hw
      exact (localIdele_snd_self K w x).trans rfl
    · exact ((localIdele_isSupportedAt K v x).2 w hw).trans (ha.2 w hw).symm

end GlobalTheory.Div.SuppIdele
