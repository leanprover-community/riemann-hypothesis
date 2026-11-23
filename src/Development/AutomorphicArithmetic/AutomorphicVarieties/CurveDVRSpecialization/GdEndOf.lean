module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyClauseStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.NumberTheory.NumberField.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem fix_iff {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] (hK : Module.finrank ℚ K = 2)
    (f g : K →+* Ω) (s : Ω ≃ₐ[ℚ] Ω) (h : ∀ x, s (f x) = f x) (x : K) : s (g x) = g x := by
  by_cases hq : ∃ q : ℚ, (q : K) = x
  · obtain ⟨q, rfl⟩ := hq
    simp only [map_ratCast]
  · have hli : LinearIndependent ℚ ![(1 : K), x] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      by_cases hb : b = 0
      · subst hb
        simp at hab
        exact ⟨hab, rfl⟩
      · exfalso
        apply hq
        refine ⟨-a / b, ?_⟩
        rw [Rat.smul_def, Rat.smul_def, mul_one] at hab
        have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
        push_cast
        rw [div_eq_iff hb']
        linear_combination -hab
    have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hK])
    have hmem : x * x ∈ Submodule.span ℚ (Set.range ![(1 : K), x]) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Submodule.mem_span_pair] at hmem
    obtain ⟨a, b, hab⟩ := hmem
    rw [Rat.smul_def, Rat.smul_def, mul_one] at hab
    have hg : g x * g x = a + b * g x := by
      rw [← map_mul, ← hab, map_add (f := _), map_mul, map_ratCast, map_ratCast]
    have hf : f x * f x = a + b * f x := by
      rw [← map_mul, ← hab, map_add (f := _), map_mul, map_ratCast, map_ratCast]
    have hprod : (g x - f x) * (g x - ((b : Ω) - f x)) = 0 := by
      linear_combination hg - hf
    rcases mul_eq_zero.mp hprod with h1 | h1
    · rw [sub_eq_zero.mp h1, h x]
    · have h2 : g x = f ((b : K) - x) := by
        rw [sub_eq_zero.mp h1, map_sub, map_ratCast]
      rw [h2, h]
