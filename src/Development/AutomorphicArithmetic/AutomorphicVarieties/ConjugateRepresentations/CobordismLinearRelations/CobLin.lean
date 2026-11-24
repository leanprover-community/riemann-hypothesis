module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem geo_hd_smul_add {Γ M : Type} [AddCommGroup M] [Module ℂ M] (s : ℂ)
    (b b' : List Γ → M) (x : List Γ) :
    UpperTheory.V.Lit.Geo.hd (s • b + b') x =
      s • UpperTheory.V.Lit.Geo.hd b x + UpperTheory.V.Lit.Geo.hd b' x := by
  unfold UpperTheory.V.Lit.Geo.hd
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, Pi.smul_apply, smul_add, smul_comm]

theorem UpperTheory.V.Cj.cobLin :
    UpperTheory.V.Cj.CobLin := by
  intro Γ M _ _ _ ρ q s c c' hc hc'
  cases q with
  | zero =>
    simp only [UpperTheory.V.Lit.Geo.HCob] at hc hc' ⊢
    intro x hx
    rw [Pi.add_apply, Pi.smul_apply, hc x hx, hc' x hx, smul_zero, add_zero]
  | succ k =>
    simp only [UpperTheory.V.Lit.Geo.HCob] at hc hc' ⊢
    obtain ⟨b, hbe, hbc⟩ := hc
    obtain ⟨b', hbe', hbc'⟩ := hc'
    refine ⟨s • b + b', fun γ x hx => ?_, fun x hx => ?_⟩
    · rw [Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, hbe γ x hx, hbe' γ x hx,
        map_add, map_smul]
    · rw [geo_hd_smul_add, Pi.add_apply, Pi.smul_apply, hbc x hx, hbc' x hx]
