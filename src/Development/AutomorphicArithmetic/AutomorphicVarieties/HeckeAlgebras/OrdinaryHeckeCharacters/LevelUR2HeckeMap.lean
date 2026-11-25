module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeCommRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct


theorem UpperTheory.V.Hi.levelUR2HeckeMap :
    ∀ (A M M' ι ι' : Type) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (Y : Submodule A M) (Y' : Submodule A M') (op : ι → Module.End A M) (op' : ι' → Module.End A M') [Fact (CommOn Y op)] [Fact (CommOn Y' op')] (φ : Y →ₗ[A] Y') (j : ι' → ι), Function.Injective φ → (∀ i (y : Y), ((φ ((heckeGen Y op (j i) : Module.End A Y) y) : Y') : M') = op' i (φ y)) → ∃ ψ : heckeAlg Y' op' →ₐ[A] heckeAlg Y op, (∀ i, ψ (heckeGen Y' op' i) = heckeGen Y op (j i)) ∧ ∀ (t : heckeAlg Y' op') (y : Y), φ ((ψ t : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
  intro A M M' ι ι' _ _ _ _ _ Y Y' op op' _ _ φ j hφ hop
  have uniq : ∀ (t : Module.End A Y') (s s' : heckeAlg Y op),
      (∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)) → (∀ y : Y, φ ((s' : Module.End A Y) y) = t (φ y)) → s = s' := by
    intro t s s' h h'
    exact Subtype.ext (LinearMap.ext fun y => hφ ((h y).trans (h' y).symm))
  have ex : ∀ t : heckeAlg Y' op', ∃ s : heckeAlg Y op,
      ∀ y : Y, φ ((s : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
    rintro ⟨t, ht⟩
    change ∃ s : heckeAlg Y op, ∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := hx
      exact ⟨heckeGen Y op (j i), fun y => Subtype.ext ((hop i y).trans (hi (φ y)).symm)⟩
    | algebraMap r =>
      refine ⟨algebraMap A _ r, fun y => ?_⟩
      change φ (r • y) = r • φ y
      exact map_smul φ r y
    | add a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s + s', fun y => ?_⟩
      change φ ((s : Module.End A Y) y + (s' : Module.End A Y) y) = a (φ y) + b (φ y)
      rw [map_add (f := _), hs, hs']
    | mul a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s * s', fun y => ?_⟩
      change φ ((s : Module.End A Y) ((s' : Module.End A Y) y)) = a (b (φ y))
      rw [hs, hs']
  choose f hf using ex
  refine ⟨{ toFun := f
            map_one' := uniq _ _ _ (hf 1) fun y => rfl
            map_mul' := fun a b => uniq _ _ _ (hf (a * b)) fun y => ?_
            map_zero' := uniq _ _ _ (hf 0) fun y => map_zero φ
            map_add' := fun a b => uniq _ _ _ (hf (a + b)) fun y => ?_
            commutes' := fun r => uniq _ _ _ (hf (algebraMap A _ r)) fun y => map_smul φ r y }, fun i => ?_, hf⟩
  · change φ ((f a : Module.End A Y) ((f b : Module.End A Y) y)) = (a : Module.End A Y') ((b : Module.End A Y') (φ y))
    rw [hf, hf]
  · change φ ((f a : Module.End A Y) y + (f b : Module.End A Y) y) = (a : Module.End A Y') (φ y) + (b : Module.End A Y') (φ y)
    rw [map_add (f := _), hf, hf]
  · exact uniq _ _ _ (hf (heckeGen Y' op' i)) fun y => Subtype.ext (hop i y)
