module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.CptLift

theorem isCptGen_of_smooth_of_surjective : ∀ (K : Type) [Field K] (X₀ X' : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀)
    (s' : X' ⟶ Spec (CommRingCat.of K)), Smooth s' → ξ' ≫ π = ξ → IsCptGen ξ →
    Function.Surjective (π.stalkMap (genPt ξ')).hom → IsCptGen ξ' := by
  intro K _ X₀ X' Ω _ ξ ξ' π s' hs hc hξ hsurj
  subst hc
  have hd : ∀ x : X', IsDomain (X'.presheaf.stalk x) := fun x =>
    GroundTheory.Arith.SchemeCoh.isDomain_stalk_of_smooth_field s' x
  have hcomp : (Scheme.stalkClosedPointTo (ξ' ≫ π)).hom =
      (Scheme.stalkClosedPointTo ξ').hom.comp (π.stalkMap (genPt ξ')).hom :=
    congrArg (fun t => t.hom) (Scheme.stalkClosedPointTo_comp ξ' π)
  have hbij : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom := by
    have hb := hξ.bij
    rw [hcomp] at hb
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · obtain ⟨a', rfl⟩ := hsurj a
      obtain ⟨b', rfl⟩ := hsurj b
      exact congrArg _ (hb.1 hab)
    · obtain ⟨a, ha⟩ := hb.2 c
      exact ⟨_, ha⟩
  refine ⟨hbij, fun p => ?_⟩
  have hinj : Function.Injective (X'.presheaf.stalkSpecializes p.2).hom := by
    haveI := hd (genPt ξ')
    exact GlobalTheory.PushInv.stalkSpecializes_injective p.2
  intro a b hab
  exact hinj (hbij.1 hab)

end GlobalTheory.CompanionTheory.Ar.CptLift
