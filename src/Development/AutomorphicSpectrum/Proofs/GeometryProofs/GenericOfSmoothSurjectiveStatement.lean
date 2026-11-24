module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjective
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

theorem _root_.GlobalTheory.T.generic_of_smooth_surjective : ∀ (K : Type) [Field K] (X₀ X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀) (s' : X' ⟶ Spec (CommRingCat.of K)), Smooth s' → ξ' ≫ π = ξ → IsCptGen ξ → Function.Surjective (π.stalkMap (genPt ξ')).hom → IsCptGen ξ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | exact GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective <;> assumption)
