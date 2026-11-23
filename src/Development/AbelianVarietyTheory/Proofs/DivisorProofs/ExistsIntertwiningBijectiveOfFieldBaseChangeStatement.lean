module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntertwiningBijectiveOfFieldBaseChange
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


theorem _root_.GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange : ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V'] (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension iV → GlobalTheory.FieldBaseChange.IsExtension iW → ∀ (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W'), (∀ i v, a' i (iV v) = iV (a i v)) → (∀ i w, b' i (iW w) = iW (b i w)) → ∀ E' : V' →ₗ[F] W', Function.Bijective E' → (∀ i v, E' (a' i v) = b' i (E' v)) → ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  first | exact @GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | exact GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | (intros; apply GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension <;> assumption)
