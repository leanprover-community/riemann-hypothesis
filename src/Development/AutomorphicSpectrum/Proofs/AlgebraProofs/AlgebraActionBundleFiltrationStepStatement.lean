module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistApply
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgebraActionBundleFiltrationStep
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem _root_.GlobalTheory.T.algebra_action_bundle_filtration_step : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (k A : Type) [Field k] [Algebra k K] [CommRing A] [Algebra k A] (τ : A →+* Module.End K V) (r : ℕ) (χ : A →ₐ[k] k) (J₁ J : Ideal A) (t : A) (l : A →ₗ[k] k), IsBun C L → (∀ a, IsHom C L L (τ a)) → (∀ (c : k) (x : V), τ (algebraMap k A c) x = algebraMap k K c • x) → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → (∀ i, FreeAt C k τ L r i) → J₁ ≤ J → t ∈ J → (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) → (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) → (∀ a ∈ J₁, l a = 0) → l t = 1 → subDeg C L (idealV τ J) = subDeg C L (idealV τ J₁) + deg C (quot C L (idealV τ (RingHom.ker χ))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep.subDeg_step | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep.subDeg_step | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep.subDeg_step <;> assumption)
