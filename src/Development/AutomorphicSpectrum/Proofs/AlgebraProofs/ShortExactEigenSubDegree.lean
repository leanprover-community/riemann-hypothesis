module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ChSplit
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

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem eigen_ses_subDeg : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ (ρ : O → V →ₗ[K] V) (ρ' : O →+* Module.End K V') (ρ'' : O → V'' →ₗ[K] V''), IsBun C L' → (∀ a, IsHom C L' L' (ρ' a)) → ShortExact C L L' L'' f g → (∀ a x, f (ρ a x) = ρ' a (f x)) → (∀ a y, g (ρ' a y) = ρ'' a (g y)) → ∀ s, subDeg C L' (eig (fun a => ρ' a) (fun a => algebraMap k K (χ s a))) = subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) + subDeg C L'' (eig (fun a => ρ'' a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_ses

end GlobalTheory.CompanionTheory.Ar.Crv
