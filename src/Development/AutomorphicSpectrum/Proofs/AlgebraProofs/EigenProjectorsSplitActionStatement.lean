module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitAction
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

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.eigen_projectors_split_action : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → ∃ e : S → Module.End K V, (∀ s, IsHom C L L (e s)) ∧ (∀ s x, e s x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)))) ∧ (∀ s, ∀ x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))), e s x = x) ∧ (∀ x, ∑ s, e s x = x) ∧ ∀ s, ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O), (∀ t, ∑ j, c j * χ t (a j) = if t = s then 1 else 0) ∧ e s = ∑ j, algebraMap k K (c j) • ρ (a j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj | exact GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj <;> assumption)
