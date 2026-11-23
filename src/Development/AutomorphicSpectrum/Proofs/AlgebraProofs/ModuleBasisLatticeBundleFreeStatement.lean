module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistApply
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleBasisLatticeBundleFree
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

theorem _root_.GlobalTheory.T.module_basis_lattice_bundle_free : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O ι k : Type) [CommRing O] [Fintype ι] [Field k] [Algebra k K] (b : Module.Basis ι ℤ O) (ρ : O →+* Module.End K V) (r : ℕ) (i : C.I), IsBun C L → (∀ c : k, C.v i (algebraMap k K c) ≤ 1) → (∃ x : Fin r → V, LinearIndependent K (fun q : Fin r × ι => ρ (b q.2) (x q.1)) ∧ ∀ y, y ∈ L i ↔ ∃ c : Fin r × ι → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • ρ (b q.2) (x q.1)) → FreeAt C k (act k ρ) L r i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice <;> assumption)
