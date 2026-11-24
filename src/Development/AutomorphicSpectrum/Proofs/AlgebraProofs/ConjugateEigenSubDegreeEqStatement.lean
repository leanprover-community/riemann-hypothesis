module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEigenSubDegreeEq
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

theorem _root_.GlobalTheory.T.conjugate_eigen_sub_degree_eq : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ s t : S, (∀ a, χ t a = χ s (star a)) → subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) = subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj | exact GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj <;> assumption)
