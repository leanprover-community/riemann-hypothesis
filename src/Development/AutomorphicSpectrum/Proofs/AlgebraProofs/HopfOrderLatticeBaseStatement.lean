module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderLatticeBase
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

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

theorem _root_.GlobalTheory.T.hopf_order_lattice_base : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk | exact GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk <;> assumption)
