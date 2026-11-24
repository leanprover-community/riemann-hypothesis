module

public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SchrodingerModelSelfDualLattice
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

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

theorem _root_.GlobalTheory.T.indicator_in_schrodinger_span : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {κ : Type} [Fintype κ] (v : Rˣ), GoodChar ψ O u → (v : R) ∈ O → (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) ∈ Submodule.span ℂ {f : (κ → R) → ℂ | ∃ y : κ → R, f = schr ψ (0, y) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ))} := by
  first | exact @GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | exact GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | (intros; apply GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span <;> assumption)
