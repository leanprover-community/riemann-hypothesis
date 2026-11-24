module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchange
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

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.levelDatum_idempotent_rank_le_root_exchange : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = true → L'.sharp = true → L.k = L'.k → L.s = L'.s + 1 → rk ρ L'.e ≤ rk ρ L.e := by
  first | exact @GlobalTheory.BadShare.RxStep.rk_le_step | exact GlobalTheory.BadShare.RxStep.rk_le_step | (intros; apply GlobalTheory.BadShare.RxStep.rk_le_step <;> assumption)
