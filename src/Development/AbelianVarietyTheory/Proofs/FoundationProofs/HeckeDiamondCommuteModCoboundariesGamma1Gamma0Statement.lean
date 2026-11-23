module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDiamondCommuteModCoboundariesGamma1Gamma0
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0 : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → Odd k →
  ∀ (q q' : ℕ) (σ σ' τ τ' : SL(2, ℤ)) (d d' : ZMod N), q.Prime → ¬ q ∣ N * l → q'.Prime → ¬ q' ∣ N * l →
   IsDiam N l (q : ZMod N) σ → IsDiam N l (q' : ZMod N) σ' → IsDiam N l d τ → IsDiam N l d' τ' →
   ∀ z ∈ Z1 (Lev N l) (k - 2),
    TqZ (Lev N l) (k - 2) q σ (TqZ (Lev N l) (k - 2) q' σ' z) - TqZ (Lev N l) (k - 2) q' σ' (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (UlZ (Lev N l) (k - 2) l z) - UlZ (Lev N l) (k - 2) l (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    UlZ (Lev N l) (k - 2) l (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (UlZ (Lev N l) (k - 2) l z) ∈ B1 (Lev N l) (k - 2) ∧
    DdZ (Lev N l) (k - 2) τ (DdZ (Lev N l) (k - 2) τ' z) - DdZ (Lev N l) (k - 2) τ' (DdZ (Lev N l) (k - 2) τ z) ∈ B1 (Lev N l) (k - 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt | exact GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt | (intros; apply GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt <;> assumption)
