module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1Coboundary
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.geometric_level_h1_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong (p := p) n (a (g * h)) (a g + g (a h))) →
    ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * a g - o * ((lq g).val : Ω))) ∧
  (∀ o : Ω, IsInt (p := p) o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) → Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => o * ((lq g).val : Ω)) → Cong (p := p) n ((p : Ω) ^ c * o) 0) := by
  exact @GlobalTheory.K5.Reb.h1_geometric_level_coboundary
