module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassCupProductGeometric
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.edge_class_cup_product_geometric : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ c₁ : ℕ, ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ (x y lz lq η : Gal p Ω → ZMod (p ^ n)) (f : Ω),
  (∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h) →
  IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq → IsInt (p := p) f → (∀ g ∈ Gn T L, g f = f) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c₁ * (((x g).val : Ω) * ((y h).val : Ω)) + (p : Ω) ^ c₁ * f * (((lz g).val : Ω) * ((lq h).val : Ω))) →
  ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L,
    Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun h => (p : Ω) ^ c * ((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : Ω) - (σ⁻¹ o - o - (p : Ω) ^ c * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)) := by
  first | exact @GlobalTheory.EdgeAlg.edge_class_cup | exact GlobalTheory.EdgeAlg.edge_class_cup | (intros; apply GlobalTheory.EdgeAlg.edge_class_cup <;> assumption)
