module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def ub2 (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := -x⁻¹.toBlocks₁₁ + Complex.I • x⁻¹.toBlocks₂₁

def Om (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := ub2 x * (ub1 x)⁻¹

def eQ (m : ℕ) (e : ℤ) (z : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (x : M2 n) : ℂ := fz m e z x * (Om x * Q).trace

def rhoP {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (k : Kg) : ℂ :=
  star (fz m e 0 (ι k) * ((u2 (ι k))⁻¹ * Y * u1 (ι k)).trace)

def LoweringDerivativeVacuum : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (z : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (x : M2 n), InG x → rC (lowQ Q) (fz m e z) x = z * eQ m e z Q x

def MultiplicityOneTestOperators : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n),
    Continuous ψ → HasCompactSupport ψ → InG a → InG b →
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (x : M2 n), InG x →
      tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) x = eQ m e z (c z • Yᴴ) x

def SingularTestsKillVacuum : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ (ρ : Kg → ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n), Continuous ρ →
    IsSingTest ψ → InG a → InG b → InG x → tOp μ ι ρ ψ a b (fz m e 0) x = 0

def Crux : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∃ (P : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n),
      IsSingTest ψ ∧ InG a ∧ InG b ∧ InG x ∧ deriv (fun z => tOp μ ι (rhoP ι m e P) ψ a b (fz m e z) x) 0 ≠ 0

def AsmLT : Prop := LoweringDerivativeVacuum → MultiplicityOneTestOperators → SingularTestsKillVacuum → Crux → LocTau

end PositivityTheory.Rg.Sw.HSt
