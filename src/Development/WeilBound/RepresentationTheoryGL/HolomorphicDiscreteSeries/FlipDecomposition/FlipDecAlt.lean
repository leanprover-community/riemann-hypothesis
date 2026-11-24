module

public import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Matrix Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

def Facts {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (X : Dec ε lam π) : Prop :=
  (∀ s, s ∈ X.S ↔ Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1)) ∧ ∀ s, X.κ s = (lam s : ℂ) + ((m : ℂ) - 1) / 2

def DecLe : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)), (∃ a, ε a = false) →
    (univ.filter fun a => ε a = false).card ≤ (univ.filter fun a => ε a = true).card →
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam π → Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3) →
    ∃ X : Dec ε lam π, Facts X

def FlipDS : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)), IsDS (fun a => !ε a) lam σ ↔ IsDS ε lam σ

def FlipDec : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (X : Dec (fun a => !ε a) lam π), Facts X → ∃ Y : Dec ε lam π, Facts Y

end PositivityTheory.RgHe.Dec
