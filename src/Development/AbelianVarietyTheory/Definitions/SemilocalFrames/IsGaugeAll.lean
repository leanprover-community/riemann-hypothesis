module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def flagAt (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) :
    Fin (a + 1) → Submodule ℂ (Fin I.n → ℂ) :=
  fun i => Submodule.span ℂ ((fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) '' (S i : Set _))

def IsSatFlag (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  S 0 = ⊥ ∧ Monotone S ∧ (∀ i : Fin a, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i) ∧
    (∀ i, ∀ y, y ∈ S i ↔ y ∈ Λ ∧ y ∈ Submodule.span I.E (S i : Set (Fin I.n → I.E))) ∧
    ∀ x ∈ S (Fin.last a), ∀ y ∈ S (Fin.last a), Formalism.UG.hform (starRingEnd I.E) I.J x y = 0

def IsGaugeAll (I : AutInst) (c : InfinitePlace I.F → ℝ) : Prop := ∀ v, IsGauge (I.ε v) (c v)

def cIw (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℝ :=
  (2 : ℝ) ^ (-((dimN (p + q) j : ℝ) / 2)) * (volU p * volU q) /
    ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) * volU (q - ∑ i, j i))

def rankFac (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) : ℝ :=
  (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ((M : ℝ) - 1 / 2)) * Formalism.HermitianLatticesTheory.lValEta E M

end GlobalTheory.FlagMeas
