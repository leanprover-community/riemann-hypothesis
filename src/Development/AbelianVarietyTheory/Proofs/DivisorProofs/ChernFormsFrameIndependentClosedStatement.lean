module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.chernForms_frame_independent_closed : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} (U : κ → Set M),
    (∀ a, IsOpen (U a)) → (∀ y, ∃ a, y ∈ U a) → ∀ (g : κ → κ → M → Matrix ι ι ℂ),
    (∀ a b i j, A.HolOn (U a ∩ U b) fun y => g a b y i j) → ∀ (G : κ → M → Matrix ι ι ℂ),
    (∀ a i j, A.SmoothOn (U a) fun y => G a y i j) → (∀ a, ∀ y ∈ U a, (G a y).PosDef) →
    (∀ a b, ∀ y ∈ U a ∩ U b, G b y = chg (g a b y) (G a y)) → ∀ (j : ℕ),
    (∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x) ∧
    ∀ P : A.Fld, (∀ a (x : A.Pt), x.pt ∈ U a → P x = (A.chern (G a) j x : GlobalTheory.CxForm.Alt n)) →
      A.IsForm P ∧ A.del P = 0 ∧ A.dbar P = 0 := by
  first | exact @GlobalTheory.ChernFrame.chern_frame_closed | exact GlobalTheory.ChernFrame.chern_frame_closed | (intros; apply GlobalTheory.ChernFrame.chern_frame_closed <;> assumption)
