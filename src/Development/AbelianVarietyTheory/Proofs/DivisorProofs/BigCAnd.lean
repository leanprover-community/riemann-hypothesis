module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory.BigConstantConjunction

theorem bigC_and : ∀ {Q Q' : GlobalTheory.SumSize.ChQ}, (GlobalTheory.SumSize.BigC fun {D : Formalism.BasicNotions.D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Γ Pl0 T (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D))] {R : Formalism.IndefR.Links.RealDat D A Ks} ↦ Q) → (GlobalTheory.SumSize.BigC fun {D : Formalism.BasicNotions.D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Γ Pl0 T (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D))] {R : Formalism.IndefR.Links.RealDat D A Ks} ↦ Q') → GlobalTheory.SumSize.BigC fun {D : Formalism.BasicNotions.D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Γ Pl0 T (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D))] {R : Formalism.IndefR.Links.RealDat D A Ks} (F : Formalism.IndefR.Links.Face D A) (ch : GlobalTheory.RowTest.Choice R) (C b : ℝ) ↦ Q F ch C b ∧ Q' F ch C b := by
  intro Q Q' h h'
  obtain ⟨A0, hA⟩ := h
  obtain ⟨B0, hB⟩ := h'
  refine ⟨max A0 B0, fun CF hCF => ?_⟩
  obtain ⟨C1, hC1⟩ := hA CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, hC2⟩ := hB CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, fun ε C hC => ?_⟩
  obtain ⟨x1, hx1⟩ := hC1 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x2, hx2⟩ := hC2 ε C (le_trans (le_max_right _ _) hC)
  refine ⟨max x1 x2, ?_⟩
  intro D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hOK
  exact ⟨hx1 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hOK,
    hx2 D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hOK⟩

end GlobalTheory.BigConstantConjunction
