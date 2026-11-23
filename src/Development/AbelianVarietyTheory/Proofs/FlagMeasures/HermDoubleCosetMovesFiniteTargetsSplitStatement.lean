module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMovesFiniteTargetsSplit
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

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → {Λ₁ : Submodule L.O S.V | ∃ w, S.MvTo (j + 1) d Λ Λ₁ w}.Finite ∧ (∀ Λ₁, Nice (S.refA (j + 1) Λ) (ind (S.MvTo (j + 1) d Λ Λ₁))) ∧ {Λ₁ | S.kern β (j + 1) βJ d Λ Λ₁ ≠ 0}.Finite ∧ (∀ Λ₁, 0 ≤ S.kern β (j + 1) βJ d Λ Λ₁) ∧ ∀ (P : Submodule L.O S.V → Prop) (g : Submodule L.O S.V → ℂ) (G : S.MW → ℂ), (∀ w Λ₁, S.MvTo (j + 1) d Λ Λ₁ w → G w = if P Λ₁ then g Λ₁ else 0) → (∀ w, ¬ S.Mv (j + 1) d Λ w → G w = 0) → Nice (S.refA (j + 1) Λ) G ∧ ∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * g y = (S.cK β βJ : ℂ) * cint (S.refA (j + 1) Λ) G := by
  first | exact @GlobalTheory.HL.moves_split_by_target | exact GlobalTheory.HL.moves_split_by_target | (intros; apply GlobalTheory.HL.moves_split_by_target <;> assumption)
