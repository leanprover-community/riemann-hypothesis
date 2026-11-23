module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLevelUnit

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem levJ_grid_succ (G : GridData L sc) (t : T) (i n : ℕ) (hn : n ≠ 0) :
    levJ G t (.grid (i + 1) n) = G.levMax (.grid (i + 1) n) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n => rfl

theorem levJ_grid_zero (G : GridData L sc) (t : T) (n : ℕ) (hn : n ≠ 0) :
    HEq (levJ G t (.grid 0 n)) (levCol L t (n - 1)) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n => exact HEq.rfl

theorem levRow_iff_levJ : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t i (hi : i ≤ D.R.m) (k : FinPt ch.G (.grid i D.R.m)), finG (ch.G.V (.grid i D.R.m)) k ∈ ch.S.toGridChoice.levRow t i hi ↔ finG (ch.G.V (.grid i D.R.m)) k ∈ levJ ch.G t (.grid i D.R.m) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t i hi k => by
    have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
    have hU : finG (ch.G.V (.grid i D.R.m)) k ∈ UA D.sp.cm (ch.G.V (.grid i D.R.m)).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
    suffices e : ch.S.toGridChoice.levRow t i hi ⊓ UA D.sp.cm (ch.G.V (.grid i D.R.m)).gram = levJ ch.G t (.grid i D.R.m) by
      rw [← e]; exact ⟨fun h => ⟨h, hU⟩, fun h => h.1⟩
    clear hU k
    cases i with
    | zero =>
      apply eq_of_heq
      exact (GlobalTheory.T.gridRowLevel_zero_inf_unitary_eq_datumLevel ch.W ch.S.toGridChoice s.core.lev t hi).trans
        ((levJ_grid_zero ch.G t D.R.m hm).trans (levCol_top _ t (j := D.R.m - 1) (by omega))).symm
    | succ i =>
      rw [levJ_grid_succ ch.G t i D.R.m hm]
      exact GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA ch.W ch.S.toGridChoice t i hi⟩⟩

end GlobalTheory.RowLevelUnit
