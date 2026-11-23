module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDataLocalPureTensorsLargeDepth
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.rowData_localPureTensors_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fr : SchRow ch.G), (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ (dr : ∀ i : Fin D.R.m, FinDatum ch.G t (.chi i D.R.m)) (cr : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) →₀ ℂ), (∀ i, (dr i).e = e ∧ IsCombOf ch.W (dr i) (cr i)) ∧ (∀ i, comb ch.W.ψ _ _ (cr i) (ch.rm.vX i D.R.m) = fr i) ∧ ∀ i y, IsHalf e y → (dr i).fn y = ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) := by
  first | exact @GlobalTheory.RowSingle.rowData | exact GlobalTheory.RowSingle.rowData | (intros; apply GlobalTheory.RowSingle.rowData <;> assumption)
