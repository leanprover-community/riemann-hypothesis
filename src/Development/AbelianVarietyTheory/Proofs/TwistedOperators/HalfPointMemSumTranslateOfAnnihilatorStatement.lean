module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPointMemSumTranslateOfAnnihilator
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix


theorem _root_.GlobalTheory.T.halfPoint_mem_sum_translate_of_annihilator : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ Z : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf e Z →
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1) →
    ∃ a ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∃ b ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), Z = e • a + actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • b) := by
  first | exact @GlobalTheory.AnnSum.ann_sum | exact GlobalTheory.AnnSum.ann_sum | (intros; apply GlobalTheory.AnnSum.ann_sum <;> assumption)
