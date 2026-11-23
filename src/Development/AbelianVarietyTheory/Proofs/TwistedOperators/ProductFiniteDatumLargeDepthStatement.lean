module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFiniteDatumLargeDepth
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.productFiniteDatum_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m) (d₁ d₂ : FinDatum ch.G t (.top t j)) (c₁ c₂ : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P) → IsCombOf ch.W d₁ c₁ → IsCombOf ch.W d₂ c₂ → ∃ (d : FinDatum ch.G t (.top t j)) (c : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf ch.W d c ∧ (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧ ∀ f, comb ch.W.ψ _ _ c f = comb ch.W.ψ _ _ c₁ (comb ch.W.ψ _ _ c₂ f) := by
  first | exact @GlobalTheory.ProdDatum.prod_datum | exact GlobalTheory.ProdDatum.prod_datum | (intros; apply GlobalTheory.ProdDatum.prod_datum <;> assumption)
