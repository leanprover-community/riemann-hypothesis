module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralVanishOfInnerVanish
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
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isIteratedInvariantIntegral_vanish_of_inner_vanish : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (A B R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → (∀ i ∈ l, Split (A i) (B i) (R i) (K i)) → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (ρ' : ∀ i, Measure ((R i).subgroupOf (B i))) (μ' : ∀ i, Measure (B i)), (∀ i ∈ l, (ρ i).IsHaarMeasure ∧ (μ i).IsHaarMeasure ∧ (ρ' i).IsHaarMeasure ∧ (μ' i).IsHaarMeasure) → ∀ (S : Finset (∀ i, H i)) (q : (∀ i, H i) → ℂ) (z : ℂ), (∀ b ∈ S, ∀ i, b i ∈ B i) → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ b ∈ S, InCells A R K l b h) → NIter ρ μ q l 1 z → (∀ a : ∀ i, H i, (∀ i, a i ∈ A i) → (∀ i, i ∉ l → a i = 1) → NIter ρ' μ' (fun b : ∀ i, B i => q fun i => a i * (b i).1) l 1 0) → z = 0 := by
  first | exact @GlobalTheory.NestVan.nested_vanish | exact GlobalTheory.NestVan.nested_vanish | (intros; apply GlobalTheory.NestVan.nested_vanish <;> assumption)
