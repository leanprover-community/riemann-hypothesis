module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bdR_filtration_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ a : ℤ, Per.FilD l (a + 1) ≤ Per.FilD l a) ∧ (1 : Per.BdR l) ∈ Per.FilD l 0 ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ x : Per.BdR l, ∃ a, x ∈ Per.FilD l a) ∧ (∀ x : Per.BdR l, (∀ a, x ∈ Per.FilD l a) → x = 0) ∧ (∀ (g : Per.Gq l) (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a → Per.σD g x ∈ Per.FilD l a) ∧ ∀ (n : ℕ) (y : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
  first | exact @GlobalTheory.MemLoc.filD_laws | exact GlobalTheory.MemLoc.filD_laws | (intros; apply GlobalTheory.MemLoc.filD_laws <;> assumption)
