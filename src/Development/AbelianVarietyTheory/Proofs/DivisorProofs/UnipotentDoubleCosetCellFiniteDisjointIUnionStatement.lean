module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDoubleCosetCellFiniteDisjointIUnion
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

open Matrix Topology

theorem _root_.GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) := by
  first | (exact @GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (exact GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (intros; apply GlobalTheory.JSW.Cut.cell_finite_disjoint_union'  <;> assumption)
