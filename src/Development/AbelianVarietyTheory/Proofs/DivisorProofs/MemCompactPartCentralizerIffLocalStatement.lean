module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Filter GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.mem_compactPart_centralizer_iff_local : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (KH : ∀ i, Subgroup (H i)) (T : Subgroup G) (TH : ∀ i, Subgroup (H i)), (∀ i, Continuous (p i)) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ a ∈ TH i, ∀ b ∈ TH i, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ x ∈ T ∧ ∀ i, p i x ∈ cptPart (TH i) := by
  first | exact @GlobalTheory.BCT.mem_cptPart_iff_local | exact GlobalTheory.BCT.mem_cptPart_iff_local | (intros; apply GlobalTheory.BCT.mem_cptPart_iff_local <;> assumption)
