module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockGroupUnipotentDoubleCosetCellBlockDia
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

theorem _root_.GlobalTheory.T.exists_blockGroup_unipotentDoubleCosetCell_blockDiag_iff : ∀ {F : Type} [NormedField F] {m : ℕ} (U : Subgroup (GL (Fin (m + 2)) F)), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∃ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) ∧ IsOpen (B : Set (GL (Fin (m + 1)) F)) ∧ (∀ b, GlobalTheory.JSW.KirFin.cor b ∈ U → b ∈ B) ∧ ∀ h₀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.cor h ∈ GlobalTheory.JSW.Cut.cell (GlobalTheory.JSW.KirFin.cor h₀) (U : Set (GL (Fin (m + 2)) F)) ↔ h ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
  first | (exact @GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff) | (exact GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff) | (intros; apply GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff  <;> assumption)
