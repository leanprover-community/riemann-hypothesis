module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mirabolic_cell_structure_data : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ),
  (MirUin k ((i + 1) + t + 1)).Normal ∧ IsOpen ((mirChar k ψ ((i + 1) + t)).ker : Set (MirUin k ((i + 1) + t + 1))) ∧
    IsClosed (Cl k i t) ∧ (∀ h ∈ HPG k (i + 1) (t + 1), ∀ x ∈ Cl k i t, h * x ∈ Cl k i t) ∧
    (∀ x ∈ Cl k i t, ∀ u ∈ MirUin k ((i + 1) + t + 1), x * u ∈ Cl k i t) ∧
    ∀ L₁ L₂ : Subgroup (Mir k ((i + 1) + t + 1)), L₁ ≤ MirUin k ((i + 1) + t + 1) → L₂ ≤ MirUin k ((i + 1) + t + 1) →
      IsCompact (L₁ : Set (Mir k ((i + 1) + t + 1))) → IsCompact (L₂ : Set (Mir k ((i + 1) + t + 1))) →
      ∃ L : Subgroup (Mir k ((i + 1) + t + 1)), L ≤ MirUin k ((i + 1) + t + 1) ∧ IsCompact (L : Set (Mir k ((i + 1) + t + 1))) ∧
        L₁ ≤ L ∧ L₂ ≤ L := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Grp.main | exact GlobalTheory.CompanionTheory.BZPhiPG.Grp.main | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.main <;> assumption)
