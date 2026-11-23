module

public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDiagonalFrameChangeUnweightingSymEdges
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_diagonal_frame_change_unweighting_symEdges : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  first | exact @GlobalTheory.DiagFrameWeights.exists_diag_frame | exact GlobalTheory.DiagFrameWeights.exists_diag_frame | (intros; apply GlobalTheory.DiagFrameWeights.exists_diag_frame <;> assumption)
