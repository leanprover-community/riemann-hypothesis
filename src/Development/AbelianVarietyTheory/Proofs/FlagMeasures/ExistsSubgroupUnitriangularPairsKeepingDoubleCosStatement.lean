module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubgroupUnitriangularPairsKeepingDoubleCos
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

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_subgroup_unitriangular_pairs_keeping_doubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (t : TauC Y u u'), ∃ B : Subgroup (GV D × GV D), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) ∧ (∀ n ∈ NLam t.lam (lf D (X.Fu u)), ∀ n' ∈ NLam t.lam' (lf D (X.Fu u')), (n, n') ∈ B) ∧ ∀ a₁ ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a₂ ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a₁' ∈ Aut0 (lf D (X.Fu u')) t.lam', ∀ a₂' ∈ Aut0 (lf D (X.Fu u')) t.lam', (KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam (a₁ * t.lin * a₁'⁻¹) (a₂ * t.lin * a₂'⁻¹) ↔ (a₁⁻¹ * a₂, a₁'⁻¹ * a₂') ∈ B) := by
  first | exact @GlobalTheory.KeyGroup.keyStab_subgroup | exact GlobalTheory.KeyGroup.keyStab_subgroup | (intros; apply GlobalTheory.KeyGroup.keyStab_subgroup <;> assumption)
