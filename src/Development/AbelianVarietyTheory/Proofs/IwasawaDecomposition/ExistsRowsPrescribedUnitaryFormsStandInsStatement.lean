module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns : ∀ (B : Base) (C : Cols B) (n : C.Tup → ℕ) (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0))) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a))) (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a)))) (mt : B.places.Pl → C.Tup), (∀ w, mt (B.places.conj w) = mt w) → SpectralModel.ColsPos C → ∃ (W : RowsRest B C) (g : ∀ a, EuclideanSpace ℂ (Fin (n a)) ≃ₗᵢ[ℂ] W.Amb a), StandIn W ∧ (∀ w, W.muAt w = C.mu0) ∧ (∀ w, W.muTw w = mt w) ∧ (∀ u F, W.eMt0 u F = g C.mu0 (e0 u F)) ∧ (∀ u a F, W.eMtTw u a F = g a (eT u a F)) ∧ (∀ a y, g a y ∈ (W.Mtilde a).carrier ↔ y ∈ (L a).carrier) ∧ (∀ a y, g a y ∈ (W.Mtilde a).gen ↔ y ∈ (L a).gen) ∧ (∀ a, W.eOp a = LinearMap.id) ∧ ∀ u a, W.ze u a = 1 := by
  first | exact @GlobalTheory.Mem.DfGen.exists_rowsRest_std | exact GlobalTheory.Mem.DfGen.exists_rowsRest_std | (intros; apply GlobalTheory.Mem.DfGen.exists_rowsRest_std <;> assumption)
