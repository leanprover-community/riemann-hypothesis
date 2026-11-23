module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
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

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ v, vac v ≠ 0) → (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] (p : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] P) (Q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type)
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ i, ∀ v ∉ T, φ i v = vac v) → ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) = 0 →
    ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) = 0 := by
  first | exact @GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure | exact GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure | (intros; apply GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure <;> assumption)
