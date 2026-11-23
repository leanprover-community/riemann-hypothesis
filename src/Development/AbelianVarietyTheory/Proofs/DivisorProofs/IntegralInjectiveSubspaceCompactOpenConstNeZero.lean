module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.integral_indicator_preimage_injective_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  intro F _ _ v κ _ N ν hν j hj c hc U hUo hUc h0
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  set S : Set (Fin N → Fv F v) := j ⁻¹' U with hSdef
  have hSo : IsOpen S := hUo.preimage hjc
  have hSsub : S ⊆ g '' U := by
    intro y hy
    refine ⟨j y, hy, ?_⟩
    have := congrArg (fun f => f y) hg
    simpa using this
  have hfin : ν S < ⊤ := lt_of_le_of_lt (measure_mono hSsub) ((hUc.image hgc).measure_lt_top)
  have hpos : 0 < ν S := hSo.measure_pos ν ⟨0, by simp [hSdef, h0]⟩
  have heq : (fun y => U.indicator (fun _ => c) (j y)) = S.indicator (fun _ => c) := by
    funext y
    by_cases hy : j y ∈ U
    · have : y ∈ S := hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : y ∉ S := hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [heq, integral_indicator_const c hSo.measurableSet]
  refine smul_ne_zero ?_ hc
  rw [Measure.real]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
