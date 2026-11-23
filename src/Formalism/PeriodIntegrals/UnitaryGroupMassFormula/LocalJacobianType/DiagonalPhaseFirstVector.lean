module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ChiZeroRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousPsiVOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

theorem continuous_tr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
  PI.VolStabSW.SdUniqW.continuous_trace_tens (F := F) (E := E) (Fv F v)

theorem diagonal_phase_first_vector : (0 : Fv F v ⊗[F] E) ∈ D1 (E := E) v ψ := by
  intro x _; simp [psiV_zero]

theorem conductor_add_mem {y y' : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (hy' : y' ∈ D1 (E := E) v ψ) :
    y + y' ∈ D1 (E := E) v ψ := by
  intro x hx
  rw [mul_add, map_add (f := _), psiV_add', hy x hx, hy' x hx, mul_one]

theorem conductor_neg_mem {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) : -y ∈ D1 (E := E) v ψ := by
  intro x hx
  have h := psiV_neg_mul v ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y))
  rw [hy x hx, mul_one] at h
  rwa [mul_neg, map_neg]

def D1sub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := D1 (E := E) v ψ
  add_mem' := conductor_add_mem v ψ
  zero_mem' := diagonal_phase_first_vector v ψ
  neg_mem' := conductor_neg_mem v ψ

theorem trE_mem_Aset {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (j : Fin (Module.finrank F E)) :
    trE (E := E) v y j ∈ PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v) := by
  intro c hc
  have e : c * trE (E := E) v y j =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((c • bas (E := E) v j) * y) := by
    rw [trE_apply, trC_apply, smul_mul_assoc, map_smul, smul_eq_mul]
  rw [e]
  exact hy _ (smul_bas_mem v hc j)

variable (hK : OpenKer v ψ)
include hK

theorem conductor_isClosed : IsClosed (D1 (E := E) v ψ) := by
  have e : D1 (E := E) v ψ = ⋂ x ∈ OEv (E := E) v,
      {y | psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1} := by
    ext y; simp [D1]
  rw [e]
  exact isClosed_biInter fun x _ => isClosed_eq ((continuous_psiV_of v ψ hK).comp
    ((continuous_tr v).comp (continuous_const.mul continuous_id))) continuous_const

theorem conductor_isCompact (hnt : ∃ r, psiV F ψ v r ≠ 1) : IsCompact (D1 (E := E) v ψ) := by
  obtain ⟨y0, -, hy0⟩ := PI.OmFibreUniq.W.SdChar.Aset_bdd v (psiV F ψ v) (psiV_add' v ψ)
    (norm_psiV_of v ψ hK) hnt
  set C : Set (Fin (Module.finrank F E) → Fv F v) :=
    Set.univ.pi fun _ => (fun s => y0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v))
  have hC : IsCompact C := isCompact_univ_pi fun _ =>
    (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_const.mul continuous_id)
  refine (hC.image (continuous_trE_symm (E := E) v)).of_isClosed_subset (conductor_isClosed v ψ hK) ?_
  intro y hy
  refine ⟨trE (E := E) v y, fun j _ => ?_, by simp⟩
  obtain ⟨s, hs, e⟩ := hy0 _ (trE_mem_Aset v ψ hy j)
  exact ⟨s, hs, e.symm⟩

theorem conductor_mem_nhds : D1 (E := E) v ψ ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
  obtain ⟨m, w, hw, hgen⟩ := exists_gens (E := E) v
  have hA := PI.OmFibreUniq.W.SdChar.Aset_mem_nhds v (psiV F ψ v) (continuous_psiV_of v ψ hK)
    (psiV_add' v ψ) (norm_psiV_of v ψ hK)
  have hN : (⋂ k, {y : Fv F v ⊗[F] E | Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) ∈
      PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v)}) ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
    refine Filter.iInter_mem.2 fun k => ?_
    have hc : Continuous fun y : Fv F v ⊗[F] E => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) :=
      (continuous_tr v).comp (continuous_const.mul continuous_id)
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hA)
  refine Filter.mem_of_superset hN fun y hy x hx => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
  obtain ⟨c, hc, rfl⟩ := hgen x hx

  rw [Finset.sum_mul, map_sum, psiV_sum]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  exact hy k (c k) (hc k)

theorem conductor_isOpen : IsOpen (D1 (E := E) v ψ) :=
  AddSubgroup.isOpen_of_mem_nhds (D1sub (E := E) v ψ) (conductor_mem_nhds v ψ hK)

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
