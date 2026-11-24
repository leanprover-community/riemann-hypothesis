module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousPsiVOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

theorem piu_inv_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (piu v)⁻¹ ∉ v.adicCompletionIntegers F := by
  intro h
  have hU : {x : Fv F v | x ≠ 1} ∈ 𝓝 (0 : Fv F v) := isOpen_ne.mem_nhds zero_ne_one
  obtain ⟨k, hk⟩ := (tube v (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v) hU).exists
  have hm : (piu v)⁻¹ ^ k ∈ v.adicCompletionIntegers F := pow_mem h k
  apply hk _ hm
  simp [smul_eq_mul, mul_inv_cancel₀ (pow_ne_zero k (piu_ne v))]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

theorem finrank_pos' : 0 < Module.finrank F E := Module.finrank_pos

theorem exists_not_mem_oev : ∃ t0 : Fv F v ⊗[F] E, t0 ∉ OEv (E := E) v := by
  classical
  set i0 : Fin (Module.finrank F E) := ⟨0, finrank_pos'⟩
  set P : Set (Fv F v) := (fun y => trE (E := E) v y i0) '' OEv (E := E) v
  have hP : IsCompact P :=
    (isCompact_oev v).image ((continuous_apply i0).comp (continuous_trE v))
  have hU : (v.adicCompletionIntegers F : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) :=
    (Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _)
  obtain ⟨k, hk⟩ := (tube v hP hU).exists
  refine ⟨(trE (E := E) v).symm (Pi.single i0 (piu v ^ (k + 1))⁻¹), fun h => ?_⟩
  have hp : (piu v ^ (k + 1))⁻¹ ∈ P :=
    ⟨_, h, by simp⟩
  have h2 := hk _ hp
  have e : piu v ^ k • (piu v ^ (k + 1))⁻¹ = (piu v)⁻¹ := by
    have := piu_ne v
    rw [smul_eq_mul, pow_succ]
    field_simp
  rw [e] at h2
  exact piu_inv_not_mem v h2

variable [SecondCountableTopology (Fv F v ⊗[F] E)]

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
