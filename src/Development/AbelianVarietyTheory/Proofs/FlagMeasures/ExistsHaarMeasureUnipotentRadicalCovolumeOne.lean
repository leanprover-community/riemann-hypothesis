module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalDomainCovol
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NsubCocompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.T2SpaceGeneralLinearGroup
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.NsubHaarCovol

theorem exists_haar_covol_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ μ : Measure (Nsub (AF F) σ J P), μ.IsHaarMeasure ∧ covol μ = 1 := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP
  have hcl : IsClosed (Nsub (AF F) σ J P : Set (HA (AF F) σ J)) :=
    PI.UnitaryGroupMassFormula.MeasWCore.isClosed_Nsub (AF F) σ J P
  let μ0 : Measure (Nsub (AF F) σ J P) := Measure.haar
  have hμ0 : μ0.IsHaarMeasure := inferInstance
  obtain ⟨⟨𝓕, h𝓕⟩, hall, hscale⟩ :=
    GlobalTheory.ClosedSubgroupCovol.fundamentalDomain_covol F E σ hCM n J hJ _ hcl μ0 hμ0
  obtain ⟨Kc, hKc, hcov⟩ := GlobalTheory.UnipFlagCore.nsub_cocompact F E σ hCM n J hJ r P T hP
  obtain ⟨hcv, hne, hle⟩ := hall 𝓕 h𝓕
  have hfin : μ0 𝓕 ≠ ∞ :=
    ((hle Kc hKc.isClosed.measurableSet hcov).trans_lt hKc.measure_lt_top).ne
  have hpos : 0 < (μ0 𝓕).toReal := ENNReal.toReal_pos hne hfin
  have hc0 : ((μ0 𝓕).toNNReal)⁻¹ ≠ 0 := inv_ne_zero (by
    intro h; rw [ENNReal.toNNReal_eq_zero_iff] at h; exact h.elim hne hfin)
  refine ⟨((μ0 𝓕).toNNReal)⁻¹ • μ0, Measure.IsHaarMeasure.nnreal_smul _ hc0, ?_⟩
  rw [hscale _ hc0, hcv, NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal]
  exact inv_mul_cancel₀ hpos.ne'

end GlobalTheory.NsubHaarCovol
