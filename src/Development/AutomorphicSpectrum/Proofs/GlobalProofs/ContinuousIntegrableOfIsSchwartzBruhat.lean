module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralSelfDualEqAdelicFourier
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.AutomorphicForms.ReductionMeasure
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord GroundTheory.Automorphic.GJMatrix
open scoped NNReal

theorem continuous_integrable_of_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Continuous Φ ∧ Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M dx hdx Φ hΦ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor 1 M
  have hf := (isSchwartzBruhat_iff b Φ).1 hΦ
  let e := crd (AF F) b M
  have hcomp : (Φ ∘ e.symm) ∘ e = Φ := by
    funext X
    simp
  have hcont : Continuous Φ := by
    have h : Continuous ((Φ ∘ e.symm) ∘ e) :=
      (continuous_of_mem_schwartzBruhatPi hf).comp e.continuous
    rwa [hcomp] at h
  refine ⟨hcont, ?_⟩
  haveI : LocallyCompactSpace (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.secondCountableTopology
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, dx = c • mu0 e := ⟨_, Measure.isAddLeftInvariant_eq_smul dx (mu0 e)⟩
  have hI : Integrable Φ (mu0 e) := by
    rw [mu0, (measurableEmbedding_symm e).integrable_map_iff]
    exact integrable_of_mem_schwartzBruhatPi hf
  rw [hc]
  exact hI.smul_measure_nnreal

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt
