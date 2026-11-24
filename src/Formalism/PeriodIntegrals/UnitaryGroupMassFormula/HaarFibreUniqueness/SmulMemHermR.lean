module

public import Formalism.PeriodIntegrals.OmFibreUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq

@[expose] public section

noncomputable section

namespace PI.OmFibreUniq.W.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.VolStabSW PI.VolStabSW.SdUniqW PI.AdicCompletionValuation
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (a : ℕ)

theorem sigR_algebraMap (c : R) : sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R _ c := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem smul_mem_HermR (c : R) (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (hS : S ∈ HermR R σ a) :
    c • S ∈ HermR R σ a := by
  intro i j
  have h := hS i j
  simp only [Matrix.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, h, sigR_algebraMap]

instance hermSMul : SMul R (HermR R σ a) :=
  ⟨fun c S => ⟨c • (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)), smul_mem_HermR R σ a c S S.2⟩⟩

instance hermContSMul [TopologicalSpace R] [IsTopologicalRing R] :
    ContinuousSMul R (HermR R σ a) :=
  ⟨by
    apply Continuous.subtype_mk
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)⟩

instance hermSC [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    [FiniteDimensional F E] : SecondCountableTopology (HermR R σ a) := by
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → R ⊗[F] E))
  exact TopologicalSpace.Subtype.secondCountableTopology _

end HermMod

def PsiNT : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)),
    IsCharAF F ψ → IsStdChar ψ → NumberField.IsTotallyReal F → ∃ y, psiV F ψ v y ≠ 1

end PI.OmFibreUniq.W.Sd
