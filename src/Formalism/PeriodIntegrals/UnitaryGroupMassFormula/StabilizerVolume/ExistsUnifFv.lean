module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.FibExGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVDxSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.EventuallySmulSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem hR_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J (t • x) y = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J x (t • y) = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

instance hermSMul (σ : E →ₐ[F] E) (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun t S => ⟨t • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h := S.2 a b
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap]
    rw [h]⟩⟩

theorem coe_hermSMul (σ : E →ₐ[F] E) (n : ℕ) (t : R) (S : HermR R σ n) :
    ((t • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = t • (S : Matrix _ _ _) := rfl

instance hermModule (σ : E →ₐ[F] E) (n : ℕ) : Module R (HermR R σ n) :=
  Function.Injective.module R (HermR R σ n).subtype Subtype.coe_injective (fun _ _ => rfl)

end HermMod

theorem exists_unif_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) ∧
      π ∈ v.adicCompletionIntegers F := PI.VolStabSW.exists_unif_Fv v

theorem gramFilt_of : GramFilt := by
  intro F E _ _ _ _ σ hσ M J hJ hdet a ha1 _ v d b x hx
  letI : FiniteDimensional F E := Module.Finite.of_basis b
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  letI : NumberField E :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F E }
  exact PI.VolStabSW.OmFibG.gramFilt_gen σ hσ M J hJ hdet a ha1 v d b x hx

end PI.VolStabS
