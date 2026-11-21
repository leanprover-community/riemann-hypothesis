import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhdEqPhk
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GJMeas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem continuous_detUnit : Continuous (GeneralLinearGroup.det : GL (Fin 2) F → Fˣ) := by
  rw [Units.continuous_iff]
  constructor
  · exact Continuous.matrix_det Units.continuous_val
  · have : Continuous fun g : GL (Fin 2) F => ((g⁻¹ : GL (Fin 2) F).val).det :=
      Continuous.matrix_det (Units.continuous_val.comp continuous_inv)
    convert this using 2 with g
    rw [← map_inv]
    rfl

theorem continuous_of_rightInvariant (W : GL (Fin 2) F → ℂ) (U : OpenSubgroup (GL (Fin 2) F))
    (h : ∀ g, ∀ u ∈ U, W (g * u) = W g) : Continuous W := by
  rw [continuous_iff_continuousAt]
  intro g
  have hopen : IsOpen ((fun x : GL (Fin 2) F => g⁻¹ * x) ⁻¹' (U : Set (GL (Fin 2) F))) :=
    U.isOpen.preimage (continuous_const.mul continuous_id)
  have hmem : ((fun x : GL (Fin 2) F => g⁻¹ * x) ⁻¹' (U : Set (GL (Fin 2) F))) ∈ nhds g :=
    hopen.mem_nhds (by simpa using U.one_mem)
  have hev : (fun _ : GL (Fin 2) F => W g) =ᶠ[nhds g] W := by
    filter_upwards [hmem] with x hx
    have := h g (g⁻¹ * x) hx
    simpa using this.symm
  exact (continuousAt_const).congr hev

theorem continuous_mp_det (z : ℂ) :
    Continuous fun g : GL (Fin 2) F => mp (GeneralLinearGroup.det g) z := by
  have h1 : Continuous fun g : GL (Fin 2) F =>
      ((modulus (((GeneralLinearGroup.det g : Fˣ)) : F) : ℝ) : ℂ) := by
    have h2 : Continuous fun g : GL (Fin 2) F => modulus (((GeneralLinearGroup.det g : Fˣ)) : F) :=
      continuous_modulus.comp (Units.continuous_val.comp continuous_detUnit)
    exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp h2)
  refine h1.cpow continuous_const fun g => ?_
  refine Complex.ofReal_mem_slitPlane.2 ?_
  exact_mod_cast modulus_pos (Units.ne_zero _)




end GlobalTheory.CompanionTheory.GJMeas
