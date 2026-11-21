import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

theorem exists_rational_rep_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ξ : κ → F,
      r - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a := by
  intro F _ _ κ _ a _ r
  have hd : DenseRange (Pi.map fun (_ : κ) => algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    DenseRange.piMap fun _ => PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)
  have hop : IsOpen {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (GlobalTheory.EvAdm.isOpen_scaledInt a).preimage (continuous_const.sub continuous_id)
  have hr : r ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} := by
    show r - r ∈ GlobalTheory.EvAdm.scaledInt F κ a
    rw [sub_self]
    exact zero_mem _
  obtain ⟨ξ, hξ⟩ := hd.exists_mem_open hop ⟨r, hr⟩
  exact ⟨ξ, hξ⟩

end GlobalTheory.EvAdm
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_approx_scaled : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ξ : κ → F,
      r - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a := by
  atlas_forward_decl GlobalTheory.EvAdm.exists_rational_rep_scaledInt
