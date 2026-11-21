import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.PureIndO

theorem pure_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = GlobalTheory.FinComm.indO v) →
    pure f φ ∈ schA F κ := by
  intro F _ _ κ _ f φ hSB hstd
  exact Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    GlobalTheory.AdelicCoordSB.finprod_mem_SB F κ φ hSB hstd, rfl⟩

end GlobalTheory.PureIndO
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_tensor_mem_schwartz_adelic : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = GlobalTheory.FinComm.indO v) →
    pure f φ ∈ schA F κ := by
  atlas_forward_decl GlobalTheory.PureIndO.pure_mem_schA
