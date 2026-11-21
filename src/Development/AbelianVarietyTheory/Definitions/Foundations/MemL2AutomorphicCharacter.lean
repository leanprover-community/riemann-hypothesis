import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstantOneNotCuspidalOfIsotropic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp
open GlobalTheory.Mem.Th GlobalTheory.Cusp.Model GlobalTheory.CuspDecay.Model
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.AutMult.Model

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [SFinite μ]
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

omit [μ.IsMulLeftInvariant] in

theorem ae_const {φ : G → ℂ} (hφ : AEStronglyMeasurable φ μ) (h : ∀ g, (fun x => φ (x * g)) =ᵐ[μ] φ) :
    ∃ c, φ =ᵐ[μ] fun _ => c := by
  refine exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU => ?_
  refine eventuallyConst_set.1 (aeconst_of_forall_preimage_smul_ae_eq Gᵐᵒᵖ (s := φ ⁻¹' U)
    (hφ.aemeasurable.nullMeasurable hU) fun g => ((h g.unop).mono fun x hx => ?_).set_eq)
  exact iff_of_eq (congrArg (· ∈ U) hx)


omit [SFinite μ] [μ.IsMulRightInvariant] in

theorem lift_smul (c : ℂ) {F : L2 Γ μ} {φ : G → ℂ} (e : lift Γ F =ᵐ[μ] φ) : lift Γ (c • F : L2 Γ μ) =ᵐ[μ] c • φ :=
  EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)) (e.const_smul c)



end General



attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {χ : GA D V →* Circle}

omit [μ.IsMulRightInvariant] in

theorem memL2_automorphic_character (hχ : Continuous χ) (h : ∀ γ ∈ GQ V, χ γ = 1) : MemL2Quotient (GQ V) μ fun x => (χ x : ℂ) :=
  memL2_of_bounded_continuous_invariant (C := 1) (fun γ hγ g => by simp [h γ hγ]) (continuous_subtype_val.comp hχ) fun g => (Circle.norm_coe _).le












omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in

theorem finVec_one (θ : InfF D) (A : CptF V) : finVec V θ A (charRep 1) = ⊤ :=
  eq_top_iff.2 fun x _ => ⟨⟨⊤, inferInstance, fun _ _ => trivial⟩, by
    change IsOpen {g : GfC V | _ = x}
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun g => one_mul x⟩

def constEmb (θ : InfF D) (A : CptF V) : finVec V θ A (charRep 1) →ₗ[ℂ] (GA D V → ℂ) :=
  LinearMap.pi fun _ => (finVec V θ A (charRep 1)).subtype


omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in

theorem constEmb_ne_zero (θ : InfF D) (A : CptF V) : constEmb θ A ≠ 0 := fun e =>
  one_ne_zero (congrFun (DFunLike.congr_fun e ⟨1, finVec_one θ A ▸ Submodule.mem_top⟩) 1)






end GlobalTheory.AutMult.Model

end
