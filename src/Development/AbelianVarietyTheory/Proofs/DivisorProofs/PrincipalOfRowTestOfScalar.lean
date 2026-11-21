import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemRangeToF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DownUpLambdaOperators

noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.OneFormTest

theorem tw_span_top (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {I : Type} (v : I → E)
    (h : Submodule.span ℂ (Set.range v) = ⊤) : Submodule.span ℂ (Set.range fun i => Tw.mk s (v i)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : Tw.out x ∈ Submodule.span ℂ (Set.range v) := h ▸ Submodule.mem_top
  have key : ∀ y ∈ Submodule.span ℂ (Set.range v),
      Tw.mkL s E y ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (v i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  exact key _ hx

theorem tw_map_surjective (s : Bool) {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E']
    [InnerProductSpace ℂ E'] {f : E →ₗ[ℂ] E'} (h : Function.Surjective f) : Function.Surjective (Tw.map s f) := h

theorem model_of_pres {H Γ : Type} [Group H] [Group Γ] {ι : Γ →* H} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup H}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (H → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) :
    (∀ x y, ⟪j x, j y⟫_ℂ = σ (S.csum x.1 y.1)) ∧ Function.Injective j ∧ Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [hM.2.2, hj, hj]
    exact h3 x y
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h4 : P.extL x = 0 := by rw [← hj, hx, map_zero]
    rw [← S.basis.sum_repr x, map_sum] at h4
    simp only [map_smulₛₗ] at h4
    have h5 := Fintype.linearIndependent_iff.1 h1 _ h4
    refine S.basis.repr.injective (Finsupp.ext fun i => ?_)
    rw [(map_eq_zero _).1 (h5 i), map_zero, Finsupp.zero_apply]
  · apply Submodule.map_injective_of_injective hM.1
    rw [Submodule.map_top, hM.2.1, Submodule.map_span, ← Set.range_comp, show M.e ∘ j = P.extL from funext hj, h2]


theorem surjective_of_scalar {H E : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup E] [Module ℂ E] (f : H →ₗ[ℂ] E)
    (g : E →ₗ[ℂ] H) {I : Type} (p : I → Submodule ℂ E) (hp : ⨆ c, p c = ⊤)
    (h : ∀ c, ∃ l : ℝ, 0 < l ∧ ∀ x ∈ p c, (f ∘ₗ g) x = (l : ℂ) • x) : Function.Surjective f := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hp, iSup_le_iff]
  intro c x hx
  obtain ⟨l, hl, h⟩ := h c
  refine ⟨(l : ℂ)⁻¹ • g x, ?_⟩
  have h1 : f (g x) = (l : ℂ) • x := h x hx
  rw [map_smul, h1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hl.ne'), one_smul]

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem model_jX (hH : R.models_HX) (hj : R.models_jX) (t : T) :
    (∀ x y : (A.MtildeCSD t).Forms, ⟪R.jX t x, R.jX t y⟫_ℂ = D.what₂.embLL ((A.MtildeCSD t).csum x.1 y.1)) ∧
      Function.Injective (R.jX t) ∧ Submodule.span ℂ (Set.range (R.jX t)) = ⊤ :=
  model_of_pres (S := A.MtildeCSD t) (R.B.R t).pres (R.HX t) (hH t) (R.jX t) (hj t)

theorem formsTie (hH : R.models_HX) (hj : R.models_jX) : FormsTie (F := A.fam) (R.toCx F) where
  inner_eq t x y := ((congrArg (cj (twAt D.what₂.embLL A.v0)) ((model_jX R hH hj t).1 x y)).trans (R.emb0 _).symm :)
  inj t := (model_jX R hH hj t).2.1
  span t := tw_span_top (twAt D.what₂.embLL A.v0) (R.jX t) (model_jX R hH hj t).2.2





def PartsSpan : Prop := ⨆ c, GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.partE R c = ⊤

theorem th_surjective (hB : GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.Concl R) (hS : PartsSpan R) (t : T) : Function.Surjective (R.Th t) :=
  surjective_of_scalar (R.Th t) (LinearMap.adjoint (R.Th t)) (GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.partE R) hS (hB.scalar_pos t)

theorem theta_surjective (hon : ∀ t, Function.Surjective (R.Th t)) (t : T) : Function.Surjective ((R.toCx F).Θ t) :=
  tw_map_surjective (twAt D.what₂.embLL A.v0) (hon t)



end Concrete

end GlobalTheory.OneFormTest
