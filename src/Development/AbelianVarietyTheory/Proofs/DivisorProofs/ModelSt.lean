import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRunModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinatesModPrimeSelfDualStabilizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqPlGwOrIsConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunWeightArch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThreeRLtGOfParams

section
open Module

namespace GlobalTheory.SemilinearReading

theorem exists_semilinear_extension_rep :
    ∀ {K LL Cs W G : Type} [Field K] [Field LL] [Algebra K LL] [AddCommGroup Cs] [Module K Cs] [AddCommGroup W] [Module ℂ W] [Group G] {n m : ℕ} (σ₀ : K →+* ℂ) (σ : LL →+* ℂ), (∀ a, σ (algebraMap K LL a) = σ₀ a) → ∀ (cu : Cs →ₗ[K] (Fin n → LL)) (b : Fin m → Cs), Submodule.span K (Set.range b) = ⊤ → LinearIndependent LL (fun k => cu (b k)) → Submodule.span LL (Set.range fun k => cu (b k)) = ⊤ → ∀ (R : Cs →ₛₗ[σ₀] W), LinearIndependent ℂ (fun k => R (b k)) → Submodule.span ℂ (Set.range R) = ⊤ → ∀ (ρL : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))), ∃ (f : (Fin n → LL) →ₛₗ[σ] W) (ρ : Representation ℂ G W), (∀ F, f (cu F) = R F) ∧ (∀ g w, ρ g (f w) = f (ρL g w)) ∧ (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  intro K LL Cs W G _ _ _ _ _ _ _ _ n m σ₀ σ hσ cu b hbs hbi hbt R hR hRs ρL
  classical
  let B : Basis (Fin m) LL (Fin n → LL) := Basis.mk hbi hbt.ge
  have hB : ∀ k, B k = cu (b k) := fun k => Basis.mk_apply _ _ _
  let f : (Fin n → LL) →ₛₗ[σ] W :=
    { toFun := fun w => ∑ k, σ (B.repr w k) • R (b k)
      map_add' := by
        intro x y
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp [Finset.smul_sum, mul_smul] }
  have hfB : ∀ k, f (B k) = R (b k) := by
    intro k
    change ∑ j, σ (B.repr (B k) j) • R (b j) = _
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj.symm]
    · simp
  have hcu : ∀ F, f (cu F) = R F := by
    intro F
    have hF : F ∈ Submodule.span K (Set.range b) := by rw [hbs]; trivial
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hF
    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ R, ← hB, ← algebraMap_smul LL (a k) (B k), map_smulₛₗ f, hσ, hfB]
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun k => R (b k)) := by
    rw [← hRs, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    rw [← hcu]
    change ∑ j, σ (B.repr (cu F) j) • R (b j) ∈ _
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let C : Basis (Fin m) ℂ W := Basis.mk hR hsp
  have hC : ∀ k, C k = f (B k) := fun k => by rw [hfB]; exact Basis.mk_apply _ _ _
  let r : G → W →ₗ[ℂ] W := fun g => C.constr ℂ fun k => f (ρL g (B k))
  have hr : ∀ g w, r g (f w) = f (ρL g w) := by
    intro g w
    conv_lhs => rw [← B.sum_repr w]
    conv_rhs => rw [← B.sum_repr w]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ f, map_smul, map_smul, map_smulₛₗ f, ← hC]
    simp [r]
  let ρ : Representation ℂ G W :=
    { toFun := r
      map_one' := C.ext fun k => by rw [hC, hr]; simp
      map_mul' := fun g h => C.ext fun k => by
        rw [hC, Module.End.mul_apply, hr, hr, hr, map_mul]; rfl }
  refine ⟨f, ρ, hcu, hr, ?_, ?_⟩
  · have hmn : m = n := by
      simpa using (Module.finrank_eq_card_basis B).symm
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · refine hsp.trans ?_
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      change R (b k) ∈ _
      rw [← hfB, ← (Pi.basisFun LL (Fin n)).sum_repr (B k), map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_smulₛₗ f, Pi.basisFun_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Module.finrank_eq_card_basis C, hmn]
  · rw [eq_top_iff]
    refine hsp.trans (Submodule.span_mono ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨B k, hfB k⟩

end GlobalTheory.SemilinearReading
end

section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_extension_of_form_with_transported_rep : ∀ {K LL Cs W G : Type} [Field K] [Field LL] [Algebra K LL] [AddCommGroup Cs] [Module K Cs] [AddCommGroup W] [Module ℂ W] [Group G] {n m : ℕ} (σ₀ : K →+* ℂ) (σ : LL →+* ℂ), (∀ a, σ (algebraMap K LL a) = σ₀ a) → ∀ (cu : Cs →ₗ[K] (Fin n → LL)) (b : Fin m → Cs), Submodule.span K (Set.range b) = ⊤ → LinearIndependent LL (fun k => cu (b k)) → Submodule.span LL (Set.range fun k => cu (b k)) = ⊤ → ∀ (R : Cs →ₛₗ[σ₀] W), LinearIndependent ℂ (fun k => R (b k)) → Submodule.span ℂ (Set.range R) = ⊤ → ∀ (ρL : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))), ∃ (f : (Fin n → LL) →ₛₗ[σ] W) (ρ : Representation ℂ G W), (∀ F, f (cu F) = R F) ∧ (∀ g w, ρ g (f w) = f (ρL g w)) ∧ (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  atlas_forward_decl GlobalTheory.SemilinearReading.exists_semilinear_extension_rep
end

section
section
set_option autoImplicit false

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

namespace GlobalTheory.TwoLevelsDom

theorem lact_tr_mem_dom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom :=
  fun M g c _x hx => GlobalTheory.CuspEmb.lact_tr_mem M g c hx

end GlobalTheory.TwoLevelsDom
end

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelFlagDomain_transporter_mem_domain : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom := by
  atlas_forward_decl GlobalTheory.TwoLevelsDom.lact_tr_mem_dom
end

section
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ShareOn.Reading

theorem cast_mem_SS_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X Y : Data E r} (hXY : X = Y)
    (hΨ : X.Ψ = Y.Ψ) {la : Wt Y.Ψ r} {la' : Wt X.Ψ r}
    (hla : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ Y.Ψ) a, la' ⟨τ, h1⟩ a = la ⟨τ, h2⟩ a) {G : Frame Y.Ψ r → ℂ}
    (hG : G ∈ Y.SS la) : (fun x => G (castFrame hΨ x)) ∈ X.SS la' := by
  subst hXY
  have e : la' = la := by funext τ a; exact hla τ.1 τ.2 τ.2 a
  subst e
  exact hG

theorem rdFun_mem_SS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), rdFun h ha F ∈ M.SS ka := by
  intro D L hT Gi Gl Kc Y cX ex Csz p r h i C _ M ka v e ha hb F c
  have key := GlobalTheory.ReadingTieCheck.reading_mem_SS (h.laws v).p ((i : ℕ) + 1) (p.κ i) F (e c)
  exact cast_mem_SS_of_eq (ha c) ((M.comp_Ψ c).trans (psi_eq ha c)) (fun τ h1 h2 a => hb c τ _ h2 a) key

end GlobalTheory.ShareOn.Reading
end
end

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), rdFun h ha F ∈ M.SS ka := by
  atlas_forward_decl GlobalTheory.ShareOn.Reading.rdFun_mem_SS
end

section
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ShareOn.Reading
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castFrame_castFrame_symm {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (hΨ : Ψ = Ψ')
    (x : Frame Ψ' r) : castFrame hΨ (castFrame hΨ.symm x) = x := by
  subst hΨ; rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem rdLin_linearIndependent {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
    {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
    [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (n : ℕ)
    (b : Fin n → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) :
    LinearIndependent (recB (h.laws v).p.toLawsCore).KO b → LinearIndependent ℂ (fun k => rdLin h ha (b k)) := by
  intro hb
  have hJ := (GlobalTheory.ReadingTieCheck.tieRead_holds (h.laws v).p ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩).2 (p.κ i)
  let b' : Fin n → cusp ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c ((r.used v).full.U ((i : ℕ) + 1))
      (wtA (p.κ i)) (p.κ i).n :=
    fun k => ⟨(b k).1, cutR_le (r.used v).full.C ((i : ℕ) + 1) (p.κ i) (b k).2⟩
  have hb' : LinearIndependent (r.used v).full.Q.c.F b' := by
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    apply Subtype.ext
    have h1 := congrArg Subtype.val hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at h1 ⊢
    exact h1
  have hR := hJ n b' hb'
  rw [Fintype.linearIndependent_iff] at hR ⊢
  intro g hg
  apply hR g
  have hoff : ∀ k, rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n (b' k) ∈
      offZero ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X :=
    fun k => rdU_mem_offZero _ _
  have claim : ∀ c, (∑ k, g k • rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n
      (b' k)) (e c) = 0 := by
    intro c
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).dom
    · have hy : castFrame (psi_eq ha c).symm x ∈ M.dom :=
        (mem_dom_iff ha c _).1 (by rw [castFrame_castFrame_symm]; exact hx)
      have := congrFun (congrFun hg c) ⟨_, hy⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, rdLin_apply, rdFun,
        castFrame_castFrame_symm] at this
      exact this
    · exact Finset.sum_eq_zero fun k _ => by rw [hoff k (e c) x hx, mul_zero]
  funext k'
  have := claim (e.symm k')
  rw [e.apply_symm_apply] at this
  exact this

end GlobalTheory.ShareOn.Reading
end
end

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_family_linearIndependent : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (n : ℕ) (b : Fin n → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), LinearIndependent (recB (h.laws v).p.toLawsCore).KO b → LinearIndependent ℂ (fun k => rdLin h ha (b k)) := by
  atlas_forward_decl GlobalTheory.ShareOn.Reading.rdLin_linearIndependent
end

section
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false

namespace GlobalTheory.ShareOn.Reading

section Onto
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ss_transport {X X' : Data E r} (hX : X = X') {Ψ : Finset (E →+* ℂ)} (h1 : X.Ψ = Ψ) (h2 : X'.Ψ = Ψ)
    (g : Frame Ψ r → ℂ) (la : Wt Ψ r) (la' : Wt X'.Ψ r)
    (hla : ∀ τ (t1 : τ ∈ Ψ) (t2 : τ ∈ X'.Ψ) a, la ⟨τ, t1⟩ a = la' ⟨τ, t2⟩ a)
    (hg : (fun x => g (castFrame h1 x)) ∈ X.SS (castWt h1 la)) :
    (fun y => g (castFrame h2 y)) ∈ X'.SS la' := by
  subst hX
  have hw : castWt h1 la = la' := by
    funext τ a
    exact hla τ.1 _ τ.2 a
  rw [← hw]
  exact hg

end Onto

theorem rdFun_onto {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
    {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C]
    {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) :
    0 < badN D → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (G : C → Frame M.Ψ D.R.r → ℂ), G ∈ M.SS ka →
      ∃ (m : ℕ) (α : Fin m → ℂ) (Fs : Fin m → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
        ∀ c, ∀ x ∈ M.dom, G c x = ∑ k, α k * rdFun h ha (Fs k) c x := by
  intro hN hnV G hG
  classical
  have ha' : ∀ k, (M.comp (e.symm k)).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k := fun k => by
    rw [ha (e.symm k), e.apply_symm_apply]
  have hΨk : ∀ k, M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ := fun k => by
    rw [← ha' k]; exact (M.comp_Ψ _).symm
  have hb' : ∀ k τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k ⟨τ, h2⟩ a := by
    intro k
    obtain ⟨c, rfl⟩ := e.surjective k
    exact hb c

  have hf : 0 < D.R.f := lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) i.2) D.R.m_le_f
  have hTau : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; exact hf
  obtain ⟨τ0⟩ := hTau
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (p.κ i).n := by
    rw [(p.fw.kap i τ0).2.2]; exact hnV
  have hOnto : RdOnto (h.laws v).p ((i : ℕ) + 1) (p.κ i) :=
    GlobalTheory.Shares.rdOnto_rec GlobalTheory.chartIndependence_unconditional D (r.used v).full.toTop (h.laws v).p ((i : ℕ) + 1)
      (GlobalTheory.OnTies.inR_succ i) (h.laws v).sh
      (GlobalTheory.RunIn.gamAt_of_lawsCore D _ (h.laws v).p.toLawsCore) hN
      (GlobalTheory.Dict.gram_xi_eq_of_lawsFull (h.laws v)) (p.κ i) hn
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA (h.laws v).p (GlobalTheory.OnTies.inR_succ i) _ (lastPos_kappa p i))
  let f : ∀ k : ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp, Frame (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ D.R.r → ℂ := fun k y => G (e.symm k) (castFrame (hΨk k).symm y)
  have hfm : ∀ k, f k ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).SS (laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k) := fun k =>
    ss_transport (ha' k) (M.comp_Ψ (e.symm k)) (hΨk k).symm (G (e.symm k)) ka _ (hb' k) (hG (e.symm k))
  obtain ⟨m, α, Fs, -, hsum⟩ := hOnto f hfm
  refine ⟨m, α, Fs, fun c x hx => ?_⟩
  have hy := (mem_dom_iff ha c x).2 hx
  have key := hsum (e c) _ hy
  have hl : f (e c) (castFrame (psi_eq ha c) x) = G c x := by
    show G (e.symm (e c)) (castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x)) = G c x
    have hc : e.symm (e c) = c := e.symm_apply_apply c
    have hx' : castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x) = x := rfl
    rw [hx', hc]
  rw [← hl, key]
  rfl

end GlobalTheory.ShareOn.Reading
end

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelCuspForms_span_usedRunReadings : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a), 0 < badN D → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (G : C → Frame M.Ψ D.R.r → ℂ), G ∈ M.SS ka → ∃ (m : ℕ) (α : Fin m → ℂ) (Fs : Fin m → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), ∀ c, ∀ x ∈ M.dom, G c x = ∑ k, α k * rdFun h ha (Fs k) c x := by
  atlas_forward_decl GlobalTheory.ShareOn.Reading.rdFun_onto
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn.Reading

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

open GlobalTheory.OnTies in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem reading_of_runModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type}
    [Finite C] [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (hb0 : 0 < badN D) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hM : RunModel p r h i M ka) :
    M.Ψ.card = D.R.f ∧ ∃ (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
      (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
      IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
      (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  refine ⟨card_of_runModel hM, ?_⟩
  obtain ⟨v, e, ha, hb, hc, -⟩ := hM
  obtain ⟨act, hact, hcu⟩ := h.action v i

  let Rd : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i) →ₛₗ[(r.used v).full.σ₀] M.cusp ka :=
    LinearMap.codRestrict (M.cusp ka) (rdLin h ha) fun F => Submodule.subset_span ⟨_, GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms h ha hb F, rfl⟩
  have hRd : ∀ F, ((Rd F : M.cusp ka) : C → M.dom → ℂ) = rdLin h ha F := fun F => rfl
  letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
  obtain ⟨σ, hσ⟩ := exists_ext_embedding (K := (r.used v).full.J.Q.c.F) (LL := D.what₂.LL) (r.used v).full.σ₀
  let cu := cuspTo (h.laws v).p (fw2 p) i
  have hcuW : ∀ F, cu F ∈ ((R2 p).FW i).WK := fun F => ((fw2 p).e i _).2
  have hcuinj : Function.Injective cu := by
    intro F G hFG
    have h1 := Subtype.ext hFG
    have h2 := ((fw2 p).e i).injective h1
    exact Submodule.inclusion_injective _ h2
  have hsurj : ∀ w ∈ ((R2 p).FW i).WK, ∃ F, cu F = w := by
    intro w hw
    refine ⟨⟨(((fw2 p).e i).symm ⟨w, hw⟩).1, by
      rw [cutR_eq _ (inR_succ i)]; exact (((fw2 p).e i).symm ⟨w, hw⟩).2⟩, ?_⟩
    show ((((fw2 p).e i) _ : ((R2 p).FW i).WK) : Fin _ → D.what₂.LL) = w
    exact congrArg Subtype.val (LinearEquiv.apply_symm_apply ((fw2 p).e i) ⟨w, hw⟩)
  obtain ⟨m, b', hbW, hbK, hspK, hbL, hspL⟩ := (fw2 p).ks i
  choose bC hbC using fun k => hsurj (b' k) (hbW k)
  have hbC' : (fun k => cu (bC k)) = b' := funext hbC
  have hbs : Submodule.span (recB (h.laws v).p.toLawsCore).KO (Set.range bC) = ⊤ := by
    rw [eq_top_iff]
    intro F _
    have h1 : cu F ∈ Submodule.span p.T.Q.c.F (Set.range b') := by rw [hspK]; exact hcuW F
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have h2 : cu (∑ k, (show (recB (h.laws v).p.toLawsCore).KO from cf k) • bC k) = cu F := by
      rw [map_sum, ← hcf]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbC k]
      rfl
    rw [← hcuinj h2]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hbi : LinearIndependent D.what₂.LL (fun k => cu (bC k)) := by rw [hbC']; exact hbL
  have hbt : Submodule.span D.what₂.LL (Set.range fun k => cu (bC k)) = ⊤ := by rw [hbC']; exact hspL
  have hK : LinearIndependent (recB (h.laws v).p.toLawsCore).KO bC := by
    apply LinearIndependent.of_comp cu
    show LinearIndependent _ (fun k => cu (bC k))
    rw [hbC']; exact hbK
  have hR : LinearIndependent ℂ (fun k => Rd (bC k)) :=
    LinearIndependent.of_comp (M.cusp ka).subtype (GlobalTheory.T.cuspForm_family_linearIndependent h ha m bC hK)
  have hRs : Submodule.span ℂ (Set.range Rd) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : y ∈ (Submodule.span ℂ (Set.range Rd)).map (M.cusp ka).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      unfold TwoLevels.cusp at hy
      refine Submodule.span_le.2 ?_ hy
      rintro _ ⟨G, hG, rfl⟩
      obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
      have hGs : M.res G = ∑ k, α k • rdLin h ha (Fs k) := by
        funext c x
        simp only [TwoLevels.res, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rdLin_apply]
        exact hGe c x.1 x.2
      rw [hGs]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fs k, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := hy'
    have hz' : z = ⟨y, hy⟩ := Subtype.ext hzy
    rw [← hz']; exact hz
  obtain ⟨f, ρ, hfcu, hint, hind, hspan⟩ := GlobalTheory.T.exists_semilinear_extension_of_form_with_transported_rep (r.used v).full.σ₀ σ hσ cu bC hbs hbi hbt Rd hR hRs ((R2 p).FW i).ρ
  have hρR : ∀ g F, ρ g (Rd F) = Rd (act g F) := by
    intro g F
    rw [← hfcu, ← hfcu, hint, hcu g F]
  obtain ⟨a, hpull⟩ := hc
  refine ⟨ρ, σ, f, ⟨a, fun g G hG c x => ?_⟩, hint, hind, hspan⟩
  obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
  have hy : (⟨M.res G, Submodule.subset_span ⟨G, hG, rfl⟩⟩ : M.cusp ka) = ∑ k, α k • Rd (Fs k) := by
    apply Subtype.ext
    funext c' x'
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TwoLevels.res, hRd,
      rdLin_apply]
    exact hGe c' x'.1 x'.2
  rw [hy, map_sum]
  simp only [map_smul, hρR, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hRd,
    rdLin_apply]
  rw [TwoLevels.pull, hGe (g • c) _ (GlobalTheory.T.twoLevelFlagDomain_transporter_mem_domain M g c x.1 x.2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hpull (Fs k) g c x.1 x.2 (psi_eq ha c) (psi_eq ha (g • c))
  rw [rdLin_apply]
  unfold rdFun rdR
  rw [hact g⁻¹ (Fs k)]
  refine (congrArg (α k * ·) hk).trans ?_
  ring
end Main2

end GlobalTheory.ShareOn.Reading
end
end

section
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipConjIdeal

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (x - y) z = ReciprocityTheory.ChartRestriction.G.FD.herm G x z - ReciprocityTheory.ChartRestriction.G.FD.herm G y z := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.herm, sub_mul, Finset.sum_sub_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (a : E) (x z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (a • x) z = a * ReciprocityTheory.ChartRestriction.G.FD.herm G x z := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (a : E) (x z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G x (a • z) = ReciprocityTheory.ChartRestriction.G.FD.cc a * ReciprocityTheory.ChartRestriction.G.FD.herm G x z := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem herm_adjoint_pow (G : Matrix (Fin r) (Fin r) E) (β : GL (Fin r) E)
    (hU : ∀ v w, ReciprocityTheory.ChartRestriction.G.FD.herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ v)
      ((β : Matrix (Fin r) (Fin r) E) *ᵥ w) = ReciprocityTheory.ChartRestriction.G.FD.herm G v w) (k : ℕ) (x y : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G ((((β : Matrix (Fin r) (Fin r) E) - 1) ^ k) *ᵥ x) y =
      ReciprocityTheory.ChartRestriction.G.FD.herm G x (((((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) - 1) ^ k) *ᵥ y) := by
  have step : ∀ x z : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G (((β : Matrix (Fin r) (Fin r) E) - 1) *ᵥ x) z =
      ReciprocityTheory.ChartRestriction.G.FD.herm G x ((((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) - 1) *ᵥ z) := by
    intro x z
    have hz : (β : Matrix (Fin r) (Fin r) E) *ᵥ (((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ z) = z := by
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, herm_sub_left]
    conv_lhs => rw [← hz, hU]
    simp [ReciprocityTheory.ChartRestriction.G.FD.herm, Finset.sum_sub_distrib, mul_sub, ReciprocityTheory.ChartRestriction.G.FD.cc]
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, step, mulVec_mulVec, ← pow_succ']

end GlobalTheory.UnipConjIdeal

namespace GlobalTheory.UnipConjIdeal

open Matrix

theorem pow_sub_one_mem_conj_ideal_smul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (β : GL (Fin r) E),
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v) (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) =
      herm X.Gm v w) →
    (∀ v, v ∈ X.L' ↔ Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v ∈ X.L') →
    ∀ P : Ideal (𝓞 E), (∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • X.L') →
    ∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈
      P.map ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E ≃+* 𝓞 E) : 𝓞 E →+* 𝓞 E) • X.L' := by
  intro E _ _ _ r X β hU hL P hP v hv
  have hsm : ∀ (p : 𝓞 E) (w : Fin r → E), p • w = (p : E) • w := fun p w => (algebraMap_smul E p w).symm
  set βm : Matrix (Fin r) (Fin r) E := (β : Matrix (Fin r) (Fin r) E) with hβm
  set βi : Matrix (Fin r) (Fin r) E := ((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hβi
  have h1 : βi * βm = 1 := Units.inv_mul β
  have h2 : βm * βi = 1 := Units.mul_inv β

  have hinv : ∀ w ∈ X.L', βi *ᵥ w ∈ X.L' := by
    intro w hw
    refine (hL _).mpr ?_
    rw [mulVec_mulVec, h2, one_mulVec]; exact hw
  have hBpow : ∀ k : ℕ, ∀ w ∈ X.L', ((-βi) ^ k) *ᵥ w ∈ X.L' := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', ← mulVec_mulVec, neg_mulVec]
      exact X.L'.neg_mem (hinv _ (ih w hw))

  have hfac : βi - 1 = (-βi) * (βm - 1) := by
    rw [neg_mul, mul_sub, h1, mul_one]; abel
  have hcomm : Commute (-βi) (βm - 1) := by
    unfold Commute SemiconjBy
    rw [neg_mul, mul_neg, mul_sub, sub_mul, h1, h2, mul_one, one_mul]
  have hadjpow : (βi - 1) ^ r = (-βi) ^ r * (βm - 1) ^ r := by
    rw [hfac, hcomm.mul_pow]
  by_cases hP0 : P = ⊥
  · subst hP0
    have h0 := hP v hv
    rw [Submodule.bot_smul, Submodule.mem_bot] at h0
    rw [h0]; exact zero_mem _
  obtain ⟨c, hcP, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨P', hPP'⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hcP)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc0

  have hi : ∀ w ∈ P • X.L', ∀ p' ∈ P', ((c : E)⁻¹ * p') • w ∈ X.L' := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro p hp l hl p' hp'
      have hm : p * p' ∈ Ideal.span {c} := by rw [hPP']; exact Ideal.mul_mem_mul hp hp'
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
      have : ((c : E)⁻¹ * p') • (p • l) = t • l := by
        rw [hsm, hsm, smul_smul]
        congr 1
        have : (p : E) * p' = t * c := by exact_mod_cast ht.symm
        field_simp
        linear_combination this
      rw [this]; exact X.L'.smul_mem t hl
    · intro x y hx hy p' hp'
      rw [smul_add]; exact X.L'.add_mem (hx p' hp') (hy p' hp')

  have hii : ∀ z ∈ X.L', ∀ p' ∈ P', ((c : E)⁻¹ * p') • (((βi - 1) ^ r) *ᵥ z) ∈ X.L' := by
    intro z hz p' hp'
    rw [hadjpow, ← mulVec_mulVec, ← mulVec_smul]
    exact hBpow r _ (hi _ (hP z hz) p' hp')

  set σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hσdef
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = ReciprocityTheory.ChartRestriction.G.FD.cc (x : E) := fun x => rfl
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc (ReciprocityTheory.ChartRestriction.G.FD.cc x) = x := by
    intro x; simp [ReciprocityTheory.ChartRestriction.G.FD.cc]

  have hiii : ∀ p' ∈ P', ((σ c : E)⁻¹ * (σ p' : E)) • (((βm - 1) ^ r) *ᵥ v) ∈ X.L' := by
    intro p' hp'
    refine X.L'_dual _ fun z hz => ?_
    rw [herm_smul_left, herm_adjoint_pow X.Gm β hU r v z]
    have : (σ c : E)⁻¹ * (σ p' : E) = ReciprocityTheory.ChartRestriction.G.FD.cc ((c : E)⁻¹ * p') := by
      rw [hσ, hσ, ReciprocityTheory.ChartRestriction.G.FD.cc, ReciprocityTheory.ChartRestriction.G.FD.cc, ReciprocityTheory.ChartRestriction.G.FD.cc, map_mul, map_inv₀]
    rw [this, ← herm_smul_right]
    exact X.L'_int v hv _ (hii z hz p' hp')

  have hmul : P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) = Ideal.span {σ c} := by
    rw [← Ideal.map_mul, ← hPP', Ideal.map_span, Set.image_singleton]; rfl
  have hd : σ c ∈ P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) := by
    rw [hmul]; exact Ideal.mem_span_singleton_self _
  have hσc : (σ c : E) ≠ 0 := by
    intro h; apply hcE
    have := congrArg ReciprocityTheory.ChartRestriction.G.FD.cc h
    rw [hσ, hcc] at this
    simpa [ReciprocityTheory.ChartRestriction.G.FD.cc] using this
  have key : ∀ u, u ∈ P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) →
      ((σ c : E)⁻¹ * u) • (((βm - 1) ^ r) *ᵥ v) ∈ P.map (σ : 𝓞 E →+* 𝓞 E) • X.L' := by
    intro u hu
    refine Submodule.mul_induction_on hu ?_ ?_
    · intro q hq q' hq'
      obtain ⟨p', hp', rfl⟩ := (Ideal.mem_map_of_equiv σ q').mp hq'
      have : ((σ c : E)⁻¹ * ((q * σ p' : 𝓞 E) : E)) • (((βm - 1) ^ r) *ᵥ v) =
          q • (((σ c : E)⁻¹ * (σ p' : E)) • (((βm - 1) ^ r) *ᵥ v)) := by
        rw [hsm, smul_smul]; congr 1; push_cast; ring
      rw [this]
      exact Submodule.smul_mem_smul hq (hiii p' hp')
    · intro x y hx hy
      rw [show ((x + y : 𝓞 E) : E) = (x : E) + y by push_cast; rfl, mul_add, add_smul]
      exact Submodule.add_mem _ hx hy
  have := key _ hd
  rwa [inv_mul_cancel₀ hσc, one_smul] at this

end GlobalTheory.UnipConjIdeal
end

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_unipotent_mod_ideal_mod_conjIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (β : GL (Fin r) E),
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v) (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) =
      herm X.Gm v w) →
    (∀ v, v ∈ X.L' ↔ Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v ∈ X.L') →
    ∀ P : Ideal (𝓞 E), (∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • X.L') →
    ∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈
      P.map ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E ≃+* 𝓞 E) : 𝓞 E →+* 𝓞 E) • X.L' := by
  atlas_forward_decl GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul
end

section
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipModHalf

theorem zpow_sub_one_eq_mul {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (ℓ : A ≃ₗ[R] A) (n : ℤ) :
    ∃ X : Module.End R A, Commute ((ℓ : Module.End R A) - 1) X ∧
      ((ℓ ^ n : A ≃ₗ[R] A) : Module.End R A) - 1 = ((ℓ : Module.End R A) - 1) * X := by
  have h1 : (ℓ.symm : Module.End R A) * (ℓ : Module.End R A) = 1 := by
    ext y; simp
  have h2 : (ℓ : Module.End R A) * (ℓ.symm : Module.End R A) = 1 := by
    ext y; simp
  have hDℓ : Commute ((ℓ : Module.End R A) - 1) (ℓ : Module.End R A) :=
    (Commute.refl _).sub_left (Commute.one_left _)
  have hDs : Commute ((ℓ : Module.End R A) - 1) (ℓ.symm : Module.End R A) := by
    show _ = _
    rw [sub_mul, mul_sub, h2, h1, one_mul, mul_one]
  induction n using Int.induction_on with
  | zero => exact ⟨0, Commute.zero_right _, by ext y; simp⟩
  | succ k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ : Module.End R A) * X + 1, (hDℓ.mul_right hc).add_right (Commute.one_right _), ?_⟩
    have e : ((ℓ ^ ((k : ℤ) + 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ : Module.End R A) * ((ℓ ^ (k : ℤ) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [add_comm, zpow_add, zpow_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    noncomm_ring
  | pred k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ.symm : Module.End R A) * X - (ℓ.symm : Module.End R A),
      (hDs.mul_right hc).sub_right hDs, ?_⟩
    have e : ((ℓ ^ (-(k : ℤ) - 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ.symm : Module.End R A) * ((ℓ ^ (-(k : ℤ)) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [sub_eq_neg_add, zpow_add, zpow_neg_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    set s : Module.End R A := (ℓ.symm : Module.End R A)
    set l : Module.End R A := (ℓ : Module.End R A)
    have : s * ((l - 1) * X + 1) - 1 = (l - 1) * (s * X - s) + (s * l - 1) * X
        - (l * s - 1) * X + (l * s - 1) := by noncomm_ring
    rw [this, h1, h2]; simp

end GlobalTheory.UnipModHalf

namespace GlobalTheory.UnipModHalf

open Matrix

theorem unip_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  intro E _ _ r L' Mb P hMP A _ _ φ ℓ n hℓ γ t hγ hγ1 ht w hw

  let tL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin t).restrictScalars (𝓞 E)
  let gL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin γ).restrictScalars (𝓞 E)
  let T : Module.End (𝓞 E) L' := tL.restrict (fun x hx => (ht ⟨x, hx⟩).1)
  let G : Module.End (𝓞 E) L' := gL.restrict (fun x hx => hγ x hx)
  let U : Module.End (𝓞 E) L' := G * T - 1
  have hU : ∀ x : L', ((U x : L') : Fin r → E) = γ *ᵥ (t *ᵥ (x : Fin r → E)) - x := by
    intro x; rfl
  have hpow : ∀ k : ℕ, ∀ x : L', ((γ * t - 1) ^ k) *ᵥ (x : Fin r → E) = (((U ^ k) x : L') : Fin r → E) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, pow_succ', Module.End.mul_apply, hU,
        Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]

  have hsub : ∀ (I : Ideal (𝓞 E)) (z : L'), (z : Fin r → E) ∈ I • L' → z ∈ I • (⊤ : Submodule (𝓞 E) L') := by
    intro I z hz
    have e : I • L' = (I • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [e] at hz
    obtain ⟨u, hu, huz⟩ := hz
    have : u = z := Subtype.ext huz
    exact this ▸ hu
  set ℓn : Module.End (𝓞 E) A := ((ℓ ^ n : A ≃ₗ[𝓞 E] A) : Module.End (𝓞 E) A)
  have hπU : ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (U x) = φ ((ℓn - 1) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro x
    have hG : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (G (T x)) = (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hsub Mb _ (hγ1 _ (T x).2)
    have hT : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) = φ ((ℓ ^ n) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := (ht x).2
    simp only [U, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, map_sub, hG, hT]
    simp [ℓn]
  have hπUk : ∀ k : ℕ, ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ k) x) = φ (((ℓn - 1) ^ k) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, hπU, ih, LinearEquiv.symm_apply_apply, pow_succ',
        Module.End.mul_apply]

  obtain ⟨X, hc, hX⟩ := zpow_sub_one_eq_mul ℓ n
  have hℓ' : ∀ y : A, ((ℓn - 1) ^ r) y ∈ P • (⊤ : Submodule (𝓞 E) A) := by
    intro y
    rw [show ℓn - 1 = ((ℓ : Module.End (𝓞 E) A) - 1) * X from hX, hc.mul_pow, Module.End.mul_apply]
    have := hℓ ((X ^ r) y)
    rwa [← Module.End.one_eq_id] at this

  have hQ : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ r) ⟨w, hw⟩) ∈ P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) := by
    rw [hπUk]
    have hm : ((P • (⊤ : Submodule (𝓞 E) A)).map (φ : A →ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))) ≤ P • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact hm (Submodule.mem_map_of_mem (hℓ' _))
  have hL : (U ^ r) ⟨w, hw⟩ ∈ P • (⊤ : Submodule (𝓞 E) L') := by
    have e : P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) = (P • (⊤ : Submodule (𝓞 E) L')).map (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [e] at hQ
    have hQ' := Submodule.mem_comap.mpr hQ
    rw [Submodule.comap_map_mkQ] at hQ'
    have hle : Mb • (⊤ : Submodule (𝓞 E) L') ≤ P • (⊤ : Submodule (𝓞 E) L') := Submodule.smul_mono_left hMP
    exact (sup_le hle le_rfl) hQ'
  have key := hpow r ⟨w, hw⟩
  simp only at key
  rw [key]
  have e : P • L' = (P • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [e]
  exact Submodule.mem_map_of_mem hL

end GlobalTheory.UnipModHalf
end

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  atlas_forward_decl GlobalTheory.UnipModHalf.unip_mod_half
end

section
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShareOn.UnipLevel

theorem pow_apply_eq_zero_of_strict {K : Type} [CommRing K] {n : ℕ} (S : Matrix (Fin n) (Fin n) K)
    (hS : ∀ a b : Fin n, b ≤ a → S a b = 0) (m : ℕ) :
    ∀ a b : Fin n, (b : ℕ) < a + m → (S ^ m) a b = 0 := by
  induction m with
  | zero =>
    intro a b h
    rw [pow_zero, Matrix.one_apply, if_neg]
    intro hab
    rw [hab] at h
    omega
  | succ m ih =>
    intro a b h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : b ≤ j
    · rw [hS j b hj, mul_zero]
    · have hj' : (j : ℕ) < a + m := by
        have : (j : ℕ) < b := Fin.lt_def.1 (not_le.1 hj)
        omega
      rw [ih a j hj', zero_mul]

end GlobalTheory.ShareOn.UnipLevel
namespace GlobalTheory.ShareOn.UnipLevel

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem levUnip_mod_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → ∀ (i : Fin D.R.m) (u : p.P.Gp) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) →
    ∀ x : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l,
      (((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ D.R.r) x ∈
        ((D.naut.plGw k v).asIdeal • ⊤ : Submodule (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p r hr i u k v hU x
  classical
  obtain ⟨v'⟩ := GlobalTheory.ShareOn.nonempty_place D
  have hlev : Formalism.IndefR.FWT.LevIs (R2 p) i (Formalism.IndefR.FWT.iotaW p.T i) p.T.Q.l.M (Mfr p.T.Q.l)
      (fun g => liftLa (r.lev i g)) := hr.level v' i
  have hL := hr.laws v'
  have hι : LatEmb (Wc D i) (Formalism.IndefR.FWT.iotaW p.T i) := GlobalTheory.TraceLattice.latEmb_iotaW hL i
  have hβ : IsSDFrame (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) 1 := p.charW.base.lev.βW i
  obtain ⟨plg, iso, hplg, -, -, hG⟩ := p.grpRecPin
  have hrk : D.R.r = (p.T.Q.Dw ((i : ℕ) + 1)).p + (p.T.Q.Dw ((i : ℕ) + 1)).q :=
    (hL.j.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ (r.used v').full.toCore.good_σ₀).1
  set PPs := plg ⟨k, v⟩ with hPPs
  obtain ⟨φ, hφs, hφk⟩ := GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer D (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) hβ _ _ hι PPs.1
  obtain ⟨κ, hκ, hκa⟩ := hlev u
  have hMbP : p.T.Q.l.Mb ≤ PPs.1.asIdeal := by
    rw [hr.half]
    exact Ideal.prod_le_inf.trans (Finset.inf_le PPs.2)
  have hM : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PPs.1.asIdeal := hMbP (GlobalTheory.LevDesc.natCast_M_mem _)
  have hSt : Lev.finE (Wc D i) κ ∈ St ((R2 p).βW i) := parLev_St hκ.2.1
  have hkill : ∀ c ∈ PPs.1.asIdeal, ∀ y, φ (c • y) = 0 := by
    intro c hc y
    rw [map_smul]
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_mul]
  have hcop : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  obtain ⟨c₁, hc₁, w, hw, hcw⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ p.T.Q.l.Mb ⊔ Mfr p.T.Q.l)
  set f := liftLa (r.lev i u) with hf
  set N : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP PPs.1) :=
    (redFn ((R2 p).βW i) PPs.1 (Lev.finE (Wc D i) κ)).1 with hN
  have hfφ : ∀ a, φ (f a) = N *ᵥ φ a := by
    intro a
    have ha : a = c₁ • a + w • a := by rw [← add_smul, hcw, one_smul]
    have h1 := hφk κ hSt p.T.Q.l.M hM (w • a) (f (w • a)) (hκa (w • a) (Submodule.smul_mem_smul hw Submodule.mem_top))
    have h2 : φ (w • a) = φ a := by
      conv_rhs => rw [ha]
      rw [map_add, hkill c₁ (hMbP hc₁), zero_add]
    have h3 : φ (f a) = φ (f (w • a)) := by
      conv_lhs => rw [ha]
      rw [map_add, map_add, map_smul, hkill c₁ (hMbP hc₁), zero_add]
    rw [h3, h1, h2]
  have hrank : (Wc D i).rank = D.R.r := Formalism.IndefR.FWT.rank_Wc i
  have h5 : (R2 p).eG u PPs = upperLeftBlock ((R2 p).datWp i (R2 p).triv).hr (redFn ((R2 p).βW i) PPs.1 (Lev.finE (Wc D i) κ)) :=
    (congrFun hκ.2.2 PPs).symm
  have h6 := upper_block_val_submatrix ((R2 p).datWp i (R2 p).triv).hr (blockTri_blkOf_le _ _ (parLev_g hκ.2.1 PPs.2))
  have h7 : (R2 p).eG u PPs = Formalism.UG.bc (iso ⟨k, v⟩ : ZMod (D.host.g k) →+* kP PPs.1) ((p.R.eG.trans p.cG) u ⟨k, v⟩) :=
    hG u ⟨k, v⟩
  rw [← h5, h7] at h6
  have hsub : ∀ a' b' : Fin D.R.r, N (Fin.castLE ((R2 p).datWp i (R2 p).triv).hr a') (Fin.castLE ((R2 p).datWp i (R2 p).triv).hr b') =
      iso ⟨k, v⟩ ((((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) a' b') := by
    intro a' b'
    have := congrFun (congrFun h6 a') b'
    exact this.symm
  have hstrict : ∀ a b : Fin (Wc D i).rank, b ≤ a → (N - 1) a b = 0 := by
    intro a b hab
    have ha' : (a : ℕ) < D.R.r := hrank ▸ a.2
    have hb' : (b : ℕ) < D.R.r := hrank ▸ b.2
    have e1 : N a b = iso ⟨k, v⟩ ((((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))
        ⟨a, ha'⟩ ⟨b, hb'⟩) := hsub ⟨a, ha'⟩ ⟨b, hb'⟩
    rw [Matrix.sub_apply, e1]
    rcases lt_or_eq_of_le hab with h | h
    · rw [(hU ⟨a, ha'⟩ ⟨b, hb'⟩).1 h, map_zero, Matrix.one_apply_ne (ne_of_gt h), sub_zero]
    · have hab' : (⟨a, ha'⟩ : Fin D.R.r) = ⟨b, hb'⟩ := by
        ext; show (a : ℕ) = b; rw [h]
      rw [(hU ⟨a, ha'⟩ ⟨b, hb'⟩).2 hab', map_one, h, Matrix.one_apply_eq, sub_self]
  have hnil : (N - 1) ^ D.R.r = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    exact pow_apply_eq_zero_of_strict _ hstrict D.R.r a b (by have := b.2; omega)
  have hpow : ∀ (m : ℕ) a, φ (((f - LinearMap.id : Module.End (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ^ m) a) = ((N - 1) ^ m) *ᵥ φ a := by
    intro m
    induction m with
    | zero => intro a; rw [pow_zero, pow_zero, Module.End.one_apply, Matrix.one_mulVec]
    | succ m ih =>
      intro a
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, hfφ, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hker : ∀ y, φ y = 0 → y ∈ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
    intro y hy
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    haveI hfin : Finite (kP PPs.1) := Finite.of_equiv _ (iso ⟨k, v⟩).toEquiv
    haveI : Finite (𝓞 D.host.E ⧸ PPs.1.asIdeal) := hfin
    haveI := (p.T.Q.Dw ((i : ℕ) + 1)).fin
    haveI := (p.T.Q.Dw ((i : ℕ) + 1)).proj
    have hle : PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ≤ LinearMap.ker φ := by
      rw [Submodule.smul_le]
      intro c hc z _
      exact hkill c hc z
    let ψ := (PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).liftQ φ hle
    have hψs : Function.Surjective ψ := by
      intro z
      obtain ⟨y', rfl⟩ := hφs z
      exact ⟨Submodule.Quotient.mk y', rfl⟩
    have hc0 : Nat.card (kP PPs.1) ≠ 0 := Nat.card_pos.ne'
    have hN1 : Nat.card ((p.T.Q.Dw ((i : ℕ) + 1)).La ⧸ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) =
        Nat.card (kP PPs.1) ^ (Wc D i).rank := by
      rw [GlobalTheory.natCard_quot_smul_top_of_projective, (p.T.Q.Dw ((i : ℕ) + 1)).rank, ← hrk, hrank]
    have hN2 : Nat.card (Fin (Wc D i).rank → kP PPs.1) = Nat.card (kP PPs.1) ^ (Wc D i).rank := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
    haveI : Finite ((p.T.Q.Dw ((i : ℕ) + 1)).La ⧸ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) :=
      Nat.finite_of_card_ne_zero (by rw [hN1]; exact pow_ne_zero _ hc0)
    have hb := hψs.bijective_of_nat_card_le (by rw [hN1, hN2])
    have h0 : ψ (Submodule.Quotient.mk y) = ψ 0 := by
      rw [map_zero]
      exact hy
    exact (Submodule.Quotient.mk_eq_zero _).1 (hb.1 h0)
  have hmk : ∀ (m : ℕ) a, ((((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ m)
      ((p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).mkQ a)) =
      (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).mkQ
        (((f - LinearMap.id : Module.End (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ^ m) a) := by
    intro m
    induction m with
    | zero => intro a; rfl
    | succ m ih =>
      intro a
      rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, hf, ← liftLa_spec,
        ← map_sub, ← hf, ih, pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.id_apply]
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hP : ((plg ⟨k, v⟩ : ↥p.R.Pg) : Pl D.host.E) = D.naut.plGw k v := hplg ⟨k, v⟩
  rw [← hP, ← hPPs]
  have hx := hmk D.R.r a
  rw [Submodule.mkQ_apply] at hx
  rw [hx]
  refine GlobalTheory.LevDesc.map_mem_smul_top _ (hker _ ?_)
  rw [hpow, hnil, Matrix.zero_mulVec]

end GlobalTheory.ShareOn.UnipLevel

end
end

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChange_unitriangular_unipotent_modPlace : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → ∀ (i : Fin D.R.m) (u : p.P.Gp) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) →
    ∀ x : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l,
      (((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ D.R.r) x ∈
        ((D.naut.plGw k v).asIdeal • ⊤ : Submodule (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) := by
  atlas_forward_decl GlobalTheory.ShareOn.UnipLevel.levUnip_mod_place
end

section
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesOnto

theorem prime_eq_plGw_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  intro D k P hP hg
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hg
    have h0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) = ((0 : ℕ) : 𝓞 D.host.E) := by simpa using hg
    have := Nat.cast_injective h0
    exact (D.host.g_prime k).ne_zero this
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP, hne⟩
  have hw : w ∈ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := hg
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlacesExhaust.eq_plGw_or_isConjPl D k w hw
  · exact ⟨v, Or.inl (congrArg HeightOneSpectrum.asIdeal hv)⟩
  · refine ⟨v, Or.inr ?_⟩
    set c : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
      RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv with hc
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap]
    have key : (y : D.host.E) = D.host.conj ((c.symm y : 𝓞 D.host.E) : D.host.E) := by
      rw [← GlobalTheory.HeightCounting.FormsStep.complexConj_eq_hostConj]
      have : c (c.symm y) = y := c.apply_symm_apply y
      rw [← congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) this]
      rfl
    exact ((hv (c.symm y) y key).symm.trans Iff.rfl)
end GlobalTheory.TypePrimesOnto
end

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_over_typePrime_fixedPlace_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  atlas_forward_decl GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitsCompletely_typePrime (D : D7) (k : Fin 2) : SplitsCompletely D.host.E (D.host.g k) := by
  refine ⟨D.host.g_prime k, ?_⟩
  have hg0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  have h := D.nd.g_split k
  rw [← h]
  have : {P : Ideal (𝓞 D.host.E) | P.IsPrime ∧ ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P} =
      (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.asIdeal) '' {v : HeightOneSpectrum (𝓞 D.host.E) | ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} := by
    ext P
    constructor
    · rintro ⟨hP, hg⟩
      have hne : P ≠ ⊥ := fun h0 => hg0 (by rw [h0] at hg; simpa using hg)
      exact ⟨⟨P, hP, hne⟩, hg, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, hv⟩
  rw [this, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem half_le_plGw (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (k : Fin 2) (v : D.nd.PlG k) :
    p.T.Q.l.Mb ≤ (D.naut.plGw k v).asIdeal := by
  rw [h.half]
  obtain ⟨plg, -, hplg, -, -, -⟩ := p.grpRecPin
  have hmem : D.naut.plGw k v ∈ (R2 p).Pg := by
    rw [← hplg ⟨k, v⟩]
    exact (plg ⟨k, v⟩).2
  exact (Ideal.prod_le_inf).trans (Finset.inf_le hmem)

theorem levelCondition_restrict_of_halfUnipotent (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type} [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r) (hg : ∀ k : Fin 2, 3 * D.R.r < D.host.g k)
    (hM : RunModel p r h i M ka) : ∀ H : Subgroup p.P.Gp, HalfUnip p H → LevelHyp (sub M H) := by
  intro H hH
  obtain ⟨k, hk⟩ := hH
  obtain ⟨v0, e, -, -, -, hd1, φ, hd2⟩ := hM
  refine ⟨D.host.g k, splitsCompletely_typePrime D k, hg k, ?_⟩
  intro c β hβ P hP hgP
  obtain ⟨u, huc, γ, hγ, rfl⟩ := hβ
  have huc' : (u : p.P.Gp) • c = c := huc
  have hγL : ∀ w, w ∈ (M.comp c).L' ↔ Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' :=
    M.Γ_L' c γ hγ
  have htL : ∀ w, w ∈ (M.comp c).L' ↔
      Matrix.mulVec (M.tr u c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' := by
    intro w
    have := M.tr_L' u c w
    rwa [huc'] at this
  have half : ∀ v : D.nd.PlG k, ∀ w ∈ (M.comp c).L',
      Matrix.mulVec ((((γ * M.tr u c : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) - 1) ^ D.R.r) w ∈
        (D.naut.plGw k v).asIdeal • (M.comp c).L' := by
    intro v w hw
    obtain ⟨n, hn⟩ := hd2 c u huc'
    rw [Units.val_mul]
    exact GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half _ _ _ (half_le_plGw p r h k v) (φ c) (r.lev i u) n (GlobalTheory.T.levelChange_unitriangular_unipotent_modPlace p r h i u k v (hk u u.2 v)) _ _ (fun w hw => (hγL w).1 hw)
      (hd1 c γ hγ) hn w hw
  obtain ⟨v, rfl | rfl⟩ := GlobalTheory.T.prime_over_typePrime_fixedPlace_or_conj D k P hP hgP
  · exact half v
  · refine GlobalTheory.T.unitary_unipotent_mod_ideal_mod_conjIdeal (M.comp c) (γ * M.tr u c) ?_ ?_ _ (half v)
    · intro a b
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ((M.comp c).Γ_stab γ hγ).1, M.comp_Gm c, M.tr_herm]
    · intro a
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (htL a).trans (hγL _)

end GlobalTheory.ShareOn

end
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem modelSt : ModelSt := by
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and runModel_arch GlobalTheory.BigOn.typePrimes_gt_three_r) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := EvPt.and hx0.1 hx0.2
  refine ⟨x0, fun x hx hle ι p hrows hmore r hr hown i => ?_⟩
  obtain ⟨harch, hg⟩ := hx0 x hx hle ι p hrows
  obtain ⟨C, hfin, hact, M, ka, hRM⟩ := exists_runModel p hmore r hr hown i
  have hb0 : 0 < badN (Fm.D x ι) := by
    obtain ⟨v, -⟩ := hRM
    exact (GlobalTheory.TrivLevel.badN_pos_iff _).2 (hmore.2.1.fieldAt v).bad
  obtain ⟨hcard, ρ, σ, f, h1, h2, h3, h4⟩ :=
    Reading.reading_of_runModel p r hr i M ka hb0 (Fm.parT x hx ι).nV_ge hRM
  exact ⟨C, hfin, hact, M, ka, ρ, σ, f, h1, h2, h3, h4, levelCondition_restrict_of_halfUnipotent p r hr i M ka (hg hmore) hRM, hcard,
    harch hmore r hr hown i C M ka hRM⟩

end GlobalTheory.ShareOn

end
end
