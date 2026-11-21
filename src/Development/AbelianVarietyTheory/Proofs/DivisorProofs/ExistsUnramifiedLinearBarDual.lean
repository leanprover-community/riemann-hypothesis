import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SplitEmbed

theorem exists_algHom_of_splitsFully : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ σ h v hs
  classical
  haveI hprime : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hne : v.asIdeal.under ℤ ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) hb)
  obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.principal (v.asIdeal.under ℤ))
  have hq' : v.asIdeal.under ℤ = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hne (by rw [hq']; simp)
  have hqp : Prime q := by
    rw [← Ideal.span_singleton_prime hq0, ← hq']
    exact hprime
  set p := q.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [hq', hpdef, Int.span_natAbs]
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
    have : (p : ℤ) ∈ v.asIdeal.under ℤ := by rw [hspan]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have hcount : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
    have := hs
    unfold SplitsFully at this
    rw [hspan] at this
    exact this
  rw [GlobalTheory.AdelicU.nonempty_split_iff h]
  exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two h.2.2.1 hp hcount v hpv

end GlobalTheory.SplitEmbed
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_embedding_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  first | exact @GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | exact GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | (intros; apply GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.SplitUnitLiftCont

open GlobalTheory.SplitGLLift GlobalTheory.SplitUnitLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem continuous_liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    Continuous (liftPair h τ) := by
  have hj : Continuous (LinearMap.inr F (Ainf F) (Af F) ∘ₗ GlobalTheory.AdelicU.singleFin v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  have h1 : Continuous (GlobalTheory.AdelicU.Supp.singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ hj
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have h2 : Continuous ((splitAlgEquiv h τ).symm : Fv F v × Fv F v → Fv F v ⊗[F] E) :=
    IsModuleTopology.continuous_of_linearMap (splitAlgEquiv h τ).symm.toLinearMap
  exact h1.comp h2

theorem continuous_liftMat (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} :
    Continuous (liftMat (n := Fin n) h τ) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun p : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v) =>
    liftPair h τ (p.1 i j, p.2 i j)
  exact (continuous_liftPair h τ).comp
    (((continuous_fst.matrix_elem i j)).prodMk (continuous_snd.matrix_elem i j))

theorem continuous_liftN (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map τ).det) : Continuous (liftN h τ J hJ) := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hp : Continuous (pairHom (J.map τ) hJ) := by
    show Continuous fun g : GL (Fin n) (Fv F v) => ((g : Matrix (Fin n) (Fin n) (Fv F v)),
      (J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)
    refine Units.continuous_val.prodMk ?_
    exact (continuous_const.matrix_mul (Units.continuous_coe_inv.matrix_transpose)).matrix_mul continuous_const
  show Continuous fun g => 1 + liftMat h τ (pairHom (J.map τ) hJ g - 1)
  exact continuous_const.add ((continuous_liftMat h τ).comp (hp.sub continuous_const))

theorem continuous_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    Continuous (liftU h τ J ε herm hJ) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.2 ⟨continuous_liftN h τ J hJ, ?_⟩
  exact (continuous_liftN h τ J hJ).comp continuous_inv

theorem tendsto_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    Tendsto (liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := by
  have := (continuous_liftU h τ J ε herm hJ).tendsto 1
  rwa [map_one] at this

theorem tendsto_liftU_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n : ℕ} (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F) (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det), Tendsto (GlobalTheory.SplitUnitLift.liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := fun h τ J ε herm hJ => tendsto_liftU h τ J ε herm hJ

end GlobalTheory.SplitUnitLiftCont

end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_unitary_lift_tendsto_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n : ℕ} (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F) (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det), Tendsto (GlobalTheory.SplitUnitLift.liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := by
  first | exact @GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | exact GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | (intros; apply GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SmoothCharDet

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

theorem isSmoothChar_of_detChar_apow_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  intro k _ _ _ _ n hn ν s P hP hν
  let i0 : Fin n := ⟨0, hn⟩
  let d : kˣ →* GL (Fin n) k :=
    (diagHom (k := k) (n := Fin n)).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i0)
  have hval : Continuous fun x : kˣ => ((d x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    show Continuous fun x : kˣ => diagonal fun i => (((Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x) i : kˣ) : k)
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp ((continuous_apply i).comp (continuous_mulSingle (A := fun _ : Fin n => kˣ) i0)))
  have hd : Continuous d := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have := hval.comp continuous_inv
    simpa [Function.comp_def, map_inv] using this
  have hdet : ∀ x : kˣ, gdet (d x) = x := fun x => by
    show Matrix.GeneralLinearGroup.det (diagGL (Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x)) = x
    rw [det_diagGL]
    simp
  have hU : (d : kˣ → GL (Fin n) k) ⁻¹' (P ∩ (KO k (Fin n) : Set (GL (Fin n) k))) ∈ 𝓝 (1 : kˣ) := by
    refine hd.continuousAt.preimage_mem_nhds ?_
    rw [map_one]
    exact Filter.inter_mem hP (isOpen_KO.mem_nhds (one_mem _))
  refine Subgroup.isOpen_of_mem_nhds ν.ker (Filter.mem_of_superset hU fun x hx => ?_)
  have h1 := hν _ hx.1
  rw [apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.2), mul_one, hdet] at h1
  exact MonoidHom.mem_ker.2 (Units.ext h1)

end GlobalTheory.SmoothCharDet
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_character_of_trivial_near_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  atlas_forward_decl GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeilTransferW

theorem local_weil_operator_second_space : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (h : UA σ G.W.J), h ∈ UAt σ G.W (evFin F v) →
    ∃ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (1, h)) φ (S φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
        S (c • φ + φ') = c • S φ + S φ') ∧
      (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (actAB (cA σ) ((1 : UA σ G.V'.J), h) γ)) (S φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ = 0 → φ = 0) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v h hh
  have hone : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by simp [mat]
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v
  choose! S hS using fun φ (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) => (hex 1 hone h hh φ hφ).exists
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  have eqR : ∀ φ₁ φ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R → φ₁ = φ₂ := by
    intro φ₁ φ₂ e0
    have hRc := (hR 0 (Submodule.zero_mem _)).1
    funext y
    have hp : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have e := congrFun e0 (fun i => GlobalTheory.LatVac.liftV v (y i))
    have e2 : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hRc 0 _ hp
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, e2] at e
    exact mul_right_cancel₀ hR0 e
  have hSR : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), om' (1, h) (tens (evFin F v) φ R) = tens (evFin F v) (S φ) R :=
    fun φ hφ => (hS φ hφ).2 R (hR φ hφ)
  have tensLin : ∀ (c : ℂ) (φ φ' : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • φ + φ') R = c • tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro c φ φ'; funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have atAct : ∀ (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) ((1 : UA σ G.V'.J), h) γ) := by
    intro γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have restS : ∀ φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (S φ) r :=
    fun φ r hφ hr => ⟨hr.1, by rw [← (hS φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro φ hφ φ' hφ' c
    have hm : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    apply eqR
    rw [← hSR _ hm, tensLin, map_add, map_smul, hSR φ hφ, hSR φ' hφ', tensLin]
  · intro γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct γ hγ) (S φ) r (restS φ r hφ hr)]
  · intro φ hφ h0
    apply eqR φ 0
    have e1 : om' (1, h⁻¹) (om' (1, h) (tens (evFin F v) φ R)) = tens (evFin F v) φ R := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel]
      rw [show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply]
    have t0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R = 0 := by
      funext x; simp [tens]
    rw [hSR φ hφ, h0, t0, map_zero] at e1
    rw [← e1, t0]

theorem atHTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl F} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (cA σ) (incM F JA) (incM F JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem sumLinForm {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem sumMulRight {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (g : Matrix n n K) (Y L : Matrix m n K) :
    ∑ k, ∑ j, (Y * g) k j * L k j = ∑ k, ∑ j, Y k j * (L * gᵀ) k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem linBar_right_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (h : UA σ G.W.J) (g : GL (Fin (a + a')) (Fv F v)), h ∈ UAt σ G.W (evFin F v) →
    (mat h).map (piW t) = g.val →
    (mat h).map (piW (t.comp σ)) = (G.W.J.map t)⁻¹ * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)ᵀ * G.W.J.map t →
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
        S (c • φ + φ') = c • S φ + S φ') →
      (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (actAB (cA σ) ((1 : UA σ G.V'.J), h) γ)) (S φ)) →
      ∀ ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ),
        G.M'.IsLinBar B.ψ t 1 1 ι →
        ∃ c : ℂ, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S φ) = c • fun Y => ι φ (Y * g.val) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v t h g hh ht hts S hSB hlin hcov ι hι
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd := hT.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set A := G.V'.J.map t with hAdef
  set Bm := G.W.J.map t with hBdef
  have hA : IsUnit A.det := GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w)
    (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have hBm : IsUnit Bm.det := GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero
    (G.W.θ w) (hT.geo.hW.cartan w)
  have hB : IsUnit Bmᵀ.det := by rw [Matrix.det_transpose]; exact hBm
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F v)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  let Pm : Matrix (Fin a') (Fin (a + a')) (Fv F v) → Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    fun C => -(A⁻¹ * C * (Bmᵀ)⁻¹)
  let Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) →
      Matrix (Fin a') (Fin (a + a')) (Fv F v) := fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (t.comp σ)) * Bmᵀ) = C := by
    intro C
    rw [hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW t) = 0 →
      u.map (piW (t.comp σ)) = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v
          (-(∑ k, ∑ j, (-(A * x.map (piW (t.comp σ)) * Bmᵀ)) k j * u.map (piW t) k j)) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ (atHTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm t G.V'.J G.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]
    rfl

  have hL := hι
  unfold Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have htr := hL.trans
  have hmu := hL.mult
  have hact : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), actAB (cA σ) ((1 : UA σ G.V'.J), h) u = u * (mat h)ᵀ := by
    intro u; simp [actAB, mat]
  have hat : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) u → At (evFin F v) (u * (mat h)ᵀ) := by
    intro u hu r hr
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hmap : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (s : E →ₐ[F] Fv F v),
      (u * (mat h)ᵀ).map (piW s) = u.map (piW s) * ((mat h).map (piW s))ᵀ := by
    intro u s; rw [Matrix.map_mul, Matrix.transpose_map]
  have hbr := fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =>
    GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ
  have hsb := fun (w : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v))
    (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ
  have c1 : ∀ C, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))) φ) = fun Y => ι φ (Y + C) := by
    intro C φ hφ
    funext Y
    rw [htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]
  have c2 : ∀ l, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)) φ) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι φ Y := by
    intro l φ hφ
    funext Y
    have hm := hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ)
      (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, sumLinForm l Y]
    congr 2
    simp [Lm, Finset.sum_neg_distrib]
  have c3 : ∀ C, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))) φ)) =
        fun Y => ι (S φ) (Y + C * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) := by
    intro C φ hφ
    funext Y
    rw [hcov _ (hUat 0 (Pm C)) φ hφ, hact]
    have hat' := hat _ (hUat 0 (Pm C))
    rw [htr _ hat' (by rw [hmap, hU0, Matrix.zero_mul]) _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) Y]
    refine congrArg (fun Z => ι (S φ) (Y + Z)) ?_
    rw [hmap, hts, hU1]
    show -(A * (-(A⁻¹ * C * (Bmᵀ)⁻¹) * (Bm⁻¹ * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)ᵀ * Bm)ᵀ) * Bmᵀ) = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hB,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have c4 : ∀ l, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l (Y * g.val)) * ι (S φ) Y := by
    intro l φ hφ
    funext Y
    rw [hcov _ (hUat (-Lm l) 0) φ hφ, hact]
    have hat' := hat _ (hUat (-Lm l) 0)
    have h1 : (U (-Lm l) 0 * (mat h)ᵀ).map (piW (t.comp σ)) = 0 := by rw [hmap, hU1, Matrix.zero_mul]
    have hm := hmu _ hat' h1 _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hmap, ht, hU0, sumLinForm l]
    congr 2
    rw [show (∑ k, ∑ j, (Y * g.val) k j * l (Matrix.single k j 1)) =
      ∑ k, ∑ j, (Y * g.val) k j * Lm l k j from rfl, sumMulRight]
    simp [Matrix.neg_mul, Finset.sum_neg_distrib]
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v)
    (GlobalTheory.SchrSB.continuous_psiAt B.ψ hstd.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v) ι
    (fun φ Y => ι (S φ) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))) hι.bij
    (fun x hx y hy c => by
      funext Y
      simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply])
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))))
    (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)))
    (fun C x hx => ⟨hsb _ x hx, c1 C x hx, by
      funext Y
      show ι (S _) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) = ι (S x) ((Y + C) * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))
      rw [c3 C x hx, Matrix.add_mul]⟩)
    (fun l x hx => ⟨hsb _ x hx, c2 l x hx, by
      funext Y
      show ι (S _) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) =
        GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (S x) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))
      rw [c4 l x hx]
      beta_reduce
      rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]⟩)
  refine ⟨c, fun φ hφ => funext fun Y => ?_⟩
  have e := congrFun (hc φ hφ) (Y * g.val)
  simp only [Pi.smul_apply] at e
  rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at e
  rw [Pi.smul_apply]
  exact e

theorem unitaryW_acts_right : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)), G.M'.IsLinBar B.ψ t 1 1 ι → ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι h₀
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have skew : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j := fun i j => by
    rw [map_neg, map_one, neg_one_mul]; exact hT.geo.hW.skew i j
  have hdetW : IsUnit (G.W.J.map t).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w) (hT.geo.hW.cartan w)
  set h := GlobalTheory.SplitUnitLift.liftU hcm t G.W.J (-1) skew hdetW h₀ with hhdef
  have hmem : h ∈ UAt σ G.W (evFin F v) := GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.W (-1) skew hdetW h₀
  obtain ⟨S, hS, hlin, hcov, hinj⟩ := local_weil_operator_second_space hP F E σ B a a' G X om om' hT v h hmem
  obtain ⟨c, hc⟩ := linBar_right_mul F E σ B a a' G X om om' hT v t h h₀ hmem
    (GlobalTheory.SplitUnitLift.liftU_piW hcm t G.W.J (-1) skew hdetW h₀)
    (GlobalTheory.SplitUnitLift.liftU_piW_comp hcm t G.W.J (-1) skew hdetW h₀) S (fun φ hφ => (hS φ hφ).1) hlin hcov ι hι
  refine ⟨h, hmem, c, ?_, fun φ hφ => ⟨S φ, (hS φ hφ).1, (hS φ hφ).2, hc φ hφ⟩⟩
  intro hc0
  have hvac := hT.geo.hM'.vac v
  have h0 : ι (S (G.M'.vac v)) = 0 := by rw [hc _ hvac.1, hc0, zero_smul]
  have hS0 : S (G.M'.vac v) = 0 :=
    hι.bij.injOn (hS _ hvac.1).1 (Submodule.zero_mem _) (by rw [h0, map_zero])
  exact hvac.2.1 (hinj _ hvac.1 hS0)

end GlobalTheory.WeilTransferW
end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_functional_good_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)), G.M'.IsLinBar B.ψ t 1 1 ι → ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  first | exact @GlobalTheory.WeilTransferW.unitaryW_acts_right | exact GlobalTheory.WeilTransferW.unitaryW_acts_right | (intros; apply GlobalTheory.WeilTransferW.unitaryW_acts_right <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeilTransfer

theorem transfer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∃ t : E →ₐ[F] Fv F v, ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (ν₀ : (Fv F v)ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
      Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
        ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0) ∧
      (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
      ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨t⟩ : Nonempty (E →ₐ[F] Fv F v) := GlobalTheory.T.split_place_embedding_exists F E σ hcm v hv.2
  let B' : Base F E := { B with v₁ := v, τ₁ := t }
  have hT' : IsTriple B' G X om om' :=
    { base := { hT.base with }
      geo := { hT.geo with hV := { hT.geo.hV with }, hV' := { hT.geo.hV' with }, hW := { hT.geo.hW with } }
      chars := { hT.chars with good := hv }
      weil := hT.weil
      weil' := hT.weil' }
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_bar_good_place hP F E σ B a a' G X om om' hT v hv t
  have hι' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι := hι

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit (G.V'.J.map t).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w)
      (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have herm : ∀ i j, σ (G.V'.J j i) = algebraMap F E 1 * G.V'.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV'.herm i j
  let K := GlobalTheory.SplitUnitLift.liftU hcm t G.V'.J 1 herm hdet
  have hK : ∀ g, K g ∈ UAt σ G.V' (evFin F B'.v₁) ∧ (mat (K g)).map (piW B'.τ₁) = g.val ∧
      (mat (K g)).map (piW (B'.τ₁.comp σ)) = (G.V'.J.map B'.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map B'.τ₁ :=
    fun g => ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V' 1 herm hdet g, GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V'.J 1 herm hdet g,
      GlobalTheory.SplitUnitLift.liftU_piW_comp hcm t G.V'.J 1 herm hdet g⟩

  choose S hS using fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v (K g) (hK g).1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  have eqR : ∀ φ₁ φ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R → φ₁ = φ₂ := by
    intro φ₁ φ₂ h
    have hRc := (hR 0 (Submodule.zero_mem _)).1
    funext y
    have hp : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (y i))
    have e2 : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hRc 0 _ hp
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, e2] at e
    exact mul_right_cancel₀ hR0 e
  have hSR : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), om' (K g, 1) (tens (evFin F v) φ R) = tens (evFin F v) (S g φ) R :=
    fun g φ hφ => (hS g φ hφ).2 R (hR φ hφ)
  have h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ := fun g φ hφ => (hS g φ hφ).1
  have tensLin : ∀ (c : ℂ) (φ φ' : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • φ + φ') R = c • tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro c φ φ'; funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hlin : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro g φ hφ φ' hφ' c
    have hm : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    apply eqR
    rw [← hSR g _ hm, tensLin, map_add, map_smul, hSR g φ hφ, hSR g φ' hφ', tensLin]
  have h2 : ∀ g g', ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    apply eqR
    have e1 : ((K (g * g'), (1 : UA σ G.W.J))) = (K g, 1) * (K g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← hSR _ φ hφ, e1, map_mul, Module.End.mul_apply, hSR g' φ hφ, hSR g _ (h1 g' φ hφ)]
  have h3 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ hφ
    apply eqR
    have e1 : ((K 1, (1 : UA σ G.W.J))) = 1 := by rw [map_one]; rfl
    rw [← hSR _ φ hφ, e1, map_one, Module.End.one_apply]
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have restS : ∀ g φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r :=
    fun g φ r hφ hr => ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v)
            (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hT v (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  obtain ⟨ν, α, hν, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator B' G X om om' hT' K hK S h1 hlin h2 h3 h4 h5
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char B' G X om om' hT' K hK S h1 h4
  obtain ⟨hTι, hMι, -, -⟩ := hA ι hι'

  have hvac := hT.geo.hM'.vac v
  have hιv : ι (G.M'.vac v) ≠ 0 := fun h0 =>
    hvac.2.1 (hι.bij.injOn hvac.1 (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  set φ₀ := GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT Y₀) (G.M'.vac v) with hφ₀def
  have hφ₀ : φ₀ ∈ SB (Fin a' × Fin (a + a') → Fv F v) := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ _ hvac.1
  have hφ₀0 : ι φ₀ 0 ≠ 0 := by
    have e := congrFun (hTι Y₀ _ hvac.1) 0
    simp only [zero_add] at e
    rw [e]; exact hY₀

  obtain ⟨-, -, hcont⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v
  obtain ⟨U, hU, hUact⟩ := hcont φ₀ hφ₀
  have hKt : Tendsto K (𝓝 1) (𝓝 1) := GlobalTheory.T.split_unitary_lift_tendsto_one hcm t G.V'.J 1 herm hdet
  have hP1 : {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U} ∈ 𝓝 1 :=
    (hKt.prodMk_nhds tendsto_const_nhds) hU
  have hone : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := fun u _ => by simp [mat]
  have hsm : ∀ g ∈ {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U},
      (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) = 1 := by
    intro g hg
    have hact := hUact (K g, 1) hg (hK g).1 hone
    have hfix : S g φ₀ = φ₀ := eqR _ _ (by rw [← hSR g φ₀ hφ₀]; exact hact R (hR φ₀ hφ₀))
    have e := congrFun (hC ι hι' g φ₀ hφ₀) 0
    rw [hfix] at e
    simp only [GlobalTheory.SplitFlip.omB, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_zero,
      Matrix.zero_mul] at e
    have e2 : ι φ₀ 0 * 1 = ι φ₀ 0 * ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2)) := by
      rw [mul_one]; nth_rw 1 [e]; ring
    exact (mul_left_cancel₀ hφ₀0 e2).symm
  have hsmooth : GlobalTheory.SmGL.IsSmoothChar ν := GlobalTheory.T.smooth_character_of_trivial_near_one (by have := (GlobalTheory.ThK.Inhab.two_le_rank hT).1; omega) ν _ _ hP1 hsm

  have hSo : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
      ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0 := by
    intro φ hφ
    constructor
    · rintro ⟨-, ι₂, hι₂, hvan⟩ Y hY
      have hι₂' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι₂ := hι₂
      obtain ⟨hT₂, hM₂, -, -⟩ := hA ι₂ hι₂'
      obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) hψc hψ1 ι₂ ι
        hι₂.bij (fun x _ y _ c => by rw [map_add, map_smul])
        (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT C))
        (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wM l))
        (fun C x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hT₂ C x hx, hTι C x hx⟩)
        (fun l x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hM₂ l x hx, hMι l x hx⟩)
      rw [hc φ hφ, Pi.smul_apply, hvan Y hY, smul_zero]
    · intro h
      exact ⟨hφ, ι, hι, h⟩
  refine ⟨t, ι, ν, hsmooth, hν, hι.bij, hSo, fun g₀ => ⟨K g₀, (hK g₀).1, fun φ hφ =>
    ⟨S g₀ φ, h1 g₀ φ hφ, (hS g₀ φ hφ).2, ?_⟩⟩, GlobalTheory.T.linear_bar_functional_good_place hP F E σ B a a' G X om om' hT v hv t ι hι⟩
  rw [hC ι hι' g₀ φ hφ]
  funext Y
  simp only [GlobalTheory.SplitFlip.omB, GlobalTheory.FullRankCoinv.lact, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one,
    Matrix.mul_one, Fintype.card_fin]

end GlobalTheory.WeilTransfer
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_linear_bar_dual : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∃ t : E →ₐ[F] Fv F v, ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (ν₀ : (Fv F v)ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
      Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
        ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0) ∧
      (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
      ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  atlas_forward_decl GlobalTheory.WeilTransfer.transfer
end
