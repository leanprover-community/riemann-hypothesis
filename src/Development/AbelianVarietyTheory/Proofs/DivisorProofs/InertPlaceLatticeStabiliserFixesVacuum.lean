import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserGeneratedDiagAntidiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSphericalStabilizerPreservesLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (1, k)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.VacTransport.transport | exact GlobalTheory.VacTransport.transport | (intros; apply GlobalTheory.VacTransport.transport <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLattice_inertPlace_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    (∀ z : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latAtV G.V G.W v ↔ ∀ γ ∈ latAtV G.V G.W v,
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z γ) = 1)) := by
  first | exact @GlobalTheory.InertSelfDual.latAtV_selfDual | exact GlobalTheory.InertSelfDual.latAtV_selfDual | (intros; apply GlobalTheory.InertSelfDual.latAtV_selfDual <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LatVacLine

theorem vacuum_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), PsiUnr B.ψ v → (∀ z : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latAtV G.V G.W v ↔ ∀ γ ∈ latAtV G.V G.W v,
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z γ) = 1)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), φ₀ ≠ 0 → (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₀
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₀)) →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • φ₀ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hψ hsd θ hθ φ₀ hφSB hφ0 hφ φ hψSB hψ'
  set Λ := latAtV G.V G.W v with hΛ
  set co := G.M.co with hco
  have hAt : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  classical
  let χ : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E))
        (incM F G.V.J) (incM F G.W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin a × Fin (a + a') → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ Λ, Acts (evFin F v) (co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E))
          (incM F G.V.J) (incM F G.W.J) γ γ) • f)) →
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l := AddSubgroup.mem_map.mp hl
    obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.T.exists_nonzero_complementary_adelicSchwartz_function v f hf
    have key := GlobalTheory.T.heisenbergEigen_latticePointAtPlace_localIdentity v co B.ψ h.choose f _ (hAt _ h.choose_spec.1) (hA _ h.choose_spec.1) r hr x₀ hx₀ ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.T.tensorLattice_localDarbouxCoords_bounded G.V G.W v co hT.geo.hV.lat hT.geo.hW.lat
  have hsd' := GlobalTheory.T.selfDual_localImage_latticeSupportedAtPlace v co B.ψ Λ hAt hsd
  have hfill := GlobalTheory.T.selfDualLocalSubgroup_firstProj_eq_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v) (Λ.map (GlobalTheory.LatVac.locCo co v)) c hc0 (fun x => hψ x) hsd'
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  exact GlobalTheory.T.heisenbergEigen_proportional_localField (GlobalTheory.LatVac.psiAt B.ψ v) (Λ.map (GlobalTheory.LatVac.locCo co v)) χ φ₀ φ (loc φ₀ hφSB hφ) (loc φ hψSB hψ')
    hφ0 hfill

end GlobalTheory.LatVacLine
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), PsiUnr B.ψ v → (∀ z : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latAtV G.V G.W v ↔ ∀ γ ∈ latAtV G.V G.W v,
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z γ) = 1)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), φ₀ ≠ 0 → (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₀
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₀)) →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • φ₀ := by
  atlas_forward_decl GlobalTheory.LatVacLine.vacuum_line
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacEigen

theorem local_identity_of_tens_eigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  intro F _ _ v W _ _ B κ _ co ψ γ f R c hγ hR x₀ hx₀ hA ξ
  have hx1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z :=
    GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : R x = R x₀ := hR x₀ z hzat
  have hrx1 : R (x + (co.e γ).1) = R x := hR x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun hA x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul] at key
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v)
      (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b
    simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add, map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : R x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  have := key
  apply mul_right_cancel₀ hr0
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this ⊢
  linear_combination this

end GlobalTheory.DblVacEigen
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIdentity_of_tensorHeisenbergEigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  atlas_forward_decl GlobalTheory.DblVacEigen.local_identity_of_tens_eigen
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceSymplecticForm_unitaryGroupAction_invariant : ∀ {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB)
    (x y : Matrix α β E), symp c ξ JA JB (actB c g x) (actB c g y) = symp c ξ JA JB x y := by
  first | exact @GlobalTheory.DblVacEigen.SympAct.symp_actB | exact GlobalTheory.DblVacEigen.SympAct.symp_actB | (intros; apply GlobalTheory.DblVacEigen.SympAct.symp_actB <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergEigen_doubledCoords_productFunction : ∀ {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ ξ' : E) (JA : Matrix α α E) (JB : Matrix β β E)
    {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)),
    IsDblCoord c ξ JA JB d dd → ∀ ψ : AddChar R ℂ, (∀ t, ‖ψ t‖ = 1) → ∀ (Λ : Set (Matrix α β E)) (f : (κ → R) → ℂ),
    (∀ w ∈ Λ, d.rho ψ w f = ψ (⅟(2 : R) * symp c ξ' JA JB w w) • f) →
    ∀ z : Matrix α (β ⊕ β) E, z.toCols₁ ∈ Λ → z.toCols₂ ∈ Λ →
      dd.rho ψ z (boxFun f (fun x => star (f x))) = ψ (⅟(2 : R) * symp c ξ' JA (dbl JB) z z) • boxFun f (fun x => star (f x)) := by
  first | exact @GlobalTheory.DblBoxRho.boxrho | exact GlobalTheory.DblBoxRho.boxrho | (intros; apply GlobalTheory.DblBoxRho.boxrho <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma vecMulVec_mul_transpose' {m k : Type} [Fintype k] {R : Type} [CommRing R] (p : m → R) (q : k → R)
    (M : Matrix k k R) : Matrix.vecMulVec p q * Mᵀ = Matrix.vecMulVec p (M *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma vecMulVec_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {x : Fin n → E} (hx : x ∈ X.L)
    {q : Fin d ⊕ Fin d → AE F E} (hq : q ∈ GlobalTheory.DblVac.latD W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latDbl X W v := by
  refine ⟨?_, ?_⟩
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₁ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inl) := by
      ext i j; simp [Matrix.toCols₁, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.1
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₂ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inr) := by
      ext i j; simp [Matrix.toCols₂, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.2

theorem mul_transpose_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F)
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (hM : ∀ q ∈ GlobalTheory.DblVac.latD W v, M *ᵥ q ∈ GlobalTheory.DblVac.latD W v) :
    ∀ γ ∈ latDbl X W v, γ * Mᵀ ∈ latDbl X W v := by

  let φ₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols γ 0 : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  let φ₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols 0 γ : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  have key : ∀ (φ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)),
      (∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ x ∈ X.L, ∀ y ∈ W.L,
        ∃ q ∈ GlobalTheory.DblVac.latD W v,
          φ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) →
      latAtV X W v ≤ (latDbl X W v).comap φ := by
    intro φ hφ
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    obtain ⟨q, hq, he⟩ := hφ a ha hai x hx y hy
    show φ _ ∈ latDbl X W v
    rw [he]; exact vecMulVec_mem_latDbl X W v hx hq
  have gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ W.L,
      (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v := fun a ha hai y hy =>
    AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, rfl⟩
  have h₁ : latAtV X W v ≤ (latDbl X W v).comap φ₁ := by
    refine key φ₁ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim (a • fun i => inclR (F := F) (AF F) (y i)) 0, hM _ ?_, ?_⟩
    · exact ⟨by simpa using gen a ha hai y hy, by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₁, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  have h₂ : latAtV X W v ≤ (latDbl X W v).comap φ₂ := by
    refine key φ₂ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (y i)), hM _ ?_, ?_⟩
    · exact ⟨by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem, by simpa using gen a ha hai y hy⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₂, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  intro γ hγ
  have hsplit : γ * Mᵀ = φ₁ γ.toCols₁ + φ₂ γ.toCols₂ := by
    simp only [φ₁, φ₂, AddMonoidHom.mk'_apply]
    rw [← Matrix.add_mul]
    congr 1
    ext i (j | j) <;> simp [Matrix.toCols₁, Matrix.toCols₂]
  rw [hsplit]
  exact (latDbl X W v).add_mem (h₁ hγ.1) (h₂ hγ.2)

end GlobalTheory.DblVacStab

theorem GlobalTheory.DblVac.kD_stab_latDbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl F), ∀ g ∈ GlobalTheory.DblVac.KD σ W v, ∀ γ ∈ latDbl X W v,
      γ * (GlobalTheory.DblVac.matD g)ᵀ ∈ latDbl X W v ∧ γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ latDbl X W v := by
  intro F E _ _ _ _ _ σ n d X W v g hg γ hγ
  exact ⟨GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).1) γ hγ,
    GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).2) γ hγ⟩
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_preserves_doubledSpaceLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl F), ∀ g ∈ GlobalTheory.DblVac.KD σ W v, ∀ γ ∈ latDbl X W v,
      γ * (GlobalTheory.DblVac.matD g)ᵀ ∈ latDbl X W v ∧ γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ latDbl X W v := by
  atlas_forward_decl GlobalTheory.DblVac.kD_stab_latDbl
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblFill

theorem symp_dbl {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (x y : Matrix α (β ⊕ β) E) :
    symp c ξ JA (dbl JB) x y = symp c ξ JA JB x.toCols₁ y.toCols₁ - symp c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold symp hTens
  rw [← map_sub, ← mul_sub]
  congr 2
  simp only [Fintype.sum_sum_type, dbl, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.toCols₁_apply, Matrix.toCols₂_apply, Matrix.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem symp_zero_right {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x : Matrix α β E) :
    symp c ξ JA JB x 0 = 0 := by
  simp [symp, hTens]

end GlobalTheory.DblFill

namespace GlobalTheory.DblFill

theorem at_toCols₁ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : Pl F} {z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)} (hz : At (evFin F v) z) : At (evFin F v) z.toCols₁ := by
  intro u hu
  have := hz u hu
  ext i j
  simpa using congrFun (congrFun this i) (Sum.inl j)

theorem at_toCols₂ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : Pl F} {z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)} (hz : At (evFin F v) z) : At (evFin F v) z.toCols₂ := by
  intro u hu
  have := hz u hu
  ext i j
  simpa using congrFun (congrFun this i) (Sum.inr j)

theorem latDbl_fill : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    ∀ η : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v,
      (∀ b, ((0 : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), b) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) →
        GlobalTheory.LatVac.psiAt B.ψ v (η ⬝ᵥ b) = 1) →
      ∃ y, (η, y) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw dd hdd η hη
  have hunr : PsiUnr B.ψ v := (hT.base.inert v w hvw).2.2
  have hsd := GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hvw

  have hglob : ∀ z : Matrix (Fin a) (Fin (a + a') ⊕ Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latDbl G.V G.W v ↔ ∀ γ ∈ latDbl G.V G.W v,
        B.ψ (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) z γ) = 1) := by
    intro z hz
    have h1 := hsd _ (at_toCols₁ hz)
    have h2 := hsd _ (at_toCols₂ hz)
    constructor
    · intro hzm γ hγ
      rw [symp_dbl, AddChar.map_sub_eq_div, (h1.1 hzm.1) _ hγ.1, (h2.1 hzm.2) _ hγ.2, div_one]
    · intro hψ
      refine ⟨h1.2 fun γ₁ hγ₁ => ?_, h2.2 fun γ₂ hγ₂ => ?_⟩
      · have := hψ (Matrix.fromCols γ₁ 0) (fromCols_mem_latDbl _ _ _ hγ₁ (zero_mem _))
        rwa [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, sub_zero] at this
      · have := hψ (Matrix.fromCols 0 γ₂) (fromCols_mem_latDbl _ _ _ (zero_mem _) hγ₂)
        rw [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, zero_sub,
          AddChar.map_neg_eq_inv] at this
        exact inv_eq_one.1 this
  have hloc := GlobalTheory.LatVac.DualLoc.map_selfDual v dd B.ψ (latDbl G.V G.W v)
    (fun γ hγ => at_of_mem_latDbl _ _ _ hγ) hglob
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v G.M.co hT.geo.hV.lat hT.geo.hW.lat
  have hbd : ∀ l ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F := by
    rintro l ⟨z, hz, rfl⟩ i
    have hzc : z = Matrix.fromCols z.toCols₁ z.toCols₂ := (Matrix.fromCols_toCols z).symm
    have he := hdd z.toCols₁ z.toCols₂
    rw [← hzc] at he
    have k1 := hc _ hz.1
    have k2 := hc _ hz.2
    rcases i with k | k
    · simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, he, Sum.elim_inl]
      exact k1 k
    · simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, he, Sum.elim_inr, Pi.neg_apply, map_neg,
        mul_neg]
      exact ⟨(k2 k).1, neg_mem (k2 k).2⟩
  exact GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v) _ c hc0 hunr hloc hbd η hη

end GlobalTheory.DblFill
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_lattice_local_image_full_at_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    ∀ η : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v,
      (∀ b, ((0 : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), b) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) →
        GlobalTheory.LatVac.psiAt B.ψ v (η ⬝ᵥ b) = 1) →
      ∃ y, (η, y) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) := by
  atlas_forward_decl GlobalTheory.DblFill.latDbl_fill
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacEigen

open MeasureTheory

theorem sb_boxFun {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem sb_star {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) : (fun x => star (φ x)) ∈ SB X :=
  ⟨h.1.comp (fun z : ℂ => star z), h.2.comp_left (g := fun z : ℂ => star z) (star_zero _)⟩

theorem locality_op {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F) (ψ : AddChar (AF F) ℂ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (hψ : IsStd ψ) (hkeep : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ)
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) :
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ, ∀ φ ∈ SB (κ → Fv F v), S φ ∈ SB _ ∧ Acts (evFin F v) T φ (S φ) := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    have e1 : ∀ Ψ : (κ → AF F) → ℂ, schr ψ (u • p, u • (0 : κ → AF F)) Ψ = fun y => Ψ (y + u • p) := fun Ψ => by
      funext y; simp [schr]
    rw [e1, e1] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨fun φ t => (R 0)⁻¹ * T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)),
    fun φ hφ => ⟨?_, ?_⟩⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.WeilLocality.liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef]
    field_simp
    ring

end GlobalTheory.DblVacEigen

noncomputable section
namespace GlobalTheory.DblVacEigen

theorem eigen_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv dd omd hdc hsp r hr g hg
  classical
  by_cases hr0 : ∀ x, r x = 0
  · refine ⟨0, ?_⟩
    have h0 : boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) = 0 := by
      funext x; simp [boxFun, tens, hr0]
    rw [h0, map_zero, smul_zero]
  push_neg at hr0
  obtain ⟨x₀, hx₀⟩ := hr0
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hT.geo.hM.vac v
  have hψ1 : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hT.base.std
  set vac := G.M.vac v with hvacdef
  set V₀ := tens (evFin F v) vac r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  set vd : ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v) → ℂ := boxFun vac (fun x => star (vac x)) with hvd
  set R : ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ := boxFun r (fun x => star (r x)) with hR
  have hSt : S = tens (evFin F v) vd R := by
    funext x
    simp only [hS, hvd, hR, hV₀, boxFun, tens, star_mul', Function.comp_def]
    ring
  have hSA : S ∈ schA F _ := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ V₀ hr.2 _ (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hRinv : ∀ x z, At (evFin F v) z → R (x + z) = R x := by
    intro x z hz
    have hl : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hr' : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by funext i; exact congrFun (hz u hu) (Sum.inr i)
    simp only [hR, boxFun]
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hl, hr.1 _ _ hr']
  have hRest : Rest (evFin F v) vd R := ⟨hRinv, hSt ▸ hSA⟩
  have hvdSB : vd ∈ SB _ := sb_boxFun hvSB (sb_star hvSB)
  have hvd0 : vd ≠ 0 := by
    obtain ⟨y, hy⟩ := Function.ne_iff.mp hv0
    intro h
    have h1 := congrFun h (Sum.elim y y)
    simp only [hvd, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at h1 hy
    exact mul_ne_zero hy (star_ne_zero.mpr hy) h1
  have hRx : R (Sum.elim x₀ x₀) ≠ 0 := by
    simp only [hR, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]
    exact mul_ne_zero hx₀ (star_ne_zero.mpr hx₀)

  have hspl := hsp.2.1
  have hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F,
      ∀ Φ ∈ schA F _, omd g (schr B.ψ (u • p, u • q) Φ) = schr B.ψ (u • p, u • q) (omd g Φ) := by
    intro u hu p q Φ hΦ
    set w' := dd.e.symm (p, q) with hw'
    have he : dd.e (u • w') = (u • p, u • q) := by
      rw [LinearEquiv.map_smul, hw', LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h0 : u • (GlobalTheory.DblVac.matD g - 1) = 0 := hg.1 u hu
    have hact : actB (cA σ) g (u • w') = u • w' := by
      have h1 : (u • w') * (GlobalTheory.DblVac.matD g)ᵀ - u • w' = w' * (u • (GlobalTheory.DblVac.matD g - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
      exact h1
    have h2 := hspl.impl g (u • w') Φ hΦ
    simp only [Darboux.rho, he, hact] at h2
    exact h2
  obtain ⟨Tl, hTl⟩ := locality_op v B.ψ (omd g) hT.base.std (fun Φ hΦ => hspl.pres g Φ hΦ)
    (fun μ hμ Φ hΦ => hspl.unit μ hμ g Φ hΦ) hcomm
  have hgS : omd g S = tens (evFin F v) (Tl vd) R := by rw [hSt]; exact (hTl vd hvdSB).2 R hRest

  have hV₀eig : ∀ γ ∈ (latAtV G.V G.W v : Set _), G.M.co.rho B.ψ γ V₀ =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • V₀ := by
    intro γ hγ
    rw [hV₀, hvac γ hγ r hr]
    funext x
    simp [tens, mul_assoc]
  have hSeig : ∀ γ ∈ latDbl G.V G.W v, dd.rho B.ψ γ S =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (dbl (incM F G.W.J)) γ γ) • S :=
    fun γ hγ => GlobalTheory.T.heisenbergEigen_doubledCoords_productFunction (cA σ) (-1) (inclR (F := F) (AF F) (θ : E)) _ _ G.M.co dd hdc B.ψ hψ1 _ V₀ hV₀eig γ hγ.1 hγ.2

  have hgSeig : ∀ γ ∈ latDbl G.V G.W v, dd.rho B.ψ γ (omd g S) =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (dbl (incM F G.W.J)) γ γ) • omd g S := by
    intro γ hγ
    have hK := (GlobalTheory.T.doubledVacuumLatticeStabilizer_preserves_doubledSpaceLattice F E σ G.V G.W v g hg γ hγ).2
    have h1 := hspl.impl g (actB (cA σ) g⁻¹ γ) S hSA
    have h2 : actB (cA σ) g (actB (cA σ) g⁻¹ γ) = γ := by
      simp only [actB, Matrix.mul_assoc, ← Matrix.transpose_mul]
      have e : ((g : GL (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) :
            Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) *
          (((g⁻¹ : GlobalTheory.DblVac.UD σ G.W) : GL (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) :
            Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      rw [e, Matrix.transpose_one, Matrix.mul_one]
    rw [h2] at h1
    rw [← h1, hSeig (actB (cA σ) g⁻¹ γ) hK, map_smul, GlobalTheory.T.traceSymplecticForm_unitaryGroupAction_invariant]

  let Λd := (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v)
  let χ : (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v) × ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v)) → ℂ :=
    fun l => if h : ∃ γ ∈ latDbl G.V G.W v, GlobalTheory.LatVac.locCo dd v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (dbl (incM F G.W.J)) h.choose h.choose)
      else 0
  have loc : ∀ f : ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v) → ℂ,
      (∀ γ ∈ latDbl G.V G.W v, dd.rho B.ψ γ (tens (evFin F v) f R) =
        B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (dbl (incM F G.W.J)) γ γ) •
          tens (evFin F v) f R) →
      ∀ l ∈ Λd, ∀ ξ, GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf l hl ξ
    have h : ∃ γ ∈ latDbl G.V G.W v, GlobalTheory.LatVac.locCo dd v γ = l := AddSubgroup.mem_map.mp hl
    have key := GlobalTheory.T.localIdentity_of_tensorHeisenbergEigen v dd B.ψ h.choose f R _ (at_of_mem_latDbl _ _ _ h.choose_spec.1) hRinv
      (Sum.elim x₀ x₀) hRx (hf _ h.choose_spec.1) ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  have hloc1 := loc vd (fun γ hγ => hSt ▸ hSeig γ hγ)
  have hloc2 := loc (Tl vd) (fun γ hγ => hgS ▸ hgSeig γ hγ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.heisenbergEigen_proportional_localField (GlobalTheory.LatVac.psiAt B.ψ v) Λd χ vd (Tl vd) hloc1 hloc2 hvd0
    (GlobalTheory.T.doubled_lattice_local_image_full_at_inert_place F E σ B a a' G X om om' hT v w hw dd hdc)
  refine ⟨c, ?_⟩
  rw [hgS, hc, hSt]
  funext x
  simp [tens, mul_assoc]

end GlobalTheory.DblVacEigen
end
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeStabilizer_scales_doubledVacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  atlas_forward_decl GlobalTheory.DblVacEigen.eigen_box
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalStabilizer_doubledVacuum_eigenvalue_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegel.eigen_eq_one_of_diag | exact GlobalTheory.DblVacSiegel.eigen_eq_one_of_diag | (intros; apply GlobalTheory.DblVacSiegel.eigen_eq_one_of_diag <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVac

theorem eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om (1, k)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv k hk c hc
  obtain ⟨dd, omd, hdc, hsp, hbox⟩ := hT.weil.1.2
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.W) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.inertPlace_latticeStabilizer_scales_doubledVacuum F E σ B a a' G X om om' hT v w hw hv dd omd hdc hsp r hr p hp
    have h1 := GlobalTheory.T.diagonalStabilizer_doubledVacuum_eigenvalue_eq_one F E σ B a a' G X om om' hT v w hw hv dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.W v, q ∈ GlobalTheory.DblVac.PAnti σ G.W → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.W v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.inertPlace_latticeStabilizer_scales_doubledVacuum F E σ B a a' G X om om' hT v w hw hv dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.W v k hk
  have hfix : omd gd S = S := GlobalTheory.T.inertPlace_lattice_stabiliser_generated_diag_antidiag F E σ B a a' G X om om' hT v w hw H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inr _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inr_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)

end GlobalTheory.DblVac
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizer_vacuum_eigenvalue_eq_one_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om (1, k)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  atlas_forward_decl GlobalTheory.DblVac.eigen_eq_one
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem vac_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk
  obtain ⟨hSB, hne, θ, hθ, hfix⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hT v k hk.1 _ hSB
  have hfix₁ := GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ _ hSB φ₁ hφ₁ hfix hact
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v (hT.base.inert v w hin).2.2
    (GlobalTheory.T.tensorLattice_inertPlace_selfDual F E σ B a a' G X om om' hT v w hin) θ hθ _ hSB hne hfix φ₁ hφ₁ hfix₁
  have hc := GlobalTheory.T.latticeStabilizer_vacuum_eigenvalue_eq_one_inertPlace F E σ B a a' G X om om' hT v w hin hvT k hk c hact
  rw [hc, one_smul] at hact
  exact hact

end GlobalTheory.InertSph
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  atlas_forward_decl GlobalTheory.InertSph.vac_fixed
end
