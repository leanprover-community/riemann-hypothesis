import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarisableOfCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton

section
noncomputable section

namespace GlobalTheory.HCFinU

open NumberField Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def starOf (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) : StarRing E where
  star := σ
  star_involutive := hσ
  star_mul x y := by simp only [map_mul, mul_comm]
  star_add := map_add σ

def mkI (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (cm : @Formalism.BasicNotions.CMData F E _ _ _ _ (starOf σ hσ) _) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hdual : ∀ x : Fin n → E, x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)
    (ε : InfinitePlace F → Fin n → Bool) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ)
    (hPu : ∀ v, IsUnit (P v)) (hP : ∀ v, (P v)ᴴ * J.map (φ v) * P v = Formalism.REAL.Jm (ε v)) :
    Formalism.MainNotions.S.AutInst :=
  letI := starOf σ hσ
  { F := F, E := E, cm := cm, n := n, J := J
    J_herm := Matrix.ext fun i j => hJ i j
    J_det := hdet
    L := L
    L_span := hspan
    L_fg := hfg
    L_dual := hdual
    ε := ε
    φ := φ
    φ_over := hφ
    P := P
    P_unit := hPu
    P_spec := hP
    topf := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose
    topf_group := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose_spec.1
    topf_open := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose_spec.2.1
    topf_basis := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose_spec.2.2 }

theorem mkI_sig (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (cm : @Formalism.BasicNotions.CMData F E _ _ _ _ (starOf σ hσ) _) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hdual : ∀ x : Fin n → E, x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)
    (ε : InfinitePlace F → Fin n → Bool) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ)
    (hPu : ∀ v, IsUnit (P v)) (hP : ∀ v, (P v)ᴴ * J.map (φ v) * P v = Formalism.REAL.Jm (ε v)) :
    σ = (mkI σ hσ cm J hJ hdet L hfg hspan hdual ε φ hφ P hPu hP).cm.sig :=
  AlgHom.ext fun _ => rfl

def bridgeS (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) :
    I.GA ≃ₜ* GlobalTheory.AdelicU.GAd s I.J := by
  subst hs
  exact Formalism.L2.SG.AdBridge.toHA I (Formalism.L2.SG.Closed.AdBridgeIso_holds I)

theorem bridgeS_isBridge (I : Formalism.MainNotions.S.AutInst) :
    Formalism.L2.SG.AdBridge.IsBridge I (bridgeS I I.cm.sig rfl) :=
  Formalism.L2.SG.AdBridge.toHA_isBridge I _

theorem bridgeS_rat (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) :
    ∀ γ ∈ I.GFset, bridgeS I s hs γ ∈ GlobalTheory.AdelicU.ratPts s I.J := by
  subst hs
  intro γ hγ
  have h := Formalism.L2.SG.Closed.AdBridgeGF_holds I (bridgeS I _ rfl) (bridgeS_isBridge I)
  have h2 : bridgeS I _ rfl γ ∈ Formalism.L2.SG.AdBridge.ratHA I := h ▸ Set.mem_image_of_mem _ hγ
  exact Subgroup.mem_subgroupOf.2 h2

end GlobalTheory.HCFinU

end
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaCplV.UnitaryTrick

theorem exists_isURep_of_core {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ K V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun k => φ (ρ k v))
    (c : InnerProductSpace.Core ℂ V) (hc : ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v) :
    ∃ (d : ℕ) (τ : K → (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)))
      (e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d)), GlobalTheory.Dec.IsURep τ ∧ ∀ k v, e (ρ k v) = τ k (e v) := by
  letI cd : InnerProductSpace.Core ℂ V := c
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ cd
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  let b := stdOrthonormalBasis ℂ V
  let e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) := b.repr.toLinearEquiv
  let τ : K → (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :=
    fun g => LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap)
  have hτ : ∀ g x, τ g x = e (ρ g (e.symm x)) := fun _ _ => rfl
  have hn : ∀ g (y : V), ‖ρ g y‖ = ‖y‖ := by
    intro g y
    have h1 : inner ℂ (ρ g y) (ρ g y) = inner ℂ y y := hc g y y
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, h1]
  refine ⟨_, τ, e, ⟨?_, fun a c => ?_, fun g x => ?_, fun x => ?_⟩, fun g v => ?_⟩
  · ext1 x; simp [hτ]
  · ext1 x; simp [hτ, map_mul]
  · rw [hτ]
    change ‖b.repr (ρ g (b.repr.symm x))‖ = ‖x‖
    rw [LinearIsometryEquiv.norm_map, hn, ← LinearIsometryEquiv.norm_map b.repr,
      LinearIsometryEquiv.apply_symm_apply]
  · simp only [hτ]
    exact GlobalTheory.UniTrick.continuous_lin ρ hρ e.toLinearMap _
  · rw [hτ, LinearEquiv.symm_apply_apply]

end GlobalTheory.ThetaCplV.UnitaryTrick

namespace GlobalTheory.ThetaCplV

open UnitaryTrick in

theorem exists_isURep_of_stable : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (j : K →* G), Continuous j → ∀ H : Subgroup G, (∀ k, j k ∈ H) → ∀ T : Submodule ℂ (G → ℂ), FiniteDimensional ℂ T → (∀ t ∈ T, Continuous t) → (∀ h, ∀ t ∈ T, GlobalTheory.ThetaCplV.rt H h t ∈ T) → ∃ (m : ℕ) (τ : K → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))), GlobalTheory.Dec.IsURep τ ∧ ∀ f ∈ GlobalTheory.ThetaCplV.typeSet (GlobalTheory.ThetaCplV.rt H) ⊤ T, ∃ L : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (G → ℂ), (∀ k w x, L (τ k w) x = L w (x * j k)) ∧ f ∈ LinearMap.range L := by
  intro G _ _ _ K _ _ _ _ j hj H hjH T hT hcont hst
  let ρ : Representation ℂ K T :=
    { toFun := fun k => (rt H ⟨j k, hjH k⟩).restrict (fun t ht => hst _ t ht)
      map_one' := by ext t x; simp
      map_mul' := fun a b => by ext t x; simp [mul_assoc] }
  have hρv : ∀ k (v : T), ((ρ k v : T) : G → ℂ) = fun x => (v : G → ℂ) (x * j k) := fun _ _ => rfl
  have hρc : ∀ v : T, Continuous fun k => ρ k v := by
    intro v
    refine Continuous.subtype_mk ?_ _
    change Continuous fun k => fun x => (v : G → ℂ) (x * j k)
    exact continuous_pi fun x => (hcont v v.2).comp (continuous_const.mul hj)
  have hρφ : ∀ (φ : T →ₗ[ℂ] ℂ) (v : T), Continuous fun k => φ (ρ k v) := fun φ v =>
    (LinearMap.continuous_of_finiteDimensional φ).comp (hρc v)
  obtain ⟨c, hc⟩ := GlobalTheory.exists_invariant_core ρ hρc
  obtain ⟨d, τ, e, hτ, he⟩ := exists_isURep_of_core ρ hρφ c hc
  refine ⟨d, τ, hτ, fun f hf => ?_⟩
  obtain ⟨L₀, -, heq, t, rfl⟩ := hf
  refine ⟨L₀ ∘ₗ e.symm.toLinearMap, fun k w x => ?_, ⟨e t, by simp⟩⟩
  have h1 : e.symm (τ k w) = ρ k (e.symm w) := by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1]
  rw [heq ⟨j k, hjH k⟩ (e.symm w) (ρ k (e.symm w)) rfl, rt_apply]

end GlobalTheory.ThetaCplV
end
end
