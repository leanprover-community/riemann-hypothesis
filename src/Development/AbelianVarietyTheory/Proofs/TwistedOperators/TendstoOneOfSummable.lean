import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitarySphericalReps
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplit
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSphericalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic

section
section
open GlobalTheory.PRep

namespace GlobalTheory.SmoothRiesz

theorem surjective_of_injective {F : Type} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (T : F →ₛₗ[starRingEnd ℂ] Module.Dual ℂ F) (hT : ∀ x, T x = 0 → x = 0) : Function.Surjective T := by
  let b := Module.finBasis ℂ F
  have key : ∀ c : Fin (Module.finrank ℂ F) → ℂ,
      T (∑ i, starRingEnd ℂ (c i) • b i) = ∑ i, c i • T (b i) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, Complex.conj_conj]
  have hli : LinearIndependent ℂ fun i => T (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h := Fintype.linearIndependent_iff.1 b.linearIndependent _ (hT _ ((key c).trans hc)) i
    simpa using h
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp)
  intro l
  have hl : l ∈ Submodule.span ℂ (Set.range fun i => T (b i)) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hl
  exact ⟨_, (key c).trans hc⟩

def stabiliser {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := fun {a b} ha hb => by
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    show ρ a⁻¹ v = v
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]; simp

theorem exists_conj_smoothDual : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsAdmissible ρ → GlobalTheory.LGrp.IsUnitarisable ρ → ∃ φ : V →ₛₗ[starRingEnd ℂ] smoothPart ρ.dual, Function.Bijective φ ∧ ∀ g x, φ (ρ g x) = GlobalTheory.LGrp.smoothDual ρ g (φ x) := by
  intro G _ _ _ K hKo hKc V _ _ ρ hρ hU
  obtain ⟨B, -, hpos, hinv⟩ := hU
  have hadj : ∀ g v x, B (ρ g⁻¹ v) x = B v (ρ g x) := by
    intro g v x
    rw [← hinv g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hnd : ∀ x, B x x = 0 → x = 0 := fun x hx => by
    by_contra h
    have := hpos x h
    rw [hx] at this
    simp at this
  have hsm : ∀ x, B.flip x ∈ smoothPart ρ.dual := by
    intro x
    refine (stabiliser ρ.dual (B.flip x)).isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset ((hρ.1 x).mem_nhds (by simp)) fun g hg => ?_)
    have hg' : ρ g x = x := hg
    refine LinearMap.ext fun v => ?_
    show B (ρ g⁻¹ v) x = B v x
    rw [hadj, hg']
  refine ⟨B.flip.codRestrict _ hsm, ⟨?_, ?_⟩, fun g x => Subtype.ext (LinearMap.ext fun v => (hadj g v x).symm)⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => hnd x ?_
    exact LinearMap.congr_fun (congrArg Subtype.val hx) x
  · intro l
    let U : Subgroup G := stabiliser ρ.dual l.1 ⊓ K
    have hUo : IsOpen (U : Set G) := IsOpen.inter l.2 hKo
    have hUc : IsCompact (U : Set G) :=
      hKc.of_isClosed_subset (U.isClosed_of_isOpen hUo) fun _ h => h.2
    haveI := hρ.2 U hUo hUc
    let T : fixed ρ U →ₛₗ[starRingEnd ℂ] Module.Dual ℂ (fixed ρ U) :=
      (B.domRestrict₁₂ (fixed ρ U) (fixed ρ U)).flip
    obtain ⟨x, hx⟩ := surjective_of_injective T
      (fun x hx => Subtype.ext (hnd x (LinearMap.congr_fun hx x))) (l.1 ∘ₗ (fixed ρ U).subtype)
    refine ⟨x, Subtype.ext ?_⟩
    show B.flip x = l.1
    rw [← sub_eq_zero, ← LinearMap.ker_eq_top, eq_top_iff,
      ← (GlobalTheory.LocGL.isCompl_fixed_twKer hρ.1 hUc).sup_eq_top]
    refine sup_le (fun v hv => ?_) (Submodule.span_le.2 ?_)
    · exact sub_eq_zero.2 (LinearMap.congr_fun hx ⟨v, hv⟩)
    · rintro _ ⟨u, v, rfl⟩
      have h1 : l.1 (ρ u v) = l.1 v := by
        have := LinearMap.congr_fun (show ρ.dual (u : G)⁻¹ l.1 = l.1 from (U.inv_mem u.2).1) v
        rw [← this]
        show _ = l.1 (ρ (u : G)⁻¹⁻¹ v)
        rw [inv_inv]
      have h2 : B (ρ u v) x = B v x := by
        rw [← inv_inv (u : G), hadj, GlobalTheory.LGrp.mem_fixed.1 x.2 _ (U.inv_mem u.2)]
      simp [h1, h2]

end GlobalTheory.SmoothRiesz
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_unitary_conjugate_dual : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsAdmissible ρ → GlobalTheory.LGrp.IsUnitarisable ρ → ∃ φ : V →ₛₗ[starRingEnd ℂ] smoothPart ρ.dual, Function.Bijective φ ∧ ∀ g x, φ (ρ g x) = GlobalTheory.LGrp.smoothDual ρ g (φ x) := by
  atlas_forward_decl GlobalTheory.SmoothRiesz.exists_conj_smoothDual
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ConjRep

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}

theorem map_fixed (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (U : Subgroup G) :
    (fixed ρ U).map (e : V →ₛₗ[starRingEnd ℂ] W) = fixed ρ' U := by
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  constructor
  · rintro ⟨x, hx, hxe⟩
    have hxe' : e x = e v := hxe
    rw [← hxe', GlobalTheory.LGrp.mem_fixed]
    intro k hk
    rw [← he, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
  · intro h
    refine ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => e.injective ?_, rfl⟩
    rw [he, GlobalTheory.LGrp.mem_fixed.1 h k hk]

def comapSub (φ : V →ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, φ (ρ g x) = ρ' g (φ x)) (S : Subrepresentation ρ') :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule.comap φ
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_comap] at hv ⊢
    rw [he]
    exact S.apply_mem_toSubmodule g hv

theorem symm_equivariant (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (g : G) (y : W) :
    e.symm (ρ' g y) = ρ g (e.symm y) := by
  apply e.injective
  rw [he]
  simp

def subOrderIso (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x)) :
    Subrepresentation ρ' ≃o Subrepresentation ρ where
  toFun := comapSub (e : V →ₛₗ[starRingEnd ℂ] W) he
  invFun := comapSub (e.symm : W →ₛₗ[starRingEnd ℂ] V) (symm_equivariant e he)
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    simp [comapSub]
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    simp [comapSub]
  map_rel_iff' := by
    intro S T
    constructor
    · intro h w hw
      obtain ⟨v, rfl⟩ := e.surjective w
      exact @h v hw
    · intro h v hv
      exact @h (e v) hv

theorem isUnitarisable (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x))
    (h : GlobalTheory.LGrp.IsUnitarisable ρ) : GlobalTheory.LGrp.IsUnitarisable ρ' := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => B (e.symm y) (e.symm x)) ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro a b c; simp
  · intro a b c; simp [LinearEquiv.map_smulₛₗ]
  · intro a b c; simp
  · intro a b c; simp [LinearEquiv.map_smulₛₗ]
  · intro v w
    exact h1 _ _
  · intro v hv
    exact h2 _ (by simpa using hv)
  · intro g v w
    simp only [LinearMap.mk₂'ₛₗ_apply, symm_equivariant e he, h3]

theorem conj_transfer : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (φ : V →ₛₗ[starRingEnd ℂ] W), Function.Bijective φ → (∀ g x, φ (ρ g x) = ρ' g (φ x)) → (ρ.IsIrreducible → ρ'.IsIrreducible) ∧ (IsAdmissible ρ → IsAdmissible ρ') ∧ (GlobalTheory.LGrp.IsUnitarisable ρ → GlobalTheory.LGrp.IsUnitarisable ρ') ∧ (GlobalTheory.LGrp.IsSpherical ρ K → GlobalTheory.LGrp.IsSpherical ρ' K) := by
  intro G _ _ K V _ _ W _ _ ρ ρ' φ hφ hρ
  let e : V ≃ₛₗ[starRingEnd ℂ] W := LinearEquiv.ofBijective φ hφ
  have he : ∀ g x, e (ρ g x) = ρ' g (e x) := hρ
  refine ⟨fun h => ?_, fun h => ⟨fun w => ?_, fun U hU hc => ?_⟩, isUnitarisable e he, fun h h0 => h ?_⟩
  · haveI : IsSimpleOrder (Subrepresentation ρ) := h
    exact (subOrderIso e he).isSimpleOrder
  · obtain ⟨v, rfl⟩ := e.surjective w
    have := h.1 v
    convert this using 3 with g
    rw [← he]
    exact e.injective.eq_iff
  · haveI := h.2 U hU hc
    rw [← map_fixed e he U]
    have hfg : (fixed ρ U).FG := Module.Finite.iff_fg.1 inferInstance
    exact Module.Finite.iff_fg.2 (hfg.map _)
  · rw [← map_fixed e he K] at h0
    rw [eq_bot_iff]
    intro v hv
    have : e v ∈ (⊥ : Submodule ℂ W) := h0 ▸ Submodule.mem_map_of_mem hv
    simpa using this

end GlobalTheory.ConjRep
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_equiv_preserves_properties : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (φ : V →ₛₗ[starRingEnd ℂ] W), Function.Bijective φ → (∀ g x, φ (ρ g x) = ρ' g (φ x)) → (ρ.IsIrreducible → ρ'.IsIrreducible) ∧ (IsAdmissible ρ → IsAdmissible ρ') ∧ (GlobalTheory.LGrp.IsUnitarisable ρ → GlobalTheory.LGrp.IsUnitarisable ρ') ∧ (GlobalTheory.LGrp.IsSpherical ρ K → GlobalTheory.LGrp.IsSpherical ρ' K) := by
  atlas_forward_decl GlobalTheory.ConjRep.conj_transfer
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_acts_by_scalar_commutative : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), ρ.IsIrreducible → FiniteDimensional ℂ (fixed ρ K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed ρ K, heckeVec ρ K h x = c • x := by
  first | exact @GlobalTheory.LFun.HeckeScalar.heckeVec_scalar | exact GlobalTheory.LFun.HeckeScalar.heckeVec_scalar | (intros; apply GlobalTheory.LFun.HeckeScalar.heckeVec_scalar <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticPowerCharacter_splitPlaces_values_inverse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (w w' : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = w'.under (𝓞 F) → w ≠ w' → UnrAt μ w → UnrAt μ w' → val μ w * val μ w' = 1 := by
  first | exact @GlobalTheory.LFun.SplitVal.val_mul_val_eq_one | exact GlobalTheory.LFun.SplitVal.val_mul_val_eq_one | (intros; apply GlobalTheory.LFun.SplitVal.val_mul_val_eq_one <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_value_eq_one_at_inert_place_of_restrictsToQuadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), IsInertAt F E v w → UnrAt μ w → val μ w ^ 2 = 1 := by
  first | exact @GlobalTheory.LFun.val_sq_eq_one_of_isInertAt | exact GlobalTheory.LFun.val_sq_eq_one_of_isInertAt | (intros; apply GlobalTheory.LFun.val_sq_eq_one_of_isInertAt <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.LPositivity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Analysis

theorem isPosReal_iff {z : ℂ} : IsPosReal z ↔ ∃ r : ℝ, 0 < r ∧ z = r :=
  ⟨fun h => ⟨z.re, h.2, Complex.ext rfl (by simpa using h.1)⟩, by rintro ⟨r, hr, rfl⟩; exact ⟨rfl, hr⟩⟩

theorem isPosReal_prod {ι : Type} (s : Finset ι) {f : ι → ℂ} (h : ∀ i ∈ s, IsPosReal (f i)) :
    IsPosReal (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IsPosReal (fun a b ha hb => ?_) ⟨rfl, one_pos⟩ h
  obtain ⟨x, hx, rfl⟩ := isPosReal_iff.1 ha
  obtain ⟨y, hy, rfl⟩ := isPosReal_iff.1 hb
  exact isPosReal_iff.2 ⟨x * y, mul_pos hx hy, by simp⟩

theorem isPosReal_of_hasProd {ι : Type} {f : ι → ℂ} {a : ℂ} (ha : HasProd f a) (h0 : a ≠ 0)
    (h : ∀ i, IsPosReal (f i)) : IsPosReal a := by
  have hc : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  have := hc.mem_of_tendsto ha (Eventually.of_forall fun s =>
    ⟨(isPosReal_prod s fun i _ => h i).1, (isPosReal_prod s fun i _ => h i).2.le⟩)
  exact ⟨this.1, this.2.lt_of_ne fun e => h0 (Complex.ext e.symm this.1)⟩

theorem isPosReal_eulerFac {B : Multiset ℂˣ} {x : ℂ} (hB : B.map star = B) (hx : star x = x)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ < 1) : IsPosReal (eulerFac B x) := by
  have hre : ∀ b ∈ B, 0 < (1 - (b : ℂ) * x).re := fun b hb => by
    have := (Complex.re_le_norm _).trans_lt (h b hb)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  set u : ℂ := (B.map fun b : ℂˣ => Complex.log (1 - (b : ℂ) * x)).sum with hu
  have h1 : eulerPoly B x = Complex.exp u := by
    rw [hu, Complex.exp_multiset_sum, Multiset.map_map, eulerPoly]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => (Complex.exp_log fun e => ?_).symm)
    simpa [e] using hre b hb
  have h2 : starRingEnd ℂ u = u := by
    conv_rhs => rw [hu, ← hB, Multiset.map_map]
    rw [hu, map_multiset_sum, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => ?_)
    have h3 : (1 - (b : ℂ) * x).arg ≠ Real.pi := fun e => by
      have := (Complex.arg_eq_pi_iff.1 e).1
      linarith [hre b hb]
    simp only [Function.comp_apply, Units.coe_star]
    rw [← Complex.log_conj _ h3, map_sub, map_one, map_mul, show starRingEnd ℂ x = x from hx]
    rfl
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  exact isPosReal_iff.2 ⟨(Real.exp r)⁻¹, by positivity, by rw [eulerFac, h1, hr]; simp⟩

variable {K : Type} [Field K] [NumberField K]

theorem star_npow (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : star (npow w (-(s : ℂ))) = npow w (-(s : ℂ)) := by
  rw [npow, ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
  exact Complex.conj_ofReal _

theorem norm_lt_one_of_bounded {T : Set (HeightOneSpectrum (𝓞 K))} {c : Fam K} {r : ℕ} {κ : ℝ} (h : Bounded T c r κ)
    {s : ℂ} (hs : κ < s.re) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ T) :
    ∀ b ∈ c w, ‖(b : ℂ) * npow w (-s)‖ < 1 := fun _ hb =>
  (h.norm_le le_rfl hw hb).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith))

theorem summable_norm_mul {ι : Type} {a g : ι → ℂ} {c : ℂ} (ha : Summable fun i => ‖a i‖)
    (hg : Tendsto g cofinite (𝓝 c)) : Summable fun i => ‖a i * g i‖ := by
  refine summable_of_isBigO ha ?_
  simpa using ((Asymptotics.isBigO_refl a cofinite).mul (hg.isBigO_one ℂ)).norm_norm

theorem tendsto_one_of_summable {ι : Type} {g : ι → ℂ} (hg : Summable fun i => ‖g i - 1‖) :
    Tendsto g cofinite (𝓝 1) := tendsto_iff_norm_sub_tendsto_zero.2 hg.tendsto_cofinite_zero


theorem summable_prod {ι κ : Type} (s : Finset κ) {f : κ → ι → ℂ} (h : ∀ k ∈ s, Summable fun i => ‖f k i - 1‖) :
    Summable fun i => ‖∏ k ∈ s, f k i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [summable_zero]
  | insert k s hk ih =>
    have h1 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h2 := h k (Finset.mem_insert_self _ _)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
      ((summable_norm_mul h2 (tendsto_one_of_summable h1)).add h1)
    rw [Finset.prod_insert hk]
    exact (congrArg _ (by ring)).trans_le (norm_add_le _ _)

end Analysis

section Normalising

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]



end Normalising

section Transport

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem irreducible_comp (e : G ≃* H) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp e.symm.toMonoidHom) := by
  let f : Subrepresentation (ρ.comp e.symm.toMonoidHom) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g x hx => by simpa using S.apply_mem_toSubmodule (e g) hx⟩
      invFun := fun S => ⟨S.toSubmodule, fun g x hx => S.apply_mem_toSubmodule (e.symm g) hx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact f.isSimpleOrder

theorem unitarisable_comp (e : G ≃* H) (h : GlobalTheory.LGrp.IsUnitarisable ρ) :
    GlobalTheory.LGrp.IsUnitarisable (ρ.comp e.symm.toMonoidHom) :=
  h.imp fun _ hB => ⟨hB.1, hB.2.1, fun g => hB.2.2 (e.symm g)⟩

theorem fixed_comp (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K') :
    fixed (ρ.comp e.symm.toMonoidHom) K' = fixed ρ K := Submodule.ext fun _ => mem_fixed_comp_symm e hK

theorem smooth_comp [TopologicalSpace G] [TopologicalSpace H] (e : G ≃* H) (he : Continuous e.symm)
    (h : IsSmooth ρ) : IsSmooth (ρ.comp e.symm.toMonoidHom) := fun x => (h x).preimage he

theorem admissible_comp [TopologicalSpace G] [TopologicalSpace H] (e : G ≃* H) (he : Continuous e)
    (he' : Continuous e.symm) (h : IsAdmissible ρ) : IsAdmissible (ρ.comp e.symm.toMonoidHom) := by
  refine ⟨smooth_comp e he' h.1, fun K ho hk => ?_⟩
  rw [fixed_comp e (K := K.comap e.toMonoidHom) fun _ => Iff.rfl]
  refine h.2 _ (ho.preimage he) ?_
  convert hk.image he' using 1
  exact (e.toEquiv.image_symm_eq_preimage _).symm

end Transport

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {B : Multiset ℂˣ}
  (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsLattice E L) (hd : IsSelfDualAt σ J L v)

include hc hJ hL hd

theorem exists_inert_chart (h : w.under (𝓞 F) = v) (hv : IsInertAt F E v w) :
    ∃ c ϖ e, IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨-, ⟨c, hcj, -⟩, -, -, H⟩ := (exists_isInertChart σ hc v).2 w h hv
  obtain ⟨⟨ϖ, hU⟩, H⟩ := H c hcj
  obtain ⟨e, he⟩ := H n J L hJ hL.fg hL.span_eq_top hd
  exact ⟨c, ϖ, e, hU, he⟩

theorem exists_hasParam (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v ∨ IsInertAt F E v w)
    (hi : ρ.IsIrreducible) (ha : IsAdmissible ρ) (hs : GlobalTheory.LGrp.IsSpherical ρ (stabLoc σ J L v)) :
    ∃ B, HasParam σ J L h ρ B := by
  have hf := ha.2 _ (isOpen_stabLoc σ J L v) (isCompact_stabLoc σ J L v)
  rcases hv with hv | hv
  · obtain ⟨e, he, -⟩ := SplitChart.exists_isSplitChart hc hJ hL.fg hL.span_eq_top h hv hd
    obtain ⟨B, hB⟩ := GlobalTheory.T.satake_parameter_of_spherical E w n V (ρ.comp e.symm.toMonoidHom)
      (fun e0 => hs ((fixed_comp e he.2).symm.trans e0))
      (GlobalTheory.T.hecke_acts_by_scalar_commutative _ _ (Final.GLintComm E w n) (Final.HeckeCommGL E w n ℂ) V _ (irreducible_comp e hi)
        (by rw [fixed_comp e he.2]; exact hf))
    exact ⟨B, Or.inl ⟨hv, e, he, hB⟩⟩
  · obtain ⟨c, ϖ, e, hU, he, h1, h2⟩ := exists_inert_chart hc hJ hL hd h hv
    obtain ⟨α, hα⟩ := GlobalTheory.T.exists_satake_parameter_spherical_unramifiedUnitary E w ϖ c _ n hU V (ρ.comp e.symm.toMonoidHom) (irreducible_comp e hi)
      (admissible_comp e h1 h2 ha) fun e0 => hs ((fixed_comp e he.2.2).symm.trans e0)
    exact ⟨_, Or.inr ⟨hv, c, ϖ, e, α, hU, he, hα, rfl⟩⟩



omit hc hJ hL hd in

theorem param_star_of_inert (hv : IsInertAt F E v w) (hu : GlobalTheory.LGrp.IsUnitarisable ρ) (hB : HasParam σ J L h ρ B) :
    B.map star = B := by
  rcases hB with ⟨hv', -⟩ | ⟨-, c, ϖ, e, α, hU, he, hα, rfl⟩
  · exact absurd hv' (not_isSplit_of_isInertAt hv)
  · obtain ⟨x, hx⟩ := hα.exists_vec
    conv_rhs => rw [← bcParam_eq_of_satU_eq (α := fun i => star (α i)) hU
      (GlobalTheory.T.unitarySatakeTransform_star_parameter_eq_of_unitarisable _ ϖ c _ n hU V _ x α (unitarisable_comp e hu) hx)]
    simp [bcParam, star_inv, Function.comp_def]

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_or_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) ∨ IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w := by
  haveI := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  set v := w.under (𝓞 D.host.F) with hv
  rcases (GlobalTheory.quadratic_unramified_iff_inert_or_split D.host.F D.host.E (isCMExt_host D).2.2.1 v).1
    (fun u _ => Algebra.unramified_iff_forall.1 inferInstance ⟨u.asIdeal, u.isPrime⟩) with h | h
  · exact Or.inr ((h.isMaximal (Ideal.map_ne_bot_of_ne_bot v.ne_bot)).eq_of_le w.isPrime.ne_top Ideal.map_comap_le)
  · obtain ⟨P, Q, hne, e⟩ := Set.ncard_eq_two.1 h
    have hP : P ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have hQ : Q ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have := hP.2
    have := hQ.2
    exact Or.inl ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      ⟨Q, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, fun e => hne (congrArg (·.asIdeal) e),
      hP.2.over.symm, hQ.2.over.symm⟩

variable {D : D7} {V : HSp D}


theorem star_eq_inv {z : ℂˣ} (h : ‖(z : ℂ)‖ = 1) : star z = z⁻¹ :=
  Units.ext (by simpa using (Complex.inv_eq_conj h).symm)


end Global


end GlobalTheory.LPositivity

end
end
