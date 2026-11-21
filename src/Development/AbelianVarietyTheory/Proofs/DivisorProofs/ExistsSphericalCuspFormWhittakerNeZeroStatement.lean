import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperator
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuousStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup

section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter

namespace GlobalTheory.JSW.SphVec

open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.LFun

theorem map_mem_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {K : Subgroup G}
    (S : V →ₗ[ℂ] W) (hS : ∀ h v, S (ρ h v) = σ h (S v)) {v : V} (hv : v ∈ twKer ρ K 1) : S v ∈ twKer σ K 1 := by
  have h : (twKer ρ K 1).map S ≤ twKer σ K 1 := by
    rw [twKer, Submodule.map_span_le]
    rintro _ ⟨n, u, rfl⟩
    exact Submodule.subset_span ⟨n, S u, by simp [hS]⟩
  exact h ⟨v, hv, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_fixed_mem (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (hS : GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) (U : Submodule ℂ π.V)
    (hU : ∀ g, ∀ v ∈ U, π.locRep w g v ∈ U) {y : π.V} (hy : y ∈ U) (hy0 : y ≠ 0) :
    ∃ x ∈ U, x ≠ 0 ∧ ∀ k ∈ KGL w a, π.locRep w k x = x := by
  have hK : IsCompact ((KGL w a : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have hsm : IsSmooth (π.locRep w) := π.isSmooth_locRep w
  have hsU : IsSmooth (GlobalTheory.PRep.sub (π.locRep w) U hU) := fun v => by
    convert hsm v.1 using 1
    ext g
    exact Subtype.ext_iff
  by_contra hne
  have hbot : fixed (GlobalTheory.PRep.sub (π.locRep w) U hU) (KGL w a) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra h0
    exact hne ⟨v.1, v.2, fun h => h0 (Subtype.ext h), fun k hk =>
      congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hv k hk)⟩
  have htop := (GlobalTheory.LocGL.isCompl_fixed_twKer hsU hK).sup_eq_top
  rw [hbot, bot_sup_eq] at htop
  have hall : ∀ g, π.locRep w g y ∈ twKer (π.locRep w) (KGL w a) 1 := fun g =>
    map_mem_twKer (ρ := GlobalTheory.PRep.sub (π.locRep w) U hU) U.subtype (fun _ _ => rfl)
      (v := ⟨_, hU g y hy⟩) (htop ▸ Submodule.mem_top)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hS
  let Wl : Submodule ℂ π.V := ⨅ g, (twKer (π.locRep w) (KGL w a) 1).comap (π.locRep w g)
  have memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (KGL w a) 1 := fun v => by
    simp [Wl, Submodule.mem_iInf]
  have stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype) := by
    rintro o _ ⟨v, hv, rfl⟩
    obtain ⟨g, S, hS, ho⟩ := GlobalTheory.LocFactor.op_eq_locRep_comp π w o
    have hv' := (memWl v).1 hv
    refine ⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩
    rw [ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
    have e := LinearMap.congr_fun (hS (h * g)) v
    simp only [LinearMap.comp_apply] at e
    rw [← e]
    exact map_mem_twKer S (fun h v => LinearMap.congr_fun (hS h) v) (hv' (h * g))
  rcases π.irred _ (Submodule.map_subtype_le _ _) stab with h | h
  · have h1 : (y : Sm E a) ∈ Wl.map π.V.subtype := ⟨y, (memWl y).2 hall, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact hy0 (Subtype.ext h1)
  · have h1 : (x : Sm E a) ∈ Wl.map π.V.subtype := by rw [h]; exact x.2
    obtain ⟨x', hx', e⟩ := h1
    obtain rfl : x' = x := Subtype.ext e
    have h2 := (memWl x').1 hx' 1
    rw [map_one, Module.End.one_apply] at h2
    exact hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)

theorem locRep_comm (π : CuspSub E a) {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v)
    (k : GL (Fin a) (v.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) (x : π.V) :
    π.locRep v k (π.locRep w g x) = π.locRep w g (π.locRep v k x) := by
  simp only [CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    LocSph.comm_locGL w _ (pLoc_locGL_of_ne h k)]

theorem exists_fixed_union (π : CuspSub E a) (T : Set (HeightOneSpectrum (𝓞 E))) {y : π.V} (hy0 : y ≠ 0)
    (hy : ∀ v ∈ T, ∀ k ∈ KGL v a, π.locRep v k y = y) (F : Finset (HeightOneSpectrum (𝓞 E)))
    (hF : ∀ w ∈ F, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) :
    ∃ x : π.V, x ≠ 0 ∧ ∀ v, v ∈ T ∨ v ∈ F → ∀ k ∈ KGL v a, π.locRep v k x = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨y, hy0, fun v hv => hy v (by simpa using hv)⟩
  | insert w F _ ih =>
    obtain ⟨x, hx0, hx⟩ := ih fun v hv => hF v (Finset.mem_insert_of_mem hv)
    let U : Submodule ℂ π.V := ⨅ v : {v // (v ∈ T ∨ v ∈ F) ∧ w ≠ v}, fixed (π.locRep v.1) (KGL v.1 a)
    have memU : ∀ z, z ∈ U ↔ ∀ v, (v ∈ T ∨ v ∈ F) → w ≠ v → ∀ k ∈ KGL v a, π.locRep v k z = z := fun z => by
      simp only [U, Submodule.mem_iInf, GlobalTheory.LGrp.mem_fixed, Subtype.forall]
      exact ⟨fun h v h1 h2 => h v ⟨h1, h2⟩, fun h v h1 => h v h1.1 h1.2⟩
    obtain ⟨z, hz, hz0, hzw⟩ := exists_fixed_mem π w (hF w (Finset.mem_insert_self _ _)) U
      (fun g z hz => (memU _).2 fun v hv hne k hk => by
        rw [locRep_comm π hne, (memU z).1 hz v hv hne k hk])
      ((memU x).2 fun v hv _ => hx v hv) hx0
    refine ⟨z, hz0, fun v hv => ?_⟩
    by_cases hne : w = v
    · subst hne; exact hzw
    · refine (memU z).1 hz v (hv.imp_right fun h => ?_) hne
      exact (Finset.mem_insert.1 h).resolve_left fun e => hne e.symm

theorem exists_sphVec_of_isSpherical (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ := by
  classical
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hev := LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨x, hx0, hx⟩ := exists_fixed_union π
    {w | ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ {k | finRep E a k φ = φ}}
    (y := ⟨φ, hφ⟩) (fun h => h0 (congrArg Subtype.val h))
    (by rintro v hv _ ⟨g, rfl⟩; exact Subtype.ext (hv g))
    (hev.toFinset.filter (· ∉ S)) (fun w hw => hS w (Finset.mem_filter.1 hw).2)
  refine ⟨x.1, x.2, fun h => hx0 (Subtype.ext h), fun w hw k hk => congrArg Subtype.val (hx w ?_ k hk)⟩
  refine (em _).imp_right fun h => Finset.mem_filter.2 ⟨hev.mem_toFinset.2 h, hw⟩

theorem exists_sphVec (π : CuspSub E a) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∃ B, HasSatGL w (π.locRep w) B) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec_of_isSpherical π S fun w hw => (hS w hw).elim fun _ h => h.1

theorem exists_sphVec_of_hasSat (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ)
    (h : ∀ w ∉ S, HasSatGL w (π.locRep w) (B w)) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec π S fun w hw => ⟨B w, h w hw⟩

end GlobalTheory.JSW.SphVec
end
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_spherical_vector_of_satake_family : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ), (∀ w ∉ S, GlobalTheory.LFun.HasSatGL w (π.locRep w) (B w)) → ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w a, act (.fin (locGL E a w k)) φ = φ := by
  atlas_forward_decl GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat
end

section
noncomputable section

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem IsCuspForm.mem_cuspForms {φ : Sm E a} (h : IsCuspForm φ) : φ.1 ∈ cuspForms E a :=
  (UpperTheory.V.Cm.isCuspForm_iff φ).1 h

theorem IsCuspForm.constantTerm_eq_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a) (h : IsCuspForm φ) : AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 :=
  h.mem_cuspForms.2

end GlobalTheory.CuspRep
end
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_of_isCuspForm' : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ → GroundTheory.Automorphic.AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 := by
  atlas_forward_decl GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.JSW

theorem eq_zero_of_whit_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → (∀ g, GlobalTheory.JSW.whit φ.1 g = 0) → φ = 0 := by
  intro E _ _ _ a φ hφ hW
  have hc : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E a φ hφ.1
  have hcusp := GlobalTheory.T.isCuspidal_of_isCuspForm' E a φ hφ
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant (K := E) (n := a) φ.1 :=
    fun γ g => hφ.1.left γ g
  let V : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | finRep E a k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hV : ∃ V : OpenSubgroup (GroundTheory.Automorphic.AdelicGLn.FiniteAdelicGL E a),
      ∀ g, ∀ v ∈ V, φ.1 (g * GroundTheory.Automorphic.AutomorphicForm.finEmb E a v) = φ.1 g :=
    ⟨⟨V, hφ.1.level⟩, fun g v hv => by
      rw [GlobalTheory.FinConj.finEmb_eq_finGL]
      have : (finRep E a v φ).1 g = φ.1 g := by rw [show finRep E a v φ = φ from hv]
      exact this⟩
  apply Subtype.ext
  exact GroundTheory.Automorphic.MultiplicityOne.eq_zero_of_whittaker_eq_zero hc hl hcusp hV hW

end GlobalTheory.JSW
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ → (∀ g, GlobalTheory.JSW.whit φ.1 g = 0) → φ = 0 := by
  atlas_forward_decl GlobalTheory.JSW.eq_zero_of_whit_eq_zero
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.GLFinPlaces

theorem gl_mem_int_cofinite (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w a}.Finite := by
  have hent : ∀ M : Matrix (Fin a) (Fin a) (Af E), ∀ᶠ w in Filter.cofinite,
      ∀ i j, (M i j) w ∈ w.adicCompletionIntegers E := by
    intro M
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact (M i j).2
  have h := (hent (k : Matrix (Fin a) (Fin a) (Af E))).and (hent ((k⁻¹ : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)))
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hg
  apply hw
  have key : ∀ M : Matrix (Fin a) (Fin a) (Af E), (∀ i j, (M i j) w ∈ w.adicCompletionIntegers E) →
      M.map (pLoc E w) ∈ (RingHom.mapMatrix (m := Fin a) (Ov E w).subtype).range := by
    intro M hM
    exact ⟨Matrix.of fun i j => (⟨(M i j) w, hM i j⟩ : Ov E w), by ext i j; rfl⟩
  refine P.glint_mem_range_of_integral _ _ ?_ ?_
  · exact key _ hg.1
  · rw [← map_inv]
    exact key _ hg.2

end GlobalTheory.GLFinPlaces
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)), {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w a}.Finite := by
  atlas_forward_decl GlobalTheory.GLFinPlaces.gl_mem_int_cofinite
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory

theorem outsideS_elt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  intro E _ _ a S k
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨k, fun w _ => rfl, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w S hwS ih =>
    obtain ⟨k', h1, h2⟩ := ih
    refine ⟨k' * (locGL E a w (GeneralLinearGroup.map (pLoc E w) k'))⁻¹, ?_, ?_⟩
    · intro v hv
      have hvw : v ≠ w := fun e => hv (e ▸ Finset.mem_insert_self _ _)
      rw [map_mul, map_inv, pLoc_locGL_of_ne hvw, inv_one, mul_one]
      exact h1 v (fun h => hv (Finset.mem_insert_of_mem h))
    · intro v hv
      rw [map_mul, map_inv]
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL, mul_inv_cancel]
      · rw [pLoc_locGL_of_ne hvw, inv_one, mul_one]
        exact h2 v ((Finset.mem_insert.1 hv).resolve_left hvw)

end GlobalTheory
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicGL_agree_outside_trivial_on_finset : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  atlas_forward_decl GlobalTheory.outsideS_elt
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

noncomputable section

namespace GlobalTheory.IwasawaGL

theorem diagPow_val {K : Type} [Field K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    ((GlobalTheory.JSW.diagPow ϖ l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => ((ϖ ^ l i : Kˣ) : K)) := rfl

theorem exists_unit_part (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (x : w.adicCompletion E)
    (hx : x ≠ 0) :
    ∃ e : ℤ, Valued.v (x * ((ϖ ^ (-e) : (w.adicCompletion E)ˣ) : w.adicCompletion E)) = 1 := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨γ, hγ⟩ := WithZero.ne_zero_iff_exists.1 h0
  refine ⟨-Multiplicative.toAdd γ, ?_⟩
  rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← hγ, neg_neg,
    ← WithZero.coe_zpow, ← WithZero.coe_mul]
  rw [show (1 : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

theorem iwasawa_diagPow : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ g : GL (Fin a) (w.adicCompletion E), ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w a, g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k := by
  intro E _ _ a w ϖ hϖ g
  obtain ⟨b, k, hb, hk, rfl⟩ := Formalism.UG.P.spherical_iwasawa E w g
  have hd : ∀ i, (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i ≠ 0 :=
    Formalism.UG.P.spherical_diag_ne_zero b hb
  choose e he using fun i => exists_unit_part E w ϖ hϖ _ (hd i)
  let c : Fin a → w.adicCompletion E := fun i =>
    (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i * ((ϖ ^ (-e i) : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have hc0 : ∀ i, c i ≠ 0 := fun i => mul_ne_zero (hd i) (Units.ne_zero _)
  have hcO : ∀ i, c i ∈ Ov E w := fun i => (he i).le
  have hcO' : ∀ i, (c i)⁻¹ ∈ Ov E w := fun i => by
    show Valued.v (c i)⁻¹ ≤ 1
    rw [map_inv₀, he i, inv_one]
  let Dc : GL (Fin a) (w.adicCompletion E) :=
    ⟨Matrix.diagonal c, Matrix.diagonal (fun i => (c i)⁻¹),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hc0 i),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hc0 i)⟩
  have hDc : Dc ∈ KGL w a := by
    refine Formalism.UG.P.glint_mem_range_of_integral (Ov E w) Dc
      ⟨Matrix.diagonal (fun i => (⟨c i, hcO i⟩ : Ov E w)), ?_⟩
      ⟨Matrix.diagonal (fun i => (⟨(c i)⁻¹, hcO' i⟩ : Ov E w)), ?_⟩
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc]
      split_ifs <;> simp
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc, Units.inv_mk]
      split_ifs <;> simp
  let N : ℕ := ∑ i, (e i).natAbs
  let l : Fin a → ℕ := fun i => (e i + N).toNat
  have hexp : ∀ i, ((ϖ⁻¹) ^ N * ϖ ^ (l i) : (w.adicCompletion E)ˣ) = ϖ ^ (e i) := by
    intro i
    have hle : (e i).natAbs ≤ N :=
      Finset.single_le_sum (f := fun j => (e j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h1 : -((e i).natAbs : ℤ) ≤ e i := by rw [Int.natCast_natAbs]; exact neg_abs_le _
    have h2 : ((e i).natAbs : ℤ) ≤ N := by exact_mod_cast hle
    have hl : ((l i : ℕ) : ℤ) = e i + N := Int.toNat_of_nonneg (by omega)
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_add, hl]
    congr 1; ring
  have hT : ((GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc : GL (Fin a) (w.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (w.adicCompletion E)) =
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) := by
    rw [Units.val_mul, Units.val_mul, diagPow_val, diagPow_val]
    change Matrix.diagonal _ * Matrix.diagonal _ * Matrix.diagonal c = _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← Units.val_mul, hexp i]
    simp only [c]
    rw [mul_left_comm, ← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]
  let u : GL (Fin a) (w.adicCompletion E) := b * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc)⁻¹
  have hu : u * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc) = b := by
    simp only [u]; group
  have hmat : (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) = b := by
    rw [← hT, ← Units.val_mul, hu]
  have hent : ∀ i j, (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j *
      (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) j j = (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
    intro i j
    have := congrFun (congrFun hmat i) j
    rwa [Matrix.mul_diagonal] at this
  have hmem : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := hent i j
      rw [hb hij] at h
      exact (mul_eq_zero.1 h).resolve_right (hd j)
    · exact mul_right_cancel₀ (hd i) (by rw [one_mul]; exact hent i i)
  refine ⟨u, hmem, N, l, Dc * k, Subgroup.mul_mem _ hDc hk, ?_⟩
  simp only [u]
  group

end GlobalTheory.IwasawaGL
end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_adicCompletionGL_diagonalPowers : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ g : GL (Fin a) (w.adicCompletion E), ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w a, g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k := by
  atlas_forward_decl GlobalTheory.IwasawaGL.iwasawa_diagPow
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix Filter Topology

noncomputable section

namespace GlobalTheory.CuspRep.TailFix

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem entry_int {w : HeightOneSpectrum (𝓞 E)} {g : GL (Fin a) (w.adicCompletion E)} (hg : g ∈ KGL w a)
    (i j : Fin a) : g i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨h, rfl⟩ := hg
  exact (h i j).2

theorem tendsto_of_loc {α : Type} {l : Filter α} {f : α → Af E} {x : Af E}
    (hx : ∀ v, pLoc E v x ∈ v.adicCompletionIntegers E) (hf : ∀ b v, pLoc E v (f b) ∈ v.adicCompletionIntegers E)
    (h : ∀ v, ∀ᶠ b in l, pLoc E v (f b) = pLoc E v x) : Tendsto f l (𝓝 x) := by
  let s := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let lift : ∀ y : Af E, (∀ v, pLoc E v y ∈ v.adicCompletionIntegers E) →
      ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletionIntegers E : Set (v.adicCompletion E)) :=
    fun y hy v => ⟨pLoc E v y, hy v⟩
  have hl : ∀ y hy, s (lift y hy) = y := fun y hy => FiniteAdeleRing.ext _ fun v => rfl
  have h1 : Tendsto (fun b => lift (f b) (hf b)) l (𝓝 (lift x hx)) := tendsto_pi_nhds.2 fun v =>
    tendsto_const_nhds.congr' <| (h v).mono fun b hb => Subtype.ext hb.symm
  have h2 := (hs.tendsto _).comp h1
  rw [hl] at h2
  exact h2.congr fun b => hl _ _

theorem exists_tail {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 (1 : GL (Fin a) (Af E))) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 E)), ∀ r : GL (Fin a) (Af E),
      (∀ v, GeneralLinearGroup.map (pLoc E v) r ∈ KGL v a) →
      (∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) r = 1) → r ∈ U := by
  classical
  by_contra hn
  push_neg at hn
  choose r hr1 hr2 hrU using hn
  have ent : ∀ q : Finset (HeightOneSpectrum (𝓞 E)) → GL (Fin a) (Af E),
      (∀ F v, GeneralLinearGroup.map (pLoc E v) (q F) ∈ KGL v a) →
      (∀ F, ∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) (q F) = 1) →
      Tendsto (fun F => (q F).val) atTop (𝓝 1) := fun q hq1 hq2 =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_of_loc (fun v => by rw [Matrix.one_apply]; split_ifs <;> simp)
        (fun F v => entry_int (hq1 F v) i j) fun v => by
        filter_upwards [eventually_ge_atTop {v}] with F hF
        have e := hq2 F v (hF (Finset.mem_singleton_self v))
        rw [← map_one (GeneralLinearGroup.map (pLoc E v))] at e
        exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) e
  have ht : Tendsto r atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (ent r hr1 hr2).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
      (ent (fun F => (r F)⁻¹) (fun F v => by rw [map_inv]; exact inv_mem (hr1 F v))
        (fun F v hv => by rw [map_inv, hr2 F v hv, inv_one])))
  obtain ⟨F, hF⟩ := (ht.eventually hU).exists
  exact hrU F hF

end GlobalTheory.CuspRep.TailFix

open GlobalTheory.CuspRep.TailFix in

theorem GlobalTheory.CuspRep.fixed_of_locFixed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)),
    (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E),
    (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w a) →
    (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  classical
  intro E _ _ _ a φ hφ S hS k hk1 hk2
  have hU : {x : GL (Fin a) (Af E) | finRep E a x φ = φ} ∈ 𝓝 (1 : GL (Fin a) (Af E)) :=
    hφ.level.mem_nhds (by simp)
  obtain ⟨F, hF⟩ := exists_tail hU
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w a) →
      (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) →
      (∀ w ∈ F, w ∉ T → GeneralLinearGroup.map (pLoc E w) k = 1) → finRep E a k φ = φ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro k h1 h2 h3
      refine hF k (fun v => ?_) (fun v hv => h3 v hv (by simp))
      by_cases hv : v ∈ S
      · rw [h2 v hv]; exact one_mem _
      · exact h1 v hv
    | insert w T hw ih =>
      intro k h1 h2 h3
      obtain ⟨g, hg⟩ : ∃ g, g = locGL E a w (GeneralLinearGroup.map (pLoc E w) k) := ⟨_, rfl⟩
      have hgH : finRep E a g φ = φ := by
        by_cases hwS : w ∈ S
        · rw [hg, h2 w hwS, map_one, map_one]; rfl
        · rw [hg]; exact hS w hwS _ (h1 w hwS)
      have e : ∀ v, GeneralLinearGroup.map (pLoc E v) (g⁻¹ * k) =
          if v = w then 1 else GeneralLinearGroup.map (pLoc E v) k := fun v => by
        rw [map_mul, map_inv]
        split_ifs with hv
        · subst hv; rw [hg, pLoc_locGL, inv_mul_cancel]
        · rw [hg, pLoc_locGL_of_ne hv, inv_one, one_mul]
      have hk' : finRep E a (g⁻¹ * k) φ = φ := by
        refine ih _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv hvT => ?_)
        · rw [e]; split_ifs
          · exact one_mem _
          · exact h1 v hv
        · rw [e]; split_ifs
          · rfl
          · exact h2 v hv
        · rw [e]; split_ifs with h
          · rfl
          · exact h3 v hv (by simp [h, hvT])
      calc finRep E a k φ = finRep E a (g * (g⁻¹ * k)) φ := by rw [mul_inv_cancel_left]
        _ = φ := by rw [map_mul, Module.End.mul_apply, hk', hgH]
  exact key F k hk1 hk2 (fun w hw hwF => absurd hw hwF)
end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w a) → (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  atlas_forward_decl GlobalTheory.CuspRep.fixed_of_locFixed
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

noncomputable section

namespace GlobalTheory.JSW.NzSph

theorem finite_bad (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w a}.Finite :=
  GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places E a k

theorem exists_outside (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (k : GL (Fin a) (Af E)) : ∃ k' : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧
      ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 :=
  GlobalTheory.T.exists_finiteAdelicGL_agree_outside_trivial_on_finset E a S k

theorem local_decomp (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w a,
      g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k :=
  GlobalTheory.T.iwasawa_decomposition_adicCompletionGL_diagonalPowers E a w ϖ hϖ g

theorem act_fin_eq_of_outside (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (hφ : IsAutForm φ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) (k : GL (Fin a) (Af E))
    (hk : ∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w a)
    (hk1 : ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) : act (.fin k) φ = φ :=
  GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed E a φ hφ S hS k hk hk1

end GlobalTheory.JSW.NzSph

namespace GlobalTheory.JSW.NzSph

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem map_pLoc_pFin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comp_finGL (v : HeightOneSpectrum (𝓞 E)) (h : GL (Fin a) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a h) = GeneralLinearGroup.map (pLoc E v) h := by
  rw [finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]

theorem diagPow_const_comm {K : Type} [CommRing K] {n : ℕ} (c : Kˣ) (N : ℕ) (h : GL (Fin n) K) :
    GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) * h = h * GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) := by
  ext i j
  simp [GlobalTheory.JSW.diagPow, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

variable [IsTotallyComplex E]

theorem whit_act_fin (φ : Sm E a) (k : GL (Fin a) (Af E)) (y : GA E a) :
    whit (act (.fin k) φ).1 y = whit φ.1 (y * finGL E a k) := by
  rw [whit_mul_right]; rfl

theorem act_fin_mul (k k' : GL (Fin a) (Af E)) (φ : Sm E a) :
    act (.fin (k * k')) φ = act (.fin k) (act (.fin k') φ) := by
  show finRep E a (k * k') φ = finRep E a k (finRep E a k' φ)
  rw [map_mul]; rfl

theorem exists_whittaker_ne_zero_induction_bad_places (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hψ : ∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w)
    (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ)
    (hα : ∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ g : GA E a,
      (∀ w ∉ S, w ∉ T → GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g ∈ KGL w a) → whit φ.1 g ≠ 0 →
      ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) ∧
        ∃ x ∈ GlobalTheory.JSW.supS E a S, whit φ.1 x ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro φ hφV hφ g hg hW
    obtain ⟨k, hk1, hk2⟩ := exists_outside E a S (GeneralLinearGroup.map (pFin E) g)
    have hinv : act (.fin k) φ = φ := act_fin_eq_of_outside E a φ (π.cusp φ hφV).1 S hφ k
      (fun w hw => by rw [hk1 w hw, map_pLoc_pFin]; exact hg w hw (Finset.notMem_empty w)) hk2
    refine ⟨φ, hφV, hφ, g * (finGL E a k)⁻¹, fun w hw => ?_, ?_⟩
    · rw [map_mul, map_inv, comp_finGL, hk1 w hw, map_pLoc_pFin, mul_inv_cancel]
    · have e : g = g * (finGL E a k)⁻¹ * finGL E a k := by group
      rw [e, ← whit_act_fin, hinv] at hW
      exact hW
  | insert w T hwT ih =>
    intro φ hφV hφ g hg hW
    by_cases hwS : w ∈ S
    · refine ih φ hφV hφ g (fun v hv hvT => hg v hv ?_) hW
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hv (h ▸ hwS), hvT⟩
    obtain ⟨ϖ0, hϖ0⟩ := exists_isUnifV (E := E) w
    have hne : ϖ0 ≠ 0 := fun h => by simp [IsUnifV, h] at hϖ0
    let ϖ : (w.adicCompletion E)ˣ := Units.mk0 ϖ0 hne
    have hϖ : IsUnifV E w (ϖ : w.adicCompletion E) := hϖ0
    let gw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g
    obtain ⟨u, hu, N, l, k, hk, hdec⟩ := local_decomp E a w ϖ hϖ gw
    let z := GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ : Fin a => N)
    let d := GlobalTheory.JSW.diagPow ϖ l
    let F : GL (Fin a) (w.adicCompletion E) →* GA E a := (finGL E a).comp (locGL E a w)
    have hF : ∀ h, F h = finGL E a (locGL E a w h) := fun h => rfl
    let y := g * (F gw)⁻¹
    have hyw : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y = 1 := by
      show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = 1
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL]; exact mul_inv_cancel _
    have hyv : ∀ v, v ≠ w → GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g := by
      intro v hv
      show GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = _
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL_of_ne hv, inv_one, mul_one]
    have hg' : g = y * F u * F z * F d * F k := by
      have : F gw = F u * F z * F d * F k := by
        rw [hdec, map_mul, map_mul, map_mul]
      calc g = y * F gw := by simp only [y]; group
        _ = _ := by rw [this]; simp only [mul_assoc]
    have hcont : Continuous φ.1 := (π.cusp _ hφV).1.continuous
    have hleft : AutomorphicForm.IsLeftInvariant φ.1 := fun γ x => by
      rw [show AdelicGLn.diagonal E a γ = ratGL E a γ from Units.ext (Matrix.ext fun _ _ => rfl)]
      exact (π.cusp _ hφV).1.left γ x

    have h1 : whit φ.1 (y * F u * F z * F d) ≠ 0 := by
      rw [hg', hF k, ← whit_act_fin, hφ w hwS k hk] at hW
      exact hW

    have h2 : whit φ.1 (y * F z * F d) ≠ 0 := by
      have e : y * F u * F z * F d = F u * (y * F z * F d) := by
        rw [hF u, commute_finGL_locGL w hyw u]; group
      rw [e, hF u, finGL_locGL_eq_uGL w hu, whit, whittaker_uGL_mul hcont hleft] at h1
      exact right_ne_zero_of_mul h1

    let φ₁ := act (.fin (locGL E a w z)) φ
    have hφ₁V : φ₁ ∈ π.V := π.stable _ φ hφV
    have hφ₁ : ∀ v ∉ S, ∀ k' ∈ KGL v a, act (.fin (locGL E a v k')) φ₁ = φ₁ := by
      intro v hv k' hk'
      have hc : locGL E a v k' * locGL E a w z = locGL E a w z * locGL E a v k' := by
        by_cases hvw : v = w
        · subst hvw; rw [← map_mul, ← map_mul, diagPow_const_comm]
        · exact (GlobalTheory.CuspRep.LocSph.comm_locGL v (locGL E a w z) (pLoc_locGL_of_ne hvw z) k').symm
      simp only [φ₁]
      rw [← act_fin_mul, hc, act_fin_mul, hφ v hv k' hk']
    have h3 : whit φ₁.1 (y * F d) ≠ 0 := by
      have e : y * F z * F d = y * F d * F z := by
        rw [mul_assoc y (F z), mul_assoc y (F d), ← map_mul, ← map_mul, diagPow_const_comm]
      rw [e, hF z, ← whit_act_fin] at h2
      exact h2
    have h4 : whit φ₁.1 y ≠ 0 := by
      have := GlobalTheory.JSW.whit_mul_locGL_diagPow E a π w (α w) (hψ w hwS) (hα w hwS) φ₁ hφ₁V (hφ₁ w hwS) y hyw ϖ hϖ l
      rw [hF d] at h3
      rw [this] at h3
      exact right_ne_zero_of_mul h3
    refine ih φ₁ hφ₁V hφ₁ y (fun v hv hvT => ?_) h4
    by_cases hvw : v = w
    · subst hvw; rw [hyw]; exact one_mem _
    · rw [hyv v hvw]
      exact hg v hv (by rw [Finset.mem_insert, not_or]; exact ⟨hvw, hvT⟩)

theorem exists_sph_whit_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  intro E _ _ _ m S hψ π α hα
  obtain ⟨φ₀, hφ₀V, hφ₀0, hφ₀K⟩ := GlobalTheory.T.exists_global_spherical_vector_of_satake_family E (m + 1) π S (fun w => Finset.univ.val.map (α w)) hα
  obtain ⟨g, hg⟩ : ∃ g, whit φ₀.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ₀0 (GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing E (m + 1) φ₀ (π.cusp φ₀ hφ₀V) h)
  have hfin := finite_bad E (m + 1) (GeneralLinearGroup.map (pFin E) g)
  refine exists_whittaker_ne_zero_induction_bad_places S hψ π α hα hfin.toFinset φ₀ hφ₀V hφ₀K g (fun w _ hwT => ?_) hg
  by_contra h
  refine hwT (hfin.mem_toFinset.2 ?_)
  show GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) ∉ KGL w (m + 1)
  rw [map_pLoc_pFin]; exact h

end GlobalTheory.JSW.NzSph
end
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  first | exact @GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | exact GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | (intros; apply GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero <;> assumption)
end
