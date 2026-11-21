import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrLoc
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieSep
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieIdx

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp Formalism.L2.Herm

def GenMod {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (M : ℕ) : Prop :=
  ∃ b : Fin r → Fin r → E, (∀ a, b a ∈ Λ) ∧
    ∀ x ∈ Λ, ∃ c : Fin r → 𝓞 E, ∃ z ∈ Λ, x = ∑ a, c a • b a + (M : E) • z

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

theorem mem_crdLat (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : Fin S.rank → E) :
    x ∈ crdLat S L ↔ (crd S).symm x ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem isLat_crd (S : HSpace E) (L : Submodule (𝓞 E) S.V) (h : Submodule.IsLattice E L) :
    IsLat (crdLat S L) := by
  refine ⟨Module.Finite.iff_fg.2 (h.fg.map _), ?_⟩
  have h1 : ((crdLat S L : Submodule (𝓞 E) (Fin S.rank → E)) : Set (Fin S.rank → E)) = (crd S) '' (L : Set S.V) := by
    ext x
    rw [SetLike.mem_coe, mem_crdLat]
    constructor
    · intro hx; exact ⟨_, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [h1]
  show Submodule.span E ((crd S : S.V →ₗ[E] (Fin S.rank → E)) '' (L : Set S.V)) = ⊤
  rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (crd S).surjective


def matOf (S : HSpace E) (γ : S.V ≃ₗ[E] S.V) : GL (Fin S.rank) E :=
  Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin S.rank → E)).symm
      (((crd S).symm.trans γ).trans (crd S)))

theorem matOf_mulVec (S : HSpace E) (γ : S.V ≃ₗ[E] S.V) (u : Fin S.rank → E) :
    (matOf S γ : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ u = crd S (γ ((crd S).symm u)) := by
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, matOf, MulEquiv.apply_symm_apply]
  rfl

theorem hform_single {n : Type} [Fintype n] [DecidableEq n] (σ : E →+* E) (A : Matrix n n E) (i j : n) :
    hform σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [hform, Pi.single_apply, apply_ite σ, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem UJ_of_hform {n : Type} [Fintype n] [DecidableEq n] (σ : E →+* E) (J : Matrix n n E) (G : GL n E)
    (h : ∀ u w, hform σ J ((G : Matrix n n E) *ᵥ u) ((G : Matrix n n E) *ᵥ w) = hform σ J u w) : G ∈ UJ σ J := by
  show cT σ (G : Matrix n n E) * J * (G : Matrix n n E) = J
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hform_mulVec, hform_single, hform_single] at this
  exact this

theorem frames_of_tie {hc : CMData F E} {S : HSpace E} {Lb : Submodule (𝓞 E) (Fin S.rank → E)}
    {U : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F))} {cls : Type} {stab : cls → Type} [∀ c, Group (stab c)]
    {lat : cls → Submodule (𝓞 E) S.V} (X : ClassTie hc S Lb U stab lat)
    (hLbd : IsLat (dualL hc S Lb)) (hΔ : ∀ c, Submodule.IsLattice E (Formalism.HermitianLatticesTheory.dual S.hT (lat c)))
    (M : ℕ) (hM : M ≠ 0) (hgen : GenMod (dualL hc S Lb) M)
    (hU : ∀ k : GL (Fin S.rank) 𝒜, k ∈ UAf hc S →
      (∀ u, u ∈ hat F Lb ↔ (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u ∈ hat F Lb) →
      (∀ u ∈ hat F (dualL hc S Lb), ∃ z ∈ hat F (dualL hc S Lb),
        (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u - u = (M : 𝒜) • z) → k ∈ U) :
    ∃ e : cls → Fin S.rank → S.V, (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub S (lat c)) ∧
      ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls S M (lat c) (lat c') (e c) (e c') → c = c' := by
  obtain ⟨b, hb, hgen⟩ := hgen
  have hΔ' : ∀ c, IsLat (dl hc.sig S.gram (crdLat S (lat c))) := by
    intro c
    have := isLat_crd S _ (hΔ c)
    rwa [crdLat_dual hc] at this
  obtain ⟨e, he, hsep⟩ := frames_core (F := F) hc.sig S.gram Lb hLbd (fun c => crdLat S (lat c)) hΔ'
    (fun c => (X.y c : GL (Fin S.rank) 𝒜)) (fun c => (X.y c).2) (fun c u => X.y_lat c u) M hM b hb hgen
  have hmemd : ∀ (L : Submodule (𝓞 E) S.V) (x : Fin S.rank → E),
      x ∈ dl hc.sig S.gram (crdLat S L) ↔ (crd S).symm x ∈ Formalism.HermitianLatticesTheory.dual S.hT L := by
    intro L x
    rw [← mem_crdLat]
    show x ∈ dualL hc S (crdLat S L) ↔ _
    rw [← crdLat_dual hc]
  refine ⟨fun c a => (crd S).symm (e c a), fun c a => ?_, ?_⟩
  · rw [dualSub_eq]
    exact (hmemd _ _).1 (he c a)
  rintro c c' ⟨γ, hγ, hL, hz⟩
  set G := matOf S γ with hGdef
  have hG : G ∈ UJ (hc.sig : E →+* E) S.gram := by
    refine UJ_of_hform _ _ G fun u w => ?_
    rw [matOf_mulVec, matOf_mulVec, ← hT_crd hc, hγ, hT_crd hc]
    simp
  have hΛ : ∀ x, x ∈ crdLat S (lat c) ↔ (G : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ x ∈ crdLat S (lat c') := by
    intro x
    rw [mem_crdLat, mem_crdLat, matOf_mulVec, LinearEquiv.symm_apply_apply]
    exact hL _
  have hGe : ∀ a, ∃ w ∈ dl hc.sig S.gram (crdLat S (lat c')),
      (G : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ e c a - e c' a = (M : E) • w := by
    intro a
    obtain ⟨z, hzm, hze⟩ := hz a
    refine ⟨crd S z, (hmemd _ _).2 ?_, ?_⟩
    · rw [LinearEquiv.symm_apply_apply]
      have h := hzm
      rw [dualSub_eq] at h
      exact h
    · rw [matOf_mulVec]
      have := congrArg (crd S) hze
      rw [map_sub, LinearEquiv.apply_symm_apply, map_smul] at this
      exact this
  obtain ⟨k, hkU, hst, hcg, hyk⟩ := hsep c c' G hG hΛ hGe
  have hkUU := hU k hkU hst hcg
  refine Formalism.L2.GlobalTheoryTheory.TraceIntegrality.ClassTie.eq_of_mul X ⟨bc (inclE (F := F) (Af F)) G, bc_mem_UPts hc.sig S.gram G hG⟩
    ⟨k⁻¹, inv_mem hkU⟩ ?_ (inv_mem hkUU) ?_
  · exact Subgroup.mem_subgroupOf.2 ⟨G, hG, rfl⟩
  · exact Subtype.ext hyk

end Gen

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
end

section
noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

variable {E : Type} [Field E] [NumberField E]

theorem natCast_ne_zero_int (M : ℕ) (hM : M ≠ 0) : ((M : ℕ) : 𝓞 E) ≠ 0 := by
  intro h
  apply hM
  have := congrArg (algebraMap (𝓞 E) E) h
  simpa using this

theorem ideal_gen (M : ℕ) (hM : M ≠ 0) (J : Ideal (𝓞 E)) :
    ∃ a ∈ J, ∀ j ∈ J, ∃ c : 𝓞 E, ∃ j' ∈ J, j = c * a + (M : 𝓞 E) * j' := by
  by_cases hJ : J = ⊥
  · refine ⟨0, zero_mem _, fun j hj => ⟨0, 0, zero_mem _, ?_⟩⟩
    rw [hJ, Ideal.mem_bot] at hj
    simp [hj]
  · have hM' := natCast_ne_zero_int (E := E) M hM
    have hle : Ideal.span {((M : ℕ) : 𝓞 E)} * J ≤ J := Ideal.mul_le.2 (fun r _ s hs => J.mul_mem_left r hs)
    have hne : Ideal.span {((M : ℕ) : 𝓞 E)} * J ≠ 0 := by
      intro h
      rw [Ideal.zero_eq_bot, Ideal.mul_eq_bot] at h
      rcases h with h | h
      · exact hM' (Ideal.span_singleton_eq_bot.1 h)
      · exact hJ h
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
    have haJ : a ∈ J := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    refine ⟨a, haJ, fun j hj => ?_⟩
    rw [← ha, Submodule.mem_sup] at hj
    obtain ⟨i, hi, s, hs, rfl⟩ := hj
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.1 hi
    exact ⟨c, z, hz, by ring⟩

theorem clear_fg (P : Submodule (𝓞 E) E) (hP : P.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ p ∈ P, ∃ q : 𝓞 E, (d : E) * p = q := by
  obtain ⟨s, rfl⟩ := hP
  obtain ⟨⟨b, hb⟩, hbs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) s
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun p hp => ?_⟩
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨q, hq⟩ := hbs p hp
    refine ⟨q, ?_⟩
    have hq' : (q : E) = (b : E) * p := by
      have := hq
      rw [Algebra.smul_def] at this
      exact this
    exact hq'.symm
  | zero => exact ⟨0, by simp⟩
  | add p p' _ _ h h' =>
    obtain ⟨q, hq⟩ := h
    obtain ⟨q', hq'⟩ := h'
    exact ⟨q + q', by push_cast; linear_combination hq + hq'⟩
  | smul a p _ h =>
    obtain ⟨q, hq⟩ := h
    refine ⟨a * q, ?_⟩
    show (b : E) * ((a : E) * p) = ((a * q : 𝓞 E) : E)
    push_cast
    linear_combination (a : E) * hq

theorem sub_gen (M : ℕ) (hM : M ≠ 0) (P : Submodule (𝓞 E) E) (hP : P.FG) :
    ∃ a ∈ P, ∀ p ∈ P, ∃ c : 𝓞 E, ∃ p' ∈ P, p = c • a + (M : E) • p' := by
  obtain ⟨d, hd, hdP⟩ := clear_fg P hP
  have hd' : (d : E) ≠ 0 := by
    intro h; apply hd; exact_mod_cast h
  let J : Ideal (𝓞 E) :=
    { carrier := {q | ∃ p ∈ P, (q : E) = (d : E) * p}
      add_mem' := by
        rintro q q' ⟨p, hp, hq⟩ ⟨p', hp', hq'⟩
        exact ⟨p + p', add_mem hp hp', by push_cast; linear_combination hq + hq'⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c q ⟨p, hp, hq⟩
        refine ⟨c • p, Submodule.smul_mem _ c hp, ?_⟩
        show ((c * q : 𝓞 E) : E) = (d : E) * ((c : E) * p)
        push_cast
        linear_combination (c : E) * hq }
  obtain ⟨a', ⟨pa, hpa, ha'⟩, hgen⟩ := ideal_gen M hM J
  refine ⟨pa, hpa, fun p hp => ?_⟩
  obtain ⟨q, hq⟩ := hdP p hp
  obtain ⟨c, j', ⟨pj, hpj, hj'⟩, hcj⟩ := hgen q ⟨p, hp, hq.symm⟩
  refine ⟨c, pj, hpj, ?_⟩
  have h1 : (d : E) * p = (d : E) * ((c : E) * pa + (M : E) * pj) := by
    have h3 : (q : E) = (c : E) * (a' : E) + (M : E) * (j' : E) := by rw [hcj]; push_cast; ring
    linear_combination hq + h3 + (c : E) * ha' + (M : E) * hj'
  have h2 := mul_left_cancel₀ hd' h1
  rw [h2, Algebra.smul_def, smul_eq_mul]

def snoc0 (r : ℕ) : (Fin r → E) →ₗ[E] (Fin (r + 1) → E) where
  toFun y i := if h : (i : ℕ) < r then y ⟨i, h⟩ else 0
  map_add' y y' := by
    funext i
    by_cases h : (i : ℕ) < r <;> simp [h]
  map_smul' c y := by
    funext i
    by_cases h : (i : ℕ) < r <;> simp [h]

theorem snoc_zero_castSucc (r : ℕ) (y : Fin r → E) (j : Fin r) : snoc0 r y j.castSucc = y j := by
  simp [snoc0]

theorem snoc_zero_last (r : ℕ) (y : Fin r → E) : snoc0 r y (Fin.last r) = 0 := by
  simp [snoc0]

theorem snoc_zero_injective (r : ℕ) : Function.Injective (snoc0 (E := E) r) := by
  intro y y' h
  funext j
  have := congrFun h j.castSucc
  rwa [snoc_zero_castSucc, snoc_zero_castSucc] at this

theorem genMod_fg (M : ℕ) (hM : M ≠ 0) : ∀ (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → GenMod Λ M := by
  intro r
  induction r with
  | zero =>
    intro Λ _
    refine ⟨fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun x _ => ⟨0, 0, zero_mem _, ?_⟩⟩
    exact Subsingleton.elim _ _
  | succ r ih =>
    intro Λ hΛ
    haveI : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian _ hΛ

    let Λ0 : Submodule (𝓞 E) (Fin r → E) := Λ.comap ((snoc0 r).restrictScalars (𝓞 E))
    let φ : Λ0 →ₗ[𝓞 E] Λ :=
      { toFun := fun x => ⟨snoc0 r (x : Fin r → E), x.2⟩
        map_add' := fun x y => by ext1; simp
        map_smul' := fun a x => by
          ext1
          show snoc0 r (a • (x : Fin r → E)) = a • snoc0 r (x : Fin r → E)
          rw [← algebraMap_smul E a (x : Fin r → E), map_smul, algebraMap_smul] }
    have hφ : Function.Injective φ := by
      intro x y h
      exact Subtype.ext (snoc_zero_injective r (congrArg Subtype.val h))
    haveI : IsNoetherian (𝓞 E) Λ0 := isNoetherian_of_injective φ hφ
    have hΛ0 : Λ0.FG := (Submodule.fg_top _).1 (IsNoetherian.noetherian ⊤)
    obtain ⟨b0, hb0, hgen0⟩ := ih Λ0 hΛ0

    let P : Submodule (𝓞 E) E := Λ.map ((LinearMap.proj (Fin.last r) : (Fin (r + 1) → E) →ₗ[E] E).restrictScalars (𝓞 E))
    obtain ⟨a, ⟨xa, hxa, hxae⟩, hgenP⟩ := sub_gen M hM P (hΛ.map _)
    simp only [LinearMap.coe_restrictScalars, LinearMap.coe_proj, Function.eval] at hxae
    refine ⟨Fin.lastCases xa (fun j => snoc0 r (b0 j)), fun i => ?_, fun x hx => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.lastCases_last]; exact hxa
      · simp only [Fin.lastCases_castSucc]; exact hb0 j
    · obtain ⟨c, p', ⟨xj, hxj, hxje⟩, hce⟩ := hgenP (x (Fin.last r)) ⟨x, hx, rfl⟩
      simp only [LinearMap.coe_restrictScalars, LinearMap.coe_proj, Function.eval] at hxje
      set y : Fin (r + 1) → E := x - c • xa - (M : E) • xj with hy
      have hyΛ : y ∈ Λ := by
        refine sub_mem (sub_mem hx (Submodule.smul_mem _ c hxa)) ?_
        have : (M : E) • xj = ((M : ℕ) : 𝓞 E) • xj := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        rw [this]
        exact Submodule.smul_mem _ _ hxj
      have hylast : y (Fin.last r) = 0 := by
        rw [hy]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hce, hxae, hxje, Algebra.smul_def, Algebra.smul_def]
        simp
      set y0 : Fin r → E := fun j => y j.castSucc with hy0
      have hyy : snoc0 r y0 = y := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [snoc_zero_last, hylast]
        · rw [snoc_zero_castSucc]
      have hy0Λ : y0 ∈ Λ0 := by
        show snoc0 r y0 ∈ Λ
        rw [hyy]; exact hyΛ
      obtain ⟨c', z0, hz0, hz0e⟩ := hgen0 y0 hy0Λ
      refine ⟨Fin.lastCases c c', xj + snoc0 r z0, add_mem hxj hz0, ?_⟩
      have hx' : x = c • xa + (M : E) • xj + snoc0 r y0 := by
        rw [hyy, hy]; abel
      rw [hx', hz0e, Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, map_add, map_sum, smul_add]
      have hs : ∀ j, snoc0 r (c' j • b0 j) = c' j • snoc0 r (b0 j) := by
        intro j
        rw [← algebraMap_smul E (c' j) (b0 j), map_smul, algebraMap_smul]
      simp only [hs, map_smul]
      abel


end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
end
