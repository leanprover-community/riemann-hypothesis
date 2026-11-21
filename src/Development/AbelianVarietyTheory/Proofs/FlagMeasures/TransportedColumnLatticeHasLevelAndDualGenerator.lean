import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization

section
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.MidLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hconj (x y : S.V) : star (S.hT x y) = S.hT y x := by
  have h := S.herm.eq x y
  simpa [starRingEnd_apply] using h

def prj (e f : Fin r → S.V) : S.V →ₗ[E] S.V :=
  LinearMap.id - ∑ a, (S.hT (f a)).smulRight (e a) - ∑ a, (S.hT (e a)).smulRight (f a)

theorem prj_apply (e f : Fin r → S.V) (y : S.V) :
    prj e f y = y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a := by
  simp [prj, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

variable {e f : Fin r → S.V} (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hef in
theorem hfe (a b : Fin r) : S.hT (f a) (e b) = if b = a then 1 else 0 := by
  rw [← hconj, hef]; split_ifs <;> simp

include hee hef in
theorem prj_e (b : Fin r) : prj e f (e b) = 0 := by
  rw [prj_apply]; simp [hfe hef, hee]

include hff hef in
theorem prj_f (b : Fin r) : prj e f (f b) = 0 := by
  rw [prj_apply]; simp [hff, hef]

theorem prj_perp {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) : prj e f y = y := by
  rw [prj_apply]; simp [(hy _).1, (hy _).2]

theorem pair_prj {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) (x : S.V) :
    S.hT (prj e f x) y = S.hT x y := by
  rw [prj_apply]; simp [map_sub, map_sum, (hy _).1, (hy _).2]

include hee hef in
theorem prj_spanE {s : S.V} (hs : s ∈ Submodule.span E (Set.range e)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range e) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_e hee hef b)
  exact h hs

include hff hef in
theorem prj_spanF {s : S.V} (hs : s ∈ Submodule.span E (Set.range f)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range f) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_f hff hef b)
  exact h hs

theorem latSpanS_le_span (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    latSpanS aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.St.G.MidLat

open GlobalTheory.St.G.MidLat in

theorem GlobalTheory.St.G.midLat_selfDual_pairing : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧ ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb))) ∧ (∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = 1) ∧ ∀ y ∈ (VS D).L0, y - ∑ a, (VS D).hT (X.fY a) y • X.eX a - ∑ a, (VS D).hT (X.eX a) y • X.fY a ∈ X.Lb := by
  intro D X u
  have hprjL : ∀ y ∈ (VS D).L0, prj X.eX X.fY y ∈ X.Lb := by
    intro y hy
    rw [X.Lam_split] at hy
    obtain ⟨y1, hy1, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨s, hs, l, hl, rfl⟩ := Submodule.mem_sup.1 hy1
    have hs' := latSpanS_le_span _ _ hs
    have ht' := latSpanS_le_span _ _ ht
    rw [map_add, map_add, prj_spanE X.ee X.ef hs', prj_spanF X.ff X.ef ht', zero_add, add_zero,
      prj_perp (fun a => X.Lb_perp l hl a)]
    exact hl
  have hLbL : X.Lb ≤ (VS D).L0 := by
    rw [X.Lam_split]; exact le_sup_right.trans le_sup_left
  have h1 : ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
      ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧
        ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb)) := by
    intro y hy
    refine ⟨⟨fun h => ?_, fun h => hLbL h⟩, fun hint => ?_⟩
    · have := hprjL y h; rwa [prj_perp hy] at this
    · have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
      have hyL : y ∈ (VS D).L0 := by
        rw [← hU]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply, Submodule.mem_one]
        intro x hx
        obtain ⟨o, ho⟩ := hint _ (hprjL x hx)
        exact ⟨o, by rw [ho, pair_prj hy]⟩
      have := hprjL y hyL; rwa [prj_perp hy] at this
  refine ⟨h1, ?_, fun y hy => ?_⟩

  · let σ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (starRingEnd D.host.E)
    have hσ : ∀ o : 𝓞 D.host.E, ((σ o : 𝓞 D.host.E) : D.host.E) = star (o : D.host.E) := fun o => rfl
    let J : Ideal (𝓞 D.host.E) :=
      (LinearMap.range (((VS D).hT (X.zu u)).restrictScalars (𝓞 D.host.E) ∘ₗ X.Lb.subtype)).comap
        (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hJ : ∀ o, o ∈ J ↔ ∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = (o : D.host.E) := by
      intro o
      simp only [J, Submodule.mem_comap, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, LinearMap.restrictScalars_apply, Algebra.linearMap_apply, Subtype.exists,
        exists_prop]
    by_cases hJt : J = ⊤
    · obtain ⟨x, hx, hx1⟩ := (hJ 1).1 (hJt ▸ Submodule.mem_top)
      exact ⟨x, hx, by rw [hx1]; simp⟩
    exfalso
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJt
    have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)
    obtain ⟨c, hc, hc1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := D.host.E) hM0 hM.ne_top
    have hc' := (FractionalIdeal.mem_inv_iff (by rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero])).1 hc
    have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
    have hzL : X.zu u ∈ X.Lb := X.zu_Lb u
    have hwperp : ∀ a, (VS D).hT (X.eX a) (star c • X.zu u) = 0 ∧ (VS D).hT (X.fY a) (star c • X.zu u) = 0 := by
      intro a
      exact ⟨by rw [map_smul, smul_eq_mul, (X.zu_orth u a).1, mul_zero],
        by rw [map_smul, smul_eq_mul, (X.zu_orth u a).2, mul_zero]⟩
    have hwLb : star c • X.zu u ∈ X.Lb := by
      refine (h1 _ hwperp).2 ?_
      intro x hx
      have hxd : x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 := by rw [hU]; exact hLbL hx
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one] at hxd
      obtain ⟨o, ho⟩ := hxd (X.zu u) (hLbL hzL)
      have hoM : o ∈ M := hJM ((hJ o).2 ⟨x, hx, ho.symm⟩)
      obtain ⟨o', ho'⟩ := (FractionalIdeal.mem_one_iff _).1
        (hc' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨o, hoM, rfl⟩))
      refine ⟨σ o', ?_⟩
      change ((σ o' : 𝓞 D.host.E) : D.host.E) = _
      rw [hσ]
      change star (algebraMap (𝓞 D.host.E) D.host.E o') = _
      rw [ho', map_smul, smul_eq_mul, ← hconj (X.zu u) x, ← ho, star_mul, mul_comm]
    have hprim := (X.Fu_fixed u).2.2.2.2 (star c)
    dsimp only at hprim
    rw [X.flagZVector u] at hprim
    have horth : star c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (Formalism.MainNotions.S.Lat.hS D)
        (Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))) := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      have hX : Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
          = Submodule.span D.host.E (Set.range X.eX) := by
        show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
        rw [X.Fu_e u]
      rw [hX] at hx
      have hle : Submodule.span D.host.E (Set.range X.eX) ≤ LinearMap.ker ((VS D).hT (star c • X.zu u)) :=
        Submodule.span_le.2 (by
          rintro _ ⟨a, rfl⟩
          show (VS D).hT (star c • X.zu u) (X.eX a) = 0
          rw [← hconj, (hwperp a).1, star_zero])
      have := hle hx
      rw [LinearMap.mem_ker] at this
      rw [← hconj, this, star_zero]
    obtain ⟨o, ho⟩ := hprim ⟨Submodule.mem_sup_left ⟨hLbL hwLb, horth⟩, horth⟩
    apply hc1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨σ o, ?_⟩
    change ((σ o : 𝓞 D.host.E) : D.host.E) = c
    rw [hσ, ho, star_star]
  · have := hprjL y hy; rwa [prj_apply] at this
end

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.middleLattice_selfDual_anisotropic_pairing : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧ ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb))) ∧ (∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = 1) ∧ ∀ y ∈ (VS D).L0, y - ∑ a, (VS D).hT (X.fY a) y • X.eX a - ∑ a, (VS D).hT (X.eX a) y • X.fY a ∈ X.Lb := by
  atlas_forward_decl GlobalTheory.St.G.midLat_selfDual_pairing
end

section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  first | exact @GlobalTheory.St.G.record_facts | exact GlobalTheory.St.G.record_facts | (intros; apply GlobalTheory.St.G.record_facts <;> assumption)
end

section
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St
variable {D : D7}

theorem crd_sum_smul (X : HidaSetting D) {ι : Type} [Fintype ι] (c : ι → X.B.I.E) (v : ι → (VS D).V) :
    X.crd (∑ k, X.ιE (c k) • v k) = fun i => ∑ k, c k * X.crd (v k) i := by
  funext i
  simp [HidaSetting.crd, crdOf, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_mul]

theorem crd_injective (X : HidaSetting D) : Function.Injective X.crd := by
  intro v w h
  apply X.bas.repr.injective
  ext i
  have := congrFun h i
  simp only [HidaSetting.crd, crdOf] at this
  rw [X.ιE.symm.injective this]

theorem orth_mem_span_qFr : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    WittX X u wt → ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
    (VS D).hT (X.zu u) y = 0 → ∃ d : Fin (D.R.N 0) → D.host.E, Fintype.linearCombination D.host.E (qFr wt) d = y := by
  intro D X u wt hw y hef hz
  classical
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hzc, -, -⟩ := qFrame_basis_gram D X u wt hw
  have hcol : ∀ k i, Q i k = X.crd (famQ X u wt k) i := by
    rintro (j | a | a | ⟨⟩) i
    · simp [famQ, hq]
    · simp [famQ, he, HidaSetting.eR]
    · simp [famQ, hf, HidaSetting.fR]
    · simp [famQ, hzc, HidaSetting.zR]
  set c := Qi *ᵥ X.crd y with hc
  have hy : y = ∑ k, X.ιE (c k) • famQ X u wt k := by
    apply crd_injective X
    rw [crd_sum_smul]
    have : Q *ᵥ c = X.crd y := by rw [hc, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rw [← this]
    funext i
    simp only [Matrix.mulVec, dotProduct, hcol]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hy
  simp only [famQ, Sum.elim_inl, Sum.elim_inr, Fintype.univ_unit, Finset.sum_singleton] at hy
  have hqe : ∀ j b, (VS D).hT (X.eX b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inl b))
  have hqf : ∀ j b, (VS D).hT (X.fY b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inl b)))
  have hqz : ∀ j, (VS D).hT (X.zu u) (qFr wt j) = 0 := fun j =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inr ())))

  have c2 : ∀ b, X.ιE (c (Sum.inr (Sum.inr (Sum.inl b)))) = 0 := by
    intro b
    have h := (hef b).1
    rw [hy] at h
    simpa [map_add, map_sum, hqe, X.ee, X.ef, (X.zu_orth u b).1] using h
  have c1 : ∀ b, X.ιE (c (Sum.inr (Sum.inl b))) = 0 := by
    intro b
    have h := (hef b).2
    rw [hy] at h
    simpa [map_add, map_sum, hqf, X.ff, hT_fe, (X.zu_orth u b).2] using h
  have c3 : X.ιE (c (Sum.inr (Sum.inr (Sum.inr ())))) = 0 := by
    have h := hz
    rw [hy] at h
    simp [map_add, map_sum, hqz, hT_ze, hT_zf] at h
    rw [h.resolve_right (hT_zz_ne X u), map_zero]
  refine ⟨fun j => X.ιE (c (Sum.inl j)), ?_⟩
  rw [hy, Fintype.linearCombination_apply]
  simp [c1, c2, c3]

end GlobalTheory.St
end

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_hyperbolicFrame_anisotropic_mem_span_transported : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → (VS D).hT (X.zu u) y = 0 → ∃ d : Fin (D.R.N 0) → D.host.E, Fintype.linearCombination D.host.E (qFr wt) d = y := by
  atlas_forward_decl GlobalTheory.St.orth_mem_span_qFr
end

section
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.LocNot

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_of_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F)
    (ht : (1 : E) ⊗ₜ[F] t ∈ intV E v) : t ∈ v.adicCompletionIntegers F := by
  classical
  let ι : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F := Algebra.TensorProduct.includeRight
  letI : Algebra (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) :=
    (ι.toRingHom.comp (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
  let ιO : v.adicCompletion F →ₐ[v.adicCompletionIntegers F] E ⊗[F] v.adicCompletion F :=
    { ι.toRingHom with commutes' := fun _ => rfl }
  have hinj : Function.Injective ιO :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective
  have hle : intV E v ≤
      (integralClosure (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨e, he⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · obtain ⟨a, rfl⟩ := he
      obtain ⟨p, hp, hpe⟩ := RingOfIntegers.isIntegral_coe a
      refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      let g : E →+* E ⊗[F] v.adicCompletion F := Algebra.TensorProduct.includeLeftRingHom
      have hc : (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).comp
          (Int.castRingHom _) = g.comp (algebraMap ℤ E) := RingHom.ext_int _ _
      have h3 := congrArg g hpe
      rw [Polynomial.hom_eval₂, map_zero] at h3
      rw [hc]
      exact h3
    · exact isIntegral_algebraMap (x := (⟨c, hc⟩ : v.adicCompletionIntegers F))
  have hi : IsIntegral (v.adicCompletionIntegers F) t := (isIntegral_algHom_iff ιO hinj).1 (hle ht)
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact b.2

end GlobalTheory.St.G.LocNot

namespace GlobalTheory.St.G

theorem dual_not_loc_of_norm_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ (d : Fin n → E) (T : ℕ), 0 < T → d ∈ dualL cm.sig J L → Formalism.UG.hform (cm.sig : E →+* E) J d d - ((T : E))⁻¹ ∈ (algebraMap (𝓞 E) E).range → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL cm.sig J L), x ∉ loc v L := by
  intro F E _ _ _ _ _ _ cm n J L hL d T hT hd hdd v hv
  let x : Fin n → E ⊗[F] v.adicCompletion F := fun i => inclE (F := F) (v.adicCompletion F) (d i)
  refine ⟨x, Submodule.subset_span ⟨d, hd, rfl⟩, fun hx => ?_⟩
  have hLd : L ≤ dualL cm.sig J L := fun y hy => Submodule.subset_span (hL y hy)
  have hx' : x ∈ loc v (dualL cm.sig J L) := Submodule.span_mono (Set.image_mono hLd) hx
  have hxx := Dual.fwd cm.sig J (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring L x hx' x hx
  rw [Dual.hR_incl] at hxx
  obtain ⟨a, ha⟩ := hdd
  have h1 : inclE (F := F) (v.adicCompletion F) ((T : E)⁻¹) ∈ intV E v := by
    have he : Formalism.UG.hform (cm.sig : E →+* E) J d d = algebraMap (𝓞 E) E a + (T : E)⁻¹ := by
      rw [ha]; ring
    rw [he, map_add] at hxx
    have ha' : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a) ∈ intV E v :=
      Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)
    have := sub_mem hxx ha'
    rwa [add_sub_cancel_left] at this
  have h2 : inclE (F := F) (v.adicCompletion F) ((T : E)⁻¹) =
      (1 : E) ⊗ₜ[F] ((T : v.adicCompletion F)⁻¹) := by
    have e1 : ((T : E))⁻¹ = ((T : F))⁻¹ • (1 : E) := by
      rw [Algebra.smul_def, mul_one, map_inv₀, map_natCast]
    have e2 : ((T : v.adicCompletion F))⁻¹ = ((T : F))⁻¹ • (1 : v.adicCompletion F) := by
      rw [Algebra.smul_def, mul_one, map_inv₀, map_natCast]
    rw [e1, e2]
    show ((T : F)⁻¹ • (1 : E)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [TensorProduct.smul_tmul]
  rw [h2] at h1
  have h3 := LocNot.mem_of_tmul_mem v _ h1
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h3
  have hval : Valued.v (T : v.adicCompletion F) < 1 := by
    have hv1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (T : 𝓞 F)
    have hv2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (T : 𝓞 F)).2 hv
    rw [← hv1] at hv2
    convert hv2 using 2
    simp
  have hne : (T : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hT.ne')
  rw [map_inv₀] at h3
  have hpos : 0 < Valued.v (T : v.adicCompletion F) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne)
  have h4 : 1 ≤ Valued.v (T : v.adicCompletion F) := (inv_le_one₀ hpos).1 h3
  exact absurd hval (not_lt.2 h4)

end GlobalTheory.St.G
end
end

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_dual_vector_norm_inv_not_mem_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ (d : Fin n → E) (T : ℕ), 0 < T → d ∈ dualL cm.sig J L → Formalism.UG.hform (cm.sig : E →+* E) J d d - ((T : E))⁻¹ ∈ (algebraMap (𝓞 E) E).range → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL cm.sig J L), x ∉ loc v L := by
  atlas_forward_decl GlobalTheory.St.G.dual_not_loc_of_norm_inv
end

section
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem mlat_card (E : Type) [Field E] [NumberField E] (T : ℕ) :
    Nat.card (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)}) = T ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have h := Algebra.norm_algebraMap (S := 𝓞 E) (T : ℤ)
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at h
  rw [h, Int.natAbs_pow, Int.natAbs_natCast, NumberField.RingOfIntegers.rank]

end GlobalTheory.St.G

namespace GlobalTheory.St.G

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {wt : (VS D).V ≃ₗ[D.host.E] (VS D).V}

theorem mlat_T_ne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

theorem selfDual_lattice_hermitian_form_integral {x y : (VS D).V} (hx : x ∈ (VS D).L0) (hy : y ∈ (VS D).L0) :
    (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h := (VS D).baseLattice_isUnimodular
  unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at h
  have hy' : y ∈ Formalism.E.hdual (VS D).hT (VS D).L0 := by rw [h]; exact hy
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hy' x hx)
  exact ⟨a, by simpa using ha⟩

theorem mlat_Lb_le : X.Lb ≤ (VS D).L0 := by
  rw [X.Lam_split]; exact le_sup_left.trans' le_sup_right

theorem mlat_symm (x y : (VS D).V) : (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y) :=
  ((VS D).herm.eq x y).symm

theorem mlat_gram (hW : WittX X u wt) (i j : Fin (D.R.N 0)) :
    (VS D).hT (qFr wt i) (qFr wt j) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) i j := by
  rw [← hW.1]
  simp only [qFr, LinearEquiv.apply_symm_apply, xFr]
  rw [D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)]
  rfl

theorem mlat_perp (hW : WittX X u wt) (j : Fin (D.R.N 0)) :
    (∀ a, (VS D).hT (X.eX a) (qFr wt j) = 0 ∧ (VS D).hT (X.fY a) (qFr wt j) = 0) ∧
      (VS D).hT (X.zu u) (qFr wt j) = 0 := by
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← hW.1, hW.2.1, mlat_symm]; simp [qFr, xFr, (D.sp.hyp_orthX a _).1]
  · rw [← hW.1, hW.2.2.1, mlat_symm]; simp [qFr, xFr, (D.sp.hyp_orthX a _).2]
  · rw [← hW.1, hW.2.2.2, mlat_symm]
    simp only [qFr, LinearEquiv.apply_symm_apply, xFr, D7.zmOf, map_smul, map_smulₛₗ]
    simp [D.sp.zm_orth]

end GlobalTheory.St.G

namespace GlobalTheory.St.G

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {wt : (VS D).V ≃ₗ[D.host.E] (VS D).V}

theorem mlat_hT_lc (hW : WittX X u wt) (d d' : Fin (D.R.N 0) → D.host.E) :
    (VS D).hT (Fintype.linearCombination D.host.E (qFr wt) d) (Fintype.linearCombination D.host.E (qFr wt) d') =
      Formalism.UG.hform (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) d d' := by
  simp only [Fintype.linearCombination_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, mlat_gram hW, Formalism.UG.hform, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply]
  have : ((Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)) (d i) = starRingEnd D.host.E (d i) := rfl
  rw [this]; ring

theorem mlat_lc_perp (hW : WittX X u wt) (d : Fin (D.R.N 0) → D.host.E) :
    (∀ a, (VS D).hT (X.eX a) (Fintype.linearCombination D.host.E (qFr wt) d) = 0 ∧
      (VS D).hT (X.fY a) (Fintype.linearCombination D.host.E (qFr wt) d) = 0) ∧
      (VS D).hT (X.zu u) (Fintype.linearCombination D.host.E (qFr wt) d) = 0 := by
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, (mlat_perp hW _).2, ((mlat_perp hW _).1 _).1,
    ((mlat_perp hW _).1 _).2, smul_zero, Finset.sum_const_zero, and_self, implies_true]

theorem mlat_mem_dualL {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (y : Fin n → D.host.E) :
    y ∈ dualL (Formalism.L2.Forms.sigD D) J L ↔ y ∈ dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J L := by
  refine ⟨fun hy => ?_, fun hy => Submodule.subset_span hy⟩
  induction hy using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro x _; exact ⟨0, by simp [Formalism.UG.hform]⟩
  | add a b _ _ ha hb =>
    intro x hx
    obtain ⟨p, hp⟩ := ha x hx
    obtain ⟨q, hq⟩ := hb x hx
    refine ⟨p + q, ?_⟩
    simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hp hq ⊢
    rw [map_add, hp, hq]
  | smul c a _ ha =>
    intro x hx
    obtain ⟨p, hp⟩ := ha x hx
    refine ⟨c * p, ?_⟩
    simp only [Formalism.UG.hform, Pi.smul_apply] at hp ⊢
    rw [map_mul, hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]; ring

theorem mlat_inj (hW : WittX X u wt) : Function.Injective (Fintype.linearCombination D.host.E (qFr wt)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro d hd
  have hdet := (GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts D u).2.2.2.2.2.2
  refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
  funext i
  have h := mlat_hT_lc hW (Pi.single i 1) d
  rw [hd, map_zero] at h
  simpa [Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct] using h.symm

end GlobalTheory.St.G

namespace GlobalTheory.St.G

set_option maxHeartbeats 2000000 in

theorem mlat_main (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) : TLat (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (Mq wt) ∧ ∃ x₀ ∈ X.Lb, (VS D).hT (X.zu u) x₀ = 1 ∧ ∃ d ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), Fintype.linearCombination D.host.E (qFr wt) d = x₀ + (((D.mem u).A.T : D.host.E))⁻¹ • X.zu u ∧ ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), ∃ a : 𝓞 D.host.E, y - (a : D.host.E) • d ∈ Mq wt := by
  obtain ⟨hLb, ⟨x₀, hx₀Lb, hx₀z⟩, -⟩ := GlobalTheory.T.middleLattice_selfDual_anisotropic_pairing D X u
  have hWc := GlobalTheory.T.orthogonal_hyperbolicFrame_anisotropic_mem_span_transported D X u wt hW
  set T : ℕ := (D.mem u).A.T with hTdef
  set φ := Fintype.linearCombination D.host.E (qFr wt) with hφ
  set h := (VS D).hT with hh
  set z := X.zu u with hz
  have hT0 : (T : D.host.E) ≠ 0 := mlat_T_ne
  have hzz : h z z = -(T : D.host.E) := X.zu_norm u
  have hzLb : z ∈ X.Lb := X.zu_Lb u
  have hx0L0 := mlat_Lb_le hx₀Lb
  have hzL0 := mlat_Lb_le hzLb
  have hx₀z' : h x₀ z = 1 := by rw [hh, mlat_symm, ← hh, hx₀z, map_one]
  have hTstar : starRingEnd D.host.E ((T : D.host.E)⁻¹) = (T : D.host.E)⁻¹ := by simp
  set w₀ := x₀ + (T : D.host.E)⁻¹ • z with hw₀
  have hw0e : ∀ a, h (X.eX a) w₀ = 0 ∧ h (X.fY a) w₀ = 0 := by
    intro a
    simp [w₀, (X.Lb_perp _ hx₀Lb a).1, (X.Lb_perp _ hx₀Lb a).2, (X.zu_orth u a).1, (X.zu_orth u a).2, h, z]
  have hw0z : h z w₀ = 0 := by
    simp only [w₀, map_add, map_smul, hx₀z, hzz, smul_eq_mul]
    field_simp; ring
  obtain ⟨d, hd⟩ := hWc w₀ hw0e hw0z
  have hmem : ∀ x, x ∈ Mq wt ↔ φ x ∈ (VS D).L0 := fun x => Iff.rfl
  have hmemLb : ∀ x, x ∈ Mq wt ↔ φ x ∈ X.Lb := fun x => (hmem x).trans ((hLb (φ x) (mlat_lc_perp hW x).1).1)
  have hdual : ∀ y, y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt) ↔
      ∀ x ∈ Mq wt, h (φ x) (φ y) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    rw [mlat_mem_dualL]
    simp only [dualSet, Set.mem_setOf_eq, hh, hφ, mlat_hT_lc hW]

  have hperp0 : ∀ x, h (φ x) z = 0 := fun x => by rw [hh, mlat_symm, ← hh, (mlat_lc_perp hW x).2, map_zero]
  have hsmulLb : ∀ (c : D.host.E), c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range → ∀ v ∈ X.Lb, c • v ∈ X.Lb := by
    rintro c ⟨c', rfl⟩ v hv
    rw [algebraMap_smul]; exact X.Lb.smul_mem c' hv
  have hsmulM : ∀ (c : D.host.E), c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range → ∀ v ∈ Mq wt, c • v ∈ Mq wt := by
    rintro c ⟨c', rfl⟩ v hv
    rw [algebraMap_smul]; exact (Mq wt).smul_mem c' hv

  have hC : ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt),
      (T : D.host.E) * h x₀ (φ y) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
        y - ((T : D.host.E) * h x₀ (φ y)) • d ∈ Mq wt := by
    intro y hy
    have hYp := mlat_lc_perp hW y
    set Y := φ y with hY
    set Y' := Y - h x₀ Y • z with hY'
    have hY'perp : ∀ a, h (X.eX a) Y' = 0 ∧ h (X.fY a) Y' = 0 := by
      intro a
      simp [Y', (hYp.1 a).1, (hYp.1 a).2, (X.zu_orth u a).1, (X.zu_orth u a).2, h, z]
    have hY'Lb : Y' ∈ X.Lb := by
      refine (hLb Y' hY'perp).2 fun x hx => ?_
      set c := h z x with hc
      have hcint : c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := selfDual_lattice_hermitian_form_integral hzL0 (mlat_Lb_le hx)
      set m := x - c • x₀ with hm
      have hmLb : m ∈ X.Lb := X.Lb.sub_mem hx (hsmulLb c hcint x₀ hx₀Lb)
      have hmz : h z m = 0 := by simp [m, map_sub, map_smul, hx₀z, c]
      obtain ⟨xm, hxm⟩ := hWc m (X.Lb_perp m hmLb) hmz
      have hxmM : xm ∈ Mq wt := (hmemLb xm).2 (hxm ▸ hmLb)
      have h1 : h m Y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        rw [← hxm]; exact (hdual y).1 hy xm hxmM
      have hmz' : h m z = 0 := by rw [hh, mlat_symm, ← hh, hmz, map_zero]
      have hx' : x = m + c • x₀ := by simp [m]
      rw [hx']
      have e : h (m + c • x₀) Y' = h m Y := by
        simp only [Y', map_add, map_smulₛₗ, map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hmz', hx₀z', smul_eq_mul, RingHom.id_apply]
        ring
      rw [e]; exact h1
    have hYz : h z Y = 0 := hYp.2
    have hb : h z Y' = (T : D.host.E) * h x₀ Y := by
      simp only [Y', map_sub, map_smul, hYz, hzz, smul_eq_mul]; ring
    have hbint : (T : D.host.E) * h x₀ Y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
      hb ▸ selfDual_lattice_hermitian_form_integral hzL0 (mlat_Lb_le hY'Lb)
    refine ⟨hbint, (hmemLb _).2 ?_⟩
    have hbT : (T : D.host.E) * h x₀ Y * (T : D.host.E)⁻¹ = h x₀ Y := by field_simp
    have e : φ (y - ((T : D.host.E) * h x₀ Y) • d) = Y' - ((T : D.host.E) * h x₀ Y) • x₀ := by
      rw [map_sub, map_smul, hd, ← hY]
      simp only [Y', w₀, smul_add, smul_smul, hbT]
      abel
    rw [e]
    exact X.Lb.sub_mem hY'Lb (hsmulLb _ hbint x₀ hx₀Lb)
  have hdD : d ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt) := by
    refine (hdual d).2 fun x hx => ?_
    rw [hd]
    simp only [w₀, map_add, map_smul, hperp0, smul_zero, add_zero]
    exact selfDual_lattice_hermitian_form_integral ((hmem x).1 hx) hx0L0
  have hTd : (T : D.host.E) • d ∈ Mq wt := by
    refine (hmem _).2 ?_
    rw [map_smul, hd]
    simp only [w₀, smul_add, smul_smul, mul_inv_cancel₀ hT0, one_smul]
    refine (VS D).L0.add_mem ?_ hzL0
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx0L0 T
  have hw0w0 : h w₀ w₀ = h x₀ x₀ + (T : D.host.E)⁻¹ := by
    simp only [w₀, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, hx₀z, hx₀z', hzz,
      hTstar, smul_eq_mul]
    field_simp; ring

  have hint : ∀ x ∈ Mq wt, x ∈ dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt) := by
    intro x hx x' hx'
    rw [← mlat_hT_lc hW]
    exact selfDual_lattice_hermitian_form_integral ((hmem _).1 hx') ((hmem _).1 hx)
  have hnorm : Formalism.UG.hform (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) d d -
      ((T : D.host.E))⁻¹ ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    rw [← mlat_hT_lc hW, hd, ← hh, hw0w0, add_sub_cancel_right]
    exact selfDual_lattice_hermitian_form_integral hx0L0 hx0L0
  have hLat : IsLat (Mq wt) := by
    refine ⟨?_, ?_⟩
    · haveI : IsNoetherian (𝓞 D.host.E) (VS D).L0 := isNoetherian_of_fg_of_noetherian _ (VS D).standardTuple_isLattice.fg
      let f : Mq wt →ₗ[𝓞 D.host.E] (VS D).L0 :=
        LinearMap.codRestrict (VS D).L0 ((φ.restrictScalars (𝓞 D.host.E)).comp (Mq wt).subtype) (fun x => x.2)
      refine Module.Finite.of_injective f ?_
      intro a b hab
      apply Subtype.ext
      apply mlat_inj hW
      exact congrArg Subtype.val hab
    · rw [eq_top_iff]
      intro y _
      have hspan := (VS D).standardTuple_isLattice.span_eq_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 D.host.E)) D.host.E
        ((VS D).L0 : Set (VS D).V) (φ y) (by rw [hspan]; trivial)
      rw [Submodule.span_eq, Submonoid.smul_def] at ht
      have htM : ((t : 𝓞 D.host.E)) • y ∈ Mq wt := by
        refine (hmem _).2 ?_
        rw [← algebraMap_smul D.host.E (t : 𝓞 D.host.E) y, map_smul, algebraMap_smul]
        exact ht
      have ht0 : algebraMap (𝓞 D.host.E) D.host.E t ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).2 (nonZeroDivisors.ne_zero t.2)
      have e : y = (algebraMap (𝓞 D.host.E) D.host.E t)⁻¹ • ((t : 𝓞 D.host.E) • y) := by
        rw [← algebraMap_smul D.host.E (t : 𝓞 D.host.E) y, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span htM)
  have hkill : ∀ y ∈ dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), (T : D.host.E) • y ∈ Mq wt := by
    intro y hy
    obtain ⟨hb, hyM⟩ := hC y (Submodule.subset_span hy)
    have e : (T : D.host.E) • y = (T : D.host.E) • (y - ((T : D.host.E) * h x₀ (φ y)) • d) +
        ((T : D.host.E) * h x₀ (φ y)) • ((T : D.host.E) • d) := by
      rw [smul_sub, smul_smul, smul_smul, mul_comm]; abel
    rw [e]
    refine (Mq wt).add_mem ?_ (hsmulM _ hb _ hTd)
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hyM T

  have hidx : (Mq wt).toAddSubgroup.relIndex
      (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)).toAddSubgroup = T ^ (2 * D.R.f) := by
    have key : ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt),
        ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = (T : D.host.E) * h x₀ (φ y) :=
      fun y hy => (hC y hy).1
    choose B hB using key
    have hinjO := IsFractionRing.injective (𝓞 D.host.E) D.host.E
    let ψ : (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)).toAddSubgroup →+
        (𝓞 D.host.E ⧸ Ideal.span {((T : ℕ) : 𝓞 D.host.E)}) :=
      AddMonoidHom.mk' (fun y => Ideal.Quotient.mk _ (B y.1 y.2)) (by
        intro a b
        rw [← map_add]
        congr 1
        apply hinjO
        simp only [hB, map_add, AddSubgroup.coe_add, mul_add])
    have hψ : ∀ y, ψ y = Ideal.Quotient.mk _ (B y.1 y.2) := fun y => rfl
    have hsurj : Function.Surjective ψ := by
      intro q
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      have had := Submodule.smul_mem (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)) a hdD
      obtain ⟨e, he⟩ : h x₀ x₀ ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := selfDual_lattice_hermitian_form_integral hx0L0 hx0L0
      refine ⟨⟨_, had⟩, ?_⟩
      rw [hψ, Ideal.Quotient.eq, Ideal.mem_span_singleton']
      refine ⟨a * e, hinjO ?_⟩
      have hBa := hB (a • d) had
      have hφa : φ (a • d) = algebraMap (𝓞 D.host.E) D.host.E a • w₀ := by
        rw [← algebraMap_smul D.host.E a d, map_smul, hd]
      rw [hφa] at hBa
      show algebraMap (𝓞 D.host.E) D.host.E (a * e * ((T : ℕ) : 𝓞 D.host.E)) =
        algebraMap (𝓞 D.host.E) D.host.E (B (a • d) had - a)
      rw [map_sub, hBa, map_mul, map_mul, map_natCast]
      simp only [hw₀, map_add, map_smul, smul_eq_mul, hx₀z', ← he]
      field_simp
      ring
    have hker : ψ.ker = (Mq wt).toAddSubgroup.addSubgroupOf
        (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)).toAddSubgroup := by
      ext ⟨y, hy⟩
      rw [AddMonoidHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton',
        AddSubgroup.mem_addSubgroupOf]
      simp only [Submodule.mem_toAddSubgroup]
      constructor
      · rintro ⟨c, hc⟩
        have hc' : (T : D.host.E) * h x₀ (φ y) = algebraMap (𝓞 D.host.E) D.host.E c * (T : D.host.E) := by
          rw [← hB y hy, ← hc, map_mul, map_natCast]
        have e : y = (y - ((T : D.host.E) * h x₀ (φ y)) • d) + algebraMap (𝓞 D.host.E) D.host.E c • ((T : D.host.E) • d) := by
          rw [smul_smul, ← hc']; abel
        rw [e]
        exact (Mq wt).add_mem (hC y hy).2 (hsmulM _ ⟨c, rfl⟩ _ hTd)
      · intro hyM
        obtain ⟨c, hc⟩ := selfDual_lattice_hermitian_form_integral hx0L0 ((hmem y).1 hyM)
        refine ⟨c, hinjO ?_⟩
        rw [map_mul, hc, hB y hy, map_natCast, mul_comm]
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top, mlat_card,
      (GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts D u).2.2.2.1]
  refine ⟨⟨hLat, hint, hkill, hidx, fun v hv => ?_⟩, x₀, hx₀Lb, hx₀z, d, hdD, hd, fun y hy => ?_⟩
  · exact GlobalTheory.T.hermitian_dual_vector_norm_inv_not_mem_local D.host.F D.host.E D.sp.cm (D.R.N 0) _ (Mq wt) hint d T (D.mem u).A.T_prime.pos hdD hnorm v hv
  · obtain ⟨⟨b, hb⟩, hyM⟩ := hC y hy
    refine ⟨b, ?_⟩
    have : ((b : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b := rfl
    rw [this, hb]
    exact hyM

end GlobalTheory.St.G
end

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → TLat (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (Mq wt) ∧ ∃ x₀ ∈ X.Lb, (VS D).hT (X.zu u) x₀ = 1 ∧ ∃ d ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), Fintype.linearCombination D.host.E (qFr wt) d = x₀ + (((D.mem u).A.T : D.host.E))⁻¹ • X.zu u ∧ ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), ∃ a : 𝓞 D.host.E, y - (a : D.host.E) • d ∈ Mq wt := by
  atlas_forward_decl GlobalTheory.St.G.mlat_main
end
