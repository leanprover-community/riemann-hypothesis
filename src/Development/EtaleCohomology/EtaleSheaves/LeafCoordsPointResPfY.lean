import Development.EtaleCohomology.EtaleSheaves.LeafChartRingPf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero

section
noncomputable section

namespace LateralTheory.E.LeafCoordsPf

open LateralTheory.E.LeafChartRingPf
open scoped Pointwise

theorem linIndep_of_span {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
    (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B) (g : B) {ι : Type} [Fintype ι]
    (v : ι → Ω[Localization.Away g⁄A]) (hcard : Fintype.card ι = n)
    (hsp : Submodule.span (Localization.Away g) (Set.range v) = ⊤) :
    LinearIndependent (Localization.Away g) v := by
  cases subsingleton_or_nontrivial (Localization.Away g) with
  | inl h => exact linearIndependent_of_subsingleton
  | inr h =>
    have h0 : Algebra.IsStandardSmoothOfRelativeDimension 0 B (Localization.Away g) :=
      Algebra.IsStandardSmoothOfRelativeDimension.localization_away g
    have h1 : Algebra.IsStandardSmoothOfRelativeDimension (0 + n) A (Localization.Away g) :=
      Algebra.IsStandardSmoothOfRelativeDimension.trans n 0 A B (Localization.Away g)
    rw [zero_add] at h1
    have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := A) (S := Localization.Away g) n
    have : Module.Free (Localization.Away g) Ω[Localization.Away g⁄A] := by
      have := h1.isStandardSmooth
      infer_instance
    have hf : Module.finrank (Localization.Away g) Ω[Localization.Away g⁄A] = n :=
      Module.finrank_eq_of_rank_eq hr
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hsp.ge (hcard.trans hf.symm)

theorem conormal_retraction {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n m : ℕ)
    (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B)
    (hBI : Algebra.IsStandardSmoothOfRelativeDimension m A (B ⧸ I)) :
    ∃ l, l ∘ₗ (KaehlerDifferential.kerCotangentToTensor A B (B ⧸ I)) = LinearMap.id := by
  have := hB.isStandardSmooth
  have := hBI.isStandardSmooth
  exact (Algebra.FormallySmooth.iff_split_injection (R := A) (P := B) (A := B ⧸ I)
    Ideal.Quotient.mk_surjective).mp inferInstance

def dyt {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d e : ℕ} (y : Fin e → B) (t : Fin d → B) :
    Fin e ⊕ Fin d → Ω[B⁄A] :=
  Sum.elim (fun k => KaehlerDifferential.D A B (y k)) (fun j => KaehlerDifferential.D A B (t j))

theorem ideal_fg {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n m : ℕ)
    (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B)
    (hBI : Algebra.IsStandardSmoothOfRelativeDimension m A (B ⧸ I)) : I.FG := by
  have := hB.isStandardSmooth
  have := hBI.isStandardSmooth
  have h := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ A I)
    (Ideal.Quotient.mkₐ_surjective A I)
  simpa using h

theorem spread (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B)
    (P : Ideal B) (t : Fin d → B) (y : Fin e → B) (h : B) (hh : h ∉ P)
    (ht : ∀ j, t j ∈ I) (hI : h • I ≤ Ideal.span (Set.range t))
    (hΩ : h • (⊤ : Submodule B Ω[B⁄A]) ≤ Submodule.span B (Set.range (dyt (A := A) y t))) :
    ∃ g ∉ P,
    I.map (algebraMap B (Localization.Away g)) = Ideal.span (Set.range fun j => algebraMap B (Localization.Away g) (t j)) ∧
    Submodule.span (Localization.Away g) (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j))))) = ⊤ := by
  have hu : IsUnit (algebraMap B (Localization.Away h) h) := IsLocalization.Away.algebraMap_isUnit h
  refine ⟨h, hh, ?_, ?_⟩
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : h * x ∈ Ideal.span (Set.range t) := hI (Submodule.smul_mem_pointwise_smul x h I hx)
      have h2 := Ideal.mem_map_of_mem (algebraMap B (Localization.Away h)) h1
      rw [Ideal.map_span, ← Set.range_comp, map_mul] at h2
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h2
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (ht j)
  · set T := Localization.Away h
    set S := Submodule.span T (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A T (algebraMap B T (y k)))
      (fun j => KaehlerDifferential.D A T (algebraMap B T (t j)))))
    let f := KaehlerDifferential.map A A B T
    have hspan : Submodule.span B (Set.range (dyt (A := A) y t)) ≤ (S.restrictScalars B).comap f := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rcases i with k | j
      · exact Submodule.subset_span ⟨Sum.inl k, by simp [dyt, f, KaehlerDifferential.map_D]⟩
      · exact Submodule.subset_span ⟨Sum.inr j, by simp [dyt, f, KaehlerDifferential.map_D]⟩
    rw [eq_top_iff]
    intro ω _
    obtain ⟨⟨m, u⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers h) f ω
    have huu : IsUnit (algebraMap B T (u : B)) := IsLocalization.map_units T u
    have hm : f (h • m) ∈ S := hspan (hΩ (Submodule.smul_mem_pointwise_smul m h ⊤ trivial))
    have key : (algebraMap B T h * algebraMap B T (u : B)) • IsLocalizedModule.mk' f m u = f (h • m) := by
      rw [mul_smul, algebraMap_smul, algebraMap_smul, LinearMap.map_smul]
      congr 1
      exact IsLocalizedModule.mk'_cancel' f m u
    rw [← key] at hm
    exact (Submodule.smul_mem_iff_of_isUnit S (hu.mul huu)).mp hm

def LeafNakH : Prop := ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B), P.IsPrime →
  ∀ (N N' : Submodule B M), N'.FG → ∀ h ∉ P, h • N' ≤ N ⊔ P • N' → ∃ u ∉ P, u • N' ≤ N

def LeafCoordsPoint : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ h ∉ P, ∃ (t : Fin d → B) (y : Fin e → B),
    (∀ j, t j ∈ I) ∧ h • I ≤ Ideal.span (Set.range t) ⊔ P • I ∧
    h • (⊤ : Submodule B Ω[B⁄A]) ≤ Submodule.span B (Set.range (dyt (A := A) y t)) ⊔ P • ⊤

theorem LeafCoords_of (hPt : LeafCoordsPoint) (hN : LeafNakH) : LeafCoords := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨h, hh, t, y, ht, hI, hΩ⟩ := hPt d e A B I hB hBI P hP hIP
  obtain ⟨u1, hu1, h1⟩ := hN B B P hP _ I (ideal_fg I _ _ hB hBI) h hh hI
  have := hB.isStandardSmooth
  obtain ⟨u2, hu2, h2⟩ := hN B Ω[B⁄A] P hP _ ⊤ Module.Finite.fg_top h hh hΩ
  have hu : u1 * u2 ∉ P := fun H => (hP.mem_or_mem H).elim hu1 hu2
  obtain ⟨g, hg, hIg, hsp⟩ := spread d e A B I P t y (u1 * u2) hu ht
    (by
      rintro _ ⟨x, hx, rfl⟩
      have : u1 * x ∈ Ideal.span (Set.range t) := h1 (Submodule.smul_mem_pointwise_smul x u1 I hx)
      have := Ideal.mul_mem_left _ u2 this
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this)
    (by
      rintro _ ⟨x, -, rfl⟩
      have : u2 • x ∈ Submodule.span B (Set.range (dyt (A := A) y t)) :=
        h2 (Submodule.smul_mem_pointwise_smul x u2 ⊤ trivial)
      show (u1 * u2) • x ∈ _
      rw [mul_smul]
      exact Submodule.smul_mem _ u1 this)
  exact ⟨g, hg, t, y, hIg, linIndep_of_span (e + d) hB g _ (by simp) hsp, hsp⟩

end LateralTheory.E.LeafCoordsPf
end
end

section
noncomputable section

namespace LateralTheory.E.LeafCoordsPf.NakH

open scoped Pointwise
open Polynomial

theorem eval_notMem {B : Type} [CommRing B] {P : Ideal B} (hP : P.IsPrime) (p : B[X]) (hm : p.Monic)
    (hc : ∀ k, p.coeff k ∈ P ^ (p.natDegree - k)) {h : B} (hh : h ∉ P) : p.eval h ∉ P := by
  intro H
  have hsum : ∑ i ∈ Finset.range p.natDegree, p.coeff i * h ^ i ∈ P := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    have hi' : p.natDegree - i ≠ 0 := by
      have := Finset.mem_range.mp hi
      omega
    exact Ideal.pow_le_self hi' (hc i)
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, one_mul] at H
  have : h ^ p.natDegree ∈ P := by
    have := P.sub_mem H hsum
    simpa using this
  exact hh (hP.mem_of_pow_mem _ this)

theorem nakH : LeafNakH := by
  intro B M _ _ _ P hP N N' hfg h hh hle
  have : Module.Finite B N' := Module.Finite.iff_fg.mpr hfg
  let Q := N' ⧸ N.comap N'.subtype
  let f : Module.End B Q := algebraMap B (Module.End B Q) h
  have hr : LinearMap.range f ≤ P • ⊤ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨⟨n, hn⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    have hhn : h • n ∈ N ⊔ P • N' := hle (Submodule.smul_mem_pointwise_smul n h N' hn)
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hhn
    have hb' : b ∈ (P • (⊤ : Submodule B N')).map N'.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
      exact hb
    obtain ⟨b', hb'1, hb'2⟩ := hb'
    have heq : f ((N.comap N'.subtype).mkQ ⟨n, hn⟩) = (N.comap N'.subtype).mkQ b' := by
      simp only [f, Module.algebraMap_end_apply, Submodule.mkQ_apply]
      show (Submodule.Quotient.mk (h • (⟨n, hn⟩ : N')) : N' ⧸ N.comap N'.subtype) = Submodule.Quotient.mk b'
      rw [Submodule.Quotient.eq, Submodule.mem_comap]
      simp only [Submodule.subtype_apply, SetLike.val_smul, Submodule.coe_sub, hb'2]
      convert ha using 1
      rw [← hab]
      have hb3 : (b' : M) = b := hb'2
      rw [hb3]
      abel
    rw [heq]
    have : (P • (⊤ : Submodule B N')).map (N.comap N'.subtype).mkQ ≤ P • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨b', hb'1, rfl⟩
  obtain ⟨p, hm, -, hc, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero B f P hr
  refine ⟨p.eval h, eval_notMem hP p hm hc hh, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := LinearMap.congr_fun hp (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, Module.algebraMap_end_apply, LinearMap.zero_apply,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  simpa using this

theorem LeafCoords_of_point (hPt : LeafCoordsPoint) : LateralTheory.E.LeafChartRingPf.LeafCoords :=
  LeafCoords_of hPt nakH

end LateralTheory.E.LeafCoordsPf.NakH
end
end

section
noncomputable section

namespace LateralTheory.E.LeafCoordsPointPf

open LateralTheory.E.LeafCoordsPf
open scoped Pointwise

theorem clear {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B) (hP : P.IsPrime)
    (L N : Submodule B M) (hL : L.FG) (H : ∀ x ∈ L, ∃ s ∉ P, s • x ∈ N) :
    ∃ h ∉ P, ∀ x ∈ L, h • x ∈ N := by
  classical
  obtain ⟨S, rfl⟩ := hL
  have key : ∀ T : Finset M, T ⊆ S → ∃ h ∉ P, ∀ g ∈ T, h • g ∈ N := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
    | insert a T ha ih =>
      intro hT
      obtain ⟨h, hh, hg⟩ := ih (fun x hx => hT (Finset.mem_insert_of_mem hx))
      obtain ⟨s, hs, hsa⟩ := H a (Submodule.subset_span (hT (Finset.mem_insert_self a T)))
      refine ⟨s * h, fun H' => (hP.mem_or_mem H').elim hs hh, ?_⟩
      intro g hg'
      rcases Finset.mem_insert.mp hg' with rfl | hg'
      · rw [mul_comm, mul_smul]; exact N.smul_mem h hsa
      · rw [mul_smul]; exact N.smul_mem s (hg g hg')
  obtain ⟨h, hh, hg⟩ := key S subset_rfl
  refine ⟨h, hh, fun x hx => ?_⟩
  have : Submodule.span B (S : Set M) ≤ N.comap (h • LinearMap.id) :=
    Submodule.span_le.mpr fun g hgS => by simpa using hg g hgS
  simpa using this hx

def LeafCoordsPointLoc : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ (t : Fin d → B) (y : Fin e → B),
    (∀ j, t j ∈ I) ∧ (∀ x ∈ I, ∃ s ∉ P, s • x ∈ Ideal.span (Set.range t) ⊔ P • I) ∧
    (∀ ω : Ω[B⁄A], ∃ s ∉ P, s • ω ∈ Submodule.span B (Set.range (dyt (A := A) y t)) ⊔ P • ⊤)

theorem LeafCoordsPoint_of (hLoc : LeafCoordsPointLoc) : LeafCoordsPoint := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨t, y, ht, hI, hΩ⟩ := hLoc d e A B I hB hBI P hP hIP
  obtain ⟨h1, hh1, h1I⟩ := clear P hP I _ (ideal_fg I _ _ hB hBI) hI
  have := hB.isStandardSmooth
  obtain ⟨h2, hh2, h2Ω⟩ := clear P hP ⊤ _ Module.Finite.fg_top (fun ω _ => hΩ ω)
  refine ⟨h1 * h2, fun H => (hP.mem_or_mem H).elim hh1 hh2, t, y, ht, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    show (h1 * h2) • x ∈ _
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem _ h2 (h1I x hx)
  · rintro _ ⟨x, -, rfl⟩
    show (h1 * h2) • x ∈ _
    rw [mul_smul]
    exact Submodule.smul_mem _ h1 (h2Ω x trivial)

end LateralTheory.E.LeafCoordsPointPf
end
end

section
noncomputable section

namespace LateralTheory.E.LeafCoordsPointPf

open LateralTheory.E.LeafCoordsPf
open scoped Pointwise TensorProduct

theorem exists_smul_mem_of_span {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (P : Ideal B) [P.IsPrime] (g : ι → M)
    (hg : Submodule.span P.ResidueField (Set.range fun i => (1 : P.ResidueField) ⊗ₜ[B] g i) = ⊤) (m : M) :
    ∃ s ∉ P, s • m ∈ Submodule.span B (Set.range g) := by
  set N := Submodule.span B (Set.range g)
  let f := LinearMap.baseChange P.ResidueField N.mkQ
  have hf : Function.Surjective f := LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective N)
  have hr : LinearMap.range f = ⊥ := by
    rw [LinearMap.range_eq_map, ← hg, Submodule.map_span, Submodule.span_eq_bot]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have : g i ∈ N := Submodule.subset_span (Set.mem_range_self i)
    simp [f, (Submodule.Quotient.mk_eq_zero N).mpr this]
  have : Subsingleton (P.ResidueField ⊗[B] (M ⧸ N)) := by
    have h0 : ∀ z : P.ResidueField ⊗[B] (M ⧸ N), z = 0 := fun z => by
      obtain ⟨w, rfl⟩ := hf z
      have : f w ∈ LinearMap.range f := ⟨w, rfl⟩
      rw [hr] at this
      exact this
    exact ⟨fun a b => by rw [h0 a, h0 b]⟩
  obtain ⟨u, hu, hum⟩ := GlobalTheory.SS.DefectZero.exists_smul_eq_zero B P.ResidueField (M ⧸ N) (N.mkQ m)
  refine ⟨u, fun H => hu (Ideal.algebraMap_residueField_eq_zero.mpr H), ?_⟩
  have : (Submodule.Quotient.mk (u • m) : M ⧸ N) = 0 := by rw [Submodule.Quotient.mk_smul]; exact hum
  exact (Submodule.Quotient.mk_eq_zero N).mp this

def LeafCoordsPointRes : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → ∃ (t : Fin d → I) (y : Fin e → B),
    Submodule.span P.ResidueField (Set.range fun j => (1 : P.ResidueField) ⊗ₜ[B] t j) = ⊤ ∧
    Submodule.span P.ResidueField
      (Set.range fun i => (1 : P.ResidueField) ⊗ₜ[B] dyt (A := A) y (fun j => (t j : B)) i) = ⊤

theorem LeafCoordsPointLoc_of (hR : LeafCoordsPointRes) : LeafCoordsPointLoc := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨t, y, hI, hΩ⟩ := hR d e A B I hB hBI P hIP
  have hfg := ideal_fg I _ _ hB hBI
  have : Module.Finite B I := Module.Finite.iff_fg.mpr hfg
  have := hB.isStandardSmooth
  refine ⟨fun j => t j, y, fun j => (t j).2, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hsm⟩ := exists_smul_mem_of_span P t hI ⟨x, hx⟩
    refine ⟨s, hs, Submodule.mem_sup_left ?_⟩
    have := Submodule.mem_map_of_mem (f := I.subtype) hsm
    rw [Submodule.map_span, ← Set.range_comp] at this
    simpa [Function.comp_def] using this
  · intro ω
    obtain ⟨s, hs, hsm⟩ := exists_smul_mem_of_span P _ hΩ ω
    exact ⟨s, hs, Submodule.mem_sup_left hsm⟩

theorem LeafCoordsPoint_of_res (hR : LeafCoordsPointRes) : LeafCoordsPoint :=
  LeafCoordsPoint_of (LeafCoordsPointLoc_of hR)

end LateralTheory.E.LeafCoordsPointPf
end
end

section
noncomputable section

namespace LateralTheory.E.LeafCoordsPointResPf

open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

def LeafResT : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → ∃ (t : Fin d → I),
    Submodule.span P.ResidueField (Set.range fun j => (1 : P.ResidueField) ⊗ₜ[B] t j) = ⊤

def LeafResY : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → ∀ (t : Fin d → I),
    Submodule.span P.ResidueField (Set.range fun j => (1 : P.ResidueField) ⊗ₜ[B] t j) = ⊤ →
    ∃ (y : Fin e → B), Submodule.span P.ResidueField
      (Set.range fun i => (1 : P.ResidueField) ⊗ₜ[B] dyt (A := A) y (fun j => (t j : B)) i) = ⊤

theorem LeafCoordsPointRes_of (hT : LeafResT) (hY : LeafResY) : LeafCoordsPointRes := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  obtain ⟨t, ht⟩ := hT d e A B I hB hBI P hIP
  obtain ⟨y, hy⟩ := hY d e A B I hB hBI P hIP t ht
  exact ⟨t, y, ht, hy⟩

theorem pick {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (d : ℕ)
    (g : ι → V) (i0 : ι) (hs : Submodule.span K (Set.range g) = ⊤)
    (hd : Module.finrank K V ≤ d) : ∃ f : Fin d → ι, Submodule.span K (Set.range (g ∘ f)) = ⊤ := by
  classical
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent K (Set.range g)
  rw [hs] at hsp
  let bb : Module.Basis b K V := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hsp.ge)
  have : Finite b := Module.Finite.finite_basis bb
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b ≤ d := (Module.finrank_eq_card_basis bb).symm ▸ hd
  let e := Fintype.equivFin b
  have hpre : ∀ v : b, ∃ i, g i = v := fun v => hb v.2
  let f : Fin d → ι := fun j => if h : j.val < Fintype.card b then Classical.choose (hpre (e.symm ⟨j, h⟩)) else i0
  refine ⟨f, eq_top_iff.mpr ?_⟩
  rw [← hsp]
  apply Submodule.span_le.mpr
  intro v hv
  apply Submodule.subset_span
  refine ⟨⟨(e ⟨v, hv⟩).val, lt_of_lt_of_le (e ⟨v, hv⟩).2 hcard⟩, ?_⟩
  simp only [Function.comp_apply, f, (e ⟨v, hv⟩).2, dite_true]
  rw [Classical.choose_spec (hpre _)]
  simp

theorem span_one_tmul {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B) [P.IsPrime] :
    Submodule.span P.ResidueField (Set.range fun m : M => (1 : P.ResidueField) ⊗ₜ[B] m) = ⊤ := by
  rw [eq_top_iff]; rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul k m =>
    have : k ⊗ₜ[B] m = k • ((1 : P.ResidueField) ⊗ₜ[B] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact add_mem hx hy

def LeafResDimI : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → Module.finrank P.ResidueField (P.ResidueField ⊗[B] I) ≤ d

theorem LeafResT_of (hD : LeafResDimI) : LeafResT := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  have hfg := ideal_fg I _ _ hB hBI
  have : Module.Finite B I := Module.Finite.iff_fg.mpr hfg
  obtain ⟨f, hf⟩ := pick d (fun m : I => (1 : P.ResidueField) ⊗ₜ[B] m) 0 (span_one_tmul P) (hD d e A B I hB hBI P hIP)
  exact ⟨f, hf⟩

theorem LeafCoordsPointRes_of' (hD : LeafResDimI) (hY : LeafResY) : LeafCoordsPointRes :=
  LeafCoordsPointRes_of (LeafResT_of hD) hY

end LateralTheory.E.LeafCoordsPointResPf
end
end

section
noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (P : Ideal B) [P.IsPrime]

def delta0 (hIP : I ≤ P) : I →ₗ[B] P.ResidueField ⊗[B] Ω[B⁄A] where
  toFun x := (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)
  map_add' x y := by simp [TensorProduct.tmul_add]
  map_smul' b x := by
    simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, RingHom.id_apply]
    have : (1 : P.ResidueField) ⊗ₜ[B] ((x : B) • KaehlerDifferential.D A B b) = 0 := by
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
        Ideal.algebraMap_residueField_eq_zero.mpr (hIP x.2), TensorProduct.zero_tmul]
    rw [this, add_zero, TensorProduct.tmul_smul]

def delta (hIP : I ≤ P) : P.ResidueField ⊗[B] I →ₗ[P.ResidueField] P.ResidueField ⊗[B] Ω[B⁄A] :=
  LinearMap.liftBaseChange P.ResidueField (delta0 (A := A) I P hIP)

theorem delta_tmul (hIP : I ≤ P) (k : P.ResidueField) (x : I) :
    delta (A := A) I P hIP (k ⊗ₜ x) = k • ((1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) := by
  simp [delta, delta0]

def cot (hIP : I ≤ P) : (RingHom.ker (algebraMap B (B ⧸ I))).Cotangent →ₗ[B] P.ResidueField ⊗[B] I :=
  Submodule.liftQ _ ((TensorProduct.mk B P.ResidueField I 1) ∘ₗ
    Submodule.inclusion (p := RingHom.ker (algebraMap B (B ⧸ I))) (p' := I)
      (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hx))) (by
    intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha m _
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.map_smul_of_tower]
      rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
        Ideal.algebraMap_residueField_eq_zero.mpr (hIP (Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp ha))),
        TensorProduct.zero_tmul]
    · intro x y hx hy; exact add_mem hx hy)

theorem delta_injective (n m : ℕ) (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B)
    (hBI : Algebra.IsStandardSmoothOfRelativeDimension m A (B ⧸ I)) (hIP : I ≤ P) :
    Function.Injective (delta (A := A) I P hIP) := by
  obtain ⟨l, hl⟩ := conormal_retraction I n m hB hBI
  let ρ0 : Ω[B⁄A] →ₗ[B] P.ResidueField ⊗[B] I :=
    cot I P hIP ∘ₗ (l.restrictScalars B) ∘ₗ TensorProduct.mk B (B ⧸ I) Ω[B⁄A] 1
  let ρ := LinearMap.liftBaseChange P.ResidueField ρ0
  have h1 : ∀ x : I, ρ ((1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) =
      (1 : P.ResidueField) ⊗ₜ[B] x := by
    intro x
    have hx : (x : B) ∈ RingHom.ker (algebraMap B (B ⧸ I)) :=
      RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr x.2)
    have e1 : (1 : B ⧸ I) ⊗ₜ[B] KaehlerDifferential.D A B (x : B) =
        KaehlerDifferential.kerCotangentToTensor A B (B ⧸ I)
          ((RingHom.ker (algebraMap B (B ⧸ I))).toCotangent ⟨x, hx⟩) :=
      (KaehlerDifferential.kerCotangentToTensor_toCotangent A B (B ⧸ I) ⟨x, hx⟩).symm
    have e2 := LinearMap.congr_fun hl ((RingHom.ker (algebraMap B (B ⧸ I))).toCotangent ⟨x, hx⟩)
    simp only [ρ, ρ0, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.mk_apply, LinearMap.coe_restrictScalars]
    rw [e1]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at e2
    rw [e2]
    rfl
  have key : ∀ z, ρ (delta (A := A) I P hIP z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k x =>
      rw [delta_tmul, LinearMap.map_smul, h1, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact Function.LeftInverse.injective key

theorem range_delta (hIP : I ≤ P) : LinearMap.range (delta (A := A) I P hIP) =
    Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) := by
  rw [LinearMap.range_eq_map, ← span_one_tmul (M := I) P, Submodule.map_span, ← Set.range_comp]
  congr 1; ext; simp [delta_tmul]

def LeafResSpanD : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P →
    FiniteDimensional P.ResidueField (Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))) ∧
    Module.finrank P.ResidueField (Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))) ≤ d

theorem LeafResDimI_of (hS : LeafResSpanD) : LeafResDimI := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  obtain ⟨hfin, hle⟩ := hS d e A B I hB hBI P hIP
  have hinj := delta_injective (A := A) I P _ _ hB hBI hIP
  have e := LinearEquiv.ofInjective _ hinj
  rw [range_delta] at e
  have : FiniteDimensional P.ResidueField (P.ResidueField ⊗[B] I) := LinearEquiv.finiteDimensional e.symm
  rw [e.finrank_eq]; exact hle

theorem LeafCoordsPointRes_of'' (hS : LeafResSpanD) (hY : LeafResY) : LeafCoordsPointRes :=
  LeafCoordsPointRes_of' (LeafResDimI_of hS) hY

end LateralTheory.E.LeafCoordsPointResPf
end
end

section
noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (P : Ideal B) [P.IsPrime]

def nu : P.ResidueField ⊗[B] Ω[B⁄A] →ₗ[P.ResidueField] P.ResidueField ⊗[B] Ω[(B ⧸ I)⁄A] :=
  LinearMap.baseChange P.ResidueField ((KaehlerDifferential.map A A B (B ⧸ I)).restrictScalars B)

theorem nu_surjective : Function.Surjective (nu (A := A) I P) := by
  apply LinearMap.lTensor_surjective
  exact KaehlerDifferential.map_surjective_of_surjective A A B (B ⧸ I) Ideal.Quotient.mk_surjective

theorem nu_D (x : B) : nu (A := A) I P ((1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B x) =
    (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A (B ⧸ I) (Ideal.Quotient.mk I x) := by
  simp [nu]

def LeafResDimQ : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P →
    e ≤ Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[(B ⧸ I)⁄A])

theorem LeafResSpanD_of (hQ : LeafResDimQ) : LeafResSpanD := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  have : Nontrivial B := ⟨0, 1, fun h => Ideal.IsPrime.ne_top ‹P.IsPrime› (Ideal.eq_top_of_isUnit_mem P (zero_mem P)
    (by rw [h]; exact isUnit_one))⟩
  have := hB.isStandardSmooth
  have : Module.Free B Ω[B⁄A] := inferInstance
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := A) (S := B) (e + d)
  have hf : Module.finrank B Ω[B⁄A] = e + d := Module.finrank_eq_of_rank_eq hr
  have : Module.Finite B Ω[B⁄A] := inferInstance
  have hV : Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄A]) = e + d := by
    rw [Module.finrank_baseChange, hf]
  have hrn := LinearMap.finrank_range_add_finrank_ker (nu (A := A) I P)
  rw [LinearMap.range_eq_top.mpr (nu_surjective (A := A) I P), finrank_top, hV] at hrn
  have hq := hQ d e A B I hB hBI P hIP
  have hS : Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) ≤ LinearMap.ker (nu (A := A) I P) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    simp [nu_D, Ideal.Quotient.eq_zero_iff_mem.mpr x.2]
  exact ⟨inferInstance, (Submodule.finrank_mono hS).trans (by omega)⟩

end LateralTheory.E.LeafCoordsPointResPf
end
end

section
noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

theorem span_one_tmul_of {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B) [P.IsPrime]
    (S : Set M) (hS : Submodule.span B S = ⊤) :
    Submodule.span P.ResidueField ((fun m => (1 : P.ResidueField) ⊗ₜ[B] m) '' S) = ⊤ := by
  rw [eq_top_iff, ← span_one_tmul (M := M) P, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : m ∈ Submodule.span B S := hS ▸ trivial
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => dsimp only at hx hy ⊢; rw [TensorProduct.tmul_add]; exact add_mem hx hy
  | smul b x _ hx =>
    dsimp only at hx ⊢
    rw [TensorProduct.tmul_smul, ← algebraMap_smul P.ResidueField b]
    exact Submodule.smul_mem _ _ hx

def LeafResKer : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → LinearMap.ker (nu (A := A) I P) ≤
    Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))

def LeafResDimQe : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P →
    Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[(B ⧸ I)⁄A]) = e

theorem LeafResDimQ_of (h : LeafResDimQe) : LeafResDimQ := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  exact (h d e A B I hB hBI P hIP).ge

theorem LeafResY_of (hK : LeafResKer) (hQ : LeafResDimQe) : LeafResY := by
  intro d e A B _ _ _ I hB hBI P _ hIP t ht
  set K := P.ResidueField
  have := hB.isStandardSmooth
  have : Module.Finite B Ω[B⁄A] := inferInstance
  have hsurj := nu_surjective (A := A) I P
  have : FiniteDimensional K (K ⊗[B] Ω[(B ⧸ I)⁄A]) := Module.Finite.of_surjective _ hsurj

  have hD : ∀ x : I, (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (x : B) ∈
      Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (t j : B)) := by
    intro x
    have h1 : (1 : K) ⊗ₜ[B] x ∈ Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[B] t j) := ht ▸ trivial
    have := Submodule.mem_map_of_mem (f := delta (A := A) I P hIP) h1
    rw [Submodule.map_span, ← Set.range_comp] at this
    have e1 : ∀ z : I, delta (A := A) I P hIP ((1 : K) ⊗ₜ[B] z) = (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (z : B) :=
      fun z => by rw [delta_tmul, one_smul]
    simp only [Function.comp_def, e1] at this
    exact this
  have hker : LinearMap.ker (nu (A := A) I P) ≤
      Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (t j : B)) :=
    (hK d e A B I hB hBI P hIP).trans (Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hD x))

  have hV : Submodule.span K ((fun m => (1 : K) ⊗ₜ[B] m) '' Set.range (KaehlerDifferential.D A B)) = ⊤ :=
    span_one_tmul_of P _ (KaehlerDifferential.span_range_derivation A B)
  let g : B → K ⊗[B] Ω[(B ⧸ I)⁄A] := fun b => nu (A := A) I P ((1 : K) ⊗ₜ[B] KaehlerDifferential.D A B b)
  have hg : Submodule.span K (Set.range g) = ⊤ := by
    have := congrArg (Submodule.map (nu (A := A) I P)) hV
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj, ← Set.image_comp,
      ← Set.range_comp] at this
    exact this
  obtain ⟨y, hy⟩ := pick e g 0 hg (hQ d e A B I hB hBI P hIP).le
  refine ⟨y, eq_top_iff.mpr fun ω _ => ?_⟩
  set S := Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[B] dyt (A := A) y (fun j => (t j : B)) i)
  have hY : Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (y i)) ≤ S :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨Sum.inl i, rfl⟩)
  have hT : Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (t j : B)) ≤ S :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  have hω : nu (A := A) I P ω ∈ Submodule.map (nu (A := A) I P)
      (Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (y i))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    have : Set.range (g ∘ y) = Set.range (⇑(nu (A := A) I P) ∘
        fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (y i)) := rfl
    rw [← this, hy]; trivial
  obtain ⟨w, hw, hwν⟩ := hω
  have hk : ω - w ∈ LinearMap.ker (nu (A := A) I P) := by simp [hwν]
  have : ω = w + (ω - w) := by abel
  rw [this]
  exact add_mem (hY hw) (hT (hker hk))

theorem LeafCoordsPointRes_of_leaves (hQ : LeafResDimQe) (hK : LeafResKer) : LeafCoordsPointRes :=
  LeafCoordsPointRes_of'' (LeafResSpanD_of (LeafResDimQ_of hQ)) (LeafResY_of hK hQ)

end LateralTheory.E.LeafCoordsPointResPf
end
end
