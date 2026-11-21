import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplQuot
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinQuotAnn
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FlatnessPrecompleteProducts

section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem pullback_fin_relation {k C : Type} [Field k] [CommRing C] [Algebra k C] (S : Subalgebra k C)
    [Module.Finite k S] (T : Set C) (hT : T ⊆ S) (hfg : (Ideal.span T).FG)
    (hI : ∀ x ∈ Ideal.span T, IsUnit (1 - x))
    (hd : ∀ (n : ℕ) (c : C), ∃ a ∈ S, ∃ s ∈ S, IsUnit s ∧ s * c - a ∈ Ideal.span T ^ n) :
    Module.Finite k C := by
  set J := Ideal.span T with hJ
  have hinv : ∀ s ∈ S, IsUnit s → ∃ t ∈ S, t * s = 1 := by
    intro s hsS hs
    let f : S →ₗ[k] S := LinearMap.mulLeft k (⟨s, hsS⟩ : S)
    have hfi : Function.Injective f := by
      intro x y hxy
      have h1 : s * (x : C) = s * (y : C) := congrArg Subtype.val hxy
      exact Subtype.ext (hs.mul_left_cancel h1)
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hfi) 1
    refine ⟨y, y.2, ?_⟩
    have h2 : s * (y : C) = 1 := congrArg Subtype.val hy
    rw [mul_comm]
    exact h2
  have hC : ∀ (n : ℕ) (c : C), ∃ a ∈ S, c - a ∈ J ^ n := by
    intro n c
    obtain ⟨a, haS, s, hsS, hs, hmem⟩ := hd n c
    obtain ⟨t, htS, hts⟩ := hinv s hsS hs
    refine ⟨t * a, S.mul_mem htS haS, ?_⟩
    have e : c - t * a = t * (s * c - a) := by
      calc c - t * a = (t * s) * c - t * a := by rw [hts, one_mul]
        _ = t * (s * c - a) := by ring
    rw [e]
    exact Ideal.mul_mem_left _ t hmem
  let W : ℕ → Submodule k S := fun n =>
    Submodule.comap S.val.toLinearMap ((J ^ n).restrictScalars k)
  have hWmem : ∀ n (x : S), x ∈ W n ↔ (x : C) ∈ J ^ n := fun n x => Iff.rfl
  have hWle : ∀ n, W (n + 1) ≤ W n := by
    intro n x hx
    rw [hWmem] at hx ⊢
    exact Ideal.pow_le_pow_right (Nat.le_succ n) hx
  obtain ⟨n0, hn0⟩ : ∃ n0, W n0 ≤ W (n0 + 1) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ n, Module.finrank k (W (n + 1)) < Module.finrank k (W n) := by
      intro n
      exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hWle n) (fun h => hcon n h.ge))
    have hbd : ∀ n, n + Module.finrank k (W n) ≤ Module.finrank k (W 0) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        have := hlt m
        omega
    have := hbd (Module.finrank k (W 0) + 1)
    omega
  have hstep : J ^ n0 ≤ J ^ (n0 + 1) := by
    intro x hx
    obtain ⟨a, haS, hxa⟩ := hC (n0 + 1) x
    have haJ : a ∈ J ^ n0 := by
      have h1 : x - a ∈ J ^ n0 := Ideal.pow_le_pow_right (Nat.le_succ n0) hxa
      have h2 := Ideal.sub_mem _ hx h1
      simpa using h2
    have ha1 : a ∈ J ^ (n0 + 1) := (hWmem (n0 + 1) ⟨a, haS⟩).mp (hn0 ((hWmem n0 ⟨a, haS⟩).mpr haJ))
    have h3 := Ideal.add_mem _ hxa ha1
    simpa using h3
  have hzero : J ^ n0 = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J (J ^ n0) (Ideal.FG.pow (n := n0) hfg)
    · rw [smul_eq_mul, ← pow_succ']
      exact hstep
    · intro x hx
      rw [Ideal.mem_jacobson_bot]
      intro y
      have h := hI (-(x * y)) (J.neg_mem (J.mul_mem_right y hx))
      rw [sub_neg_eq_add, add_comm] at h
      exact h
  have hsurj : Function.Surjective S.val.toLinearMap := by
    intro c
    obtain ⟨a, haS, hca⟩ := hC n0 c
    rw [hzero, Ideal.mem_bot, sub_eq_zero] at hca
    exact ⟨⟨a, haS⟩, hca.symm⟩
  exact Module.Finite.of_surjective _ hsurj

theorem UpperTheory.V.AlgebraTools.IsCplAt.finite_of_finite :
    ∀ (Λ R : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [Algebra Λ R] [Module.Finite Λ R]
      (p : Ideal Λ) (q : Ideal R) (L B : Type) [CommRing L] [IsLocalRing L] [CommRing B] [IsLocalRing B]
      [Algebra Λ L] [Algebra R B] [Algebra L B] [Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B],
      IsCplAt Λ p L → IsCplAt R q B → q.comap (algebraMap Λ R) = p → Module.Finite L B := by
  intro Λ R _ _ _ _ _ p q L B _ _ _ _ _ _ _ _ _ _ hL hB hq
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing Λ R
  haveI := hL.complete
  have hpB : Ideal.map (algebraMap Λ B) p ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_eq Λ R B, ← Ideal.comap_comap,
      hB.comap_eq, hq]
  have hmL : maximalIdeal L = Ideal.map (algebraMap Λ L) p := by
    simpa using (IsCplAt.map_pow_eq Λ p L hL 1).symm
  have hle : (maximalIdeal L).map (algebraMap L B) ≤ maximalIdeal B := by
    rw [hmL, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hpB
  haveI : IsHausdorff ((maximalIdeal L).map (algebraMap L B)) B :=
    ⟨fun x hx => IsHausdorff.haus hB.complete.toIsHausdorff x
      (fun n => SModEq.mono (Submodule.smul_mono_left (Ideal.pow_right_mono hle n)) (hx n))⟩
  letI : Field (L ⧸ maximalIdeal L) := Ideal.Quotient.field _
  let π : B →+* (B ⧸ (maximalIdeal L).map (algebraMap L B)) := Ideal.Quotient.mk _
  let φ : R →+* (B ⧸ (maximalIdeal L).map (algebraMap L B)) := π.comp (algebraMap R B)
  let ψ0 : Λ →+* (L ⧸ maximalIdeal L) := (Ideal.Quotient.mk (maximalIdeal L)).comp (algebraMap Λ L)
  have hΛ : ∀ x : Λ, φ (algebraMap Λ R x) =
      algebraMap (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B)) (ψ0 x) := by
    intro x
    show π (algebraMap R B (algebraMap Λ R x)) = _
    rw [← IsScalarTower.algebraMap_apply Λ R B, IsScalarTower.algebraMap_apply Λ L B]
    rfl
  have hcomp : (algebraMap (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B))).comp ψ0
      = φ.comp (algebraMap Λ R) := RingHom.ext fun x => (hΛ x).symm
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := Λ) (M := R)
  let S : Subalgebra (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B)) :=
    Algebra.adjoin (L ⧸ maximalIdeal L) (φ '' (G : Set R))
  haveI : Module.Finite (L ⧸ maximalIdeal L) S := by
    have hfg := fg_adjoin_of_finite (R := L ⧸ maximalIdeal L) ((G.finite_toSet).image φ) (by
      rintro _ ⟨g, -, rfl⟩
      obtain ⟨p0, hmon, hev⟩ := Algebra.IsIntegral.isIntegral (R := Λ) g
      refine ⟨p0.map ψ0, hmon.map _, ?_⟩
      rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hev, map_zero])
    exact Module.Finite.iff_fg.mpr hfg
  have hφS : ∀ r, φ r ∈ S := by
    intro r
    have hr : r ∈ Submodule.span Λ (G : Set R) := by
      rw [hG]
      trivial
    induction hr using Submodule.span_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, hΛ]
      exact S.mul_mem (S.algebraMap_mem _) hx
  have hspan : Ideal.span (φ '' (q : Set R)) = Ideal.map φ q := rfl
  have hmapq : Ideal.map φ q = Ideal.map π (Ideal.map (algebraMap R B) q) := by
    rw [Ideal.map_map]
  haveI : Module.Finite (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B)) := by
    refine pullback_fin_relation S (φ '' (q : Set R)) (by rintro _ ⟨r, _, rfl⟩; exact hφS r) ?_ ?_ ?_
    · rw [hspan]
      exact Ideal.FG.map (IsNoetherian.noetherian q) φ
    · intro x hx
      rw [hspan, hmapq, Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hyB : y ∈ maximalIdeal B := (Ideal.map_le_iff_le_comap.mpr hB.comap_eq.ge) hy
      have hu := isUnit_one_sub_self_of_mem_nonunits y hyB
      rw [← map_one π, ← map_sub]
      exact hu.map π
    · intro n c
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨a0, s0, hs0, hmem⟩ := hB.dense n b
      refine ⟨φ a0, hφS a0, φ s0, hφS s0, ?_, ?_⟩
      · have hu : IsUnit (algebraMap R B s0) := by
          by_contra hnu
          apply hs0
          rw [← hB.comap_eq]
          exact Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
        exact hu.map π
      · have hpow : (Ideal.map φ q) ^ n = Ideal.map π (maximalIdeal B ^ n) := by
          rw [← Ideal.map_pow, ← IsCplAt.map_pow_eq R q B hB n, Ideal.map_map]
        rw [hspan, hpow]
        convert Ideal.mem_map_of_mem π hmem using 1
        simp [φ, π]
  haveI : Module.Finite L (B ⧸ (maximalIdeal L).map (algebraMap L B)) :=
    Module.Finite.trans (L ⧸ maximalIdeal L) _
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal L)
end

section
open IsLocalRing UpperTheory.V.AlgebraTools TensorProduct

private theorem rTensor_inj_of_map {Λ : Type} [CommRing Λ] (p : Ideal Λ) {L : Type} [CommRing L]
    [Algebra Λ L] (m : Ideal L) (hm : p.map (algebraMap Λ L) = m)
    (N : Type) [AddCommGroup N] [Module Λ N] [Module L N] [IsScalarTower Λ L N]
    [Module.Flat Λ N] : Function.Injective (m.subtype.rTensor N) := by
  have hmem : ∀ a : p, algebraMap Λ L a ∈ m := fun a => hm ▸ Ideal.mem_map_of_mem _ a.2
  let ι : p →+ m :=
    { toFun := fun a => ⟨algebraMap Λ L a, hmem a⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let σ : p ⊗[Λ] N →+ m ⊗[L] N :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun a => (TensorProduct.mk L m N (ι a)).toAddMonoidHom)
        (fun a b => by ext n; simp [TensorProduct.add_tmul]))
      (fun r a n => by
        change ι (r • a) ⊗ₜ[L] n = ι a ⊗ₜ[L] (r • n)
        have h : ι (r • a) = algebraMap Λ L r • ι a := by
          apply Subtype.ext
          change algebraMap Λ L (r • (a : Λ)) = algebraMap Λ L r * algebraMap Λ L a
          rw [smul_eq_mul, map_mul]
        rw [h, TensorProduct.smul_tmul, algebraMap_smul])
  have key : ∀ y, y ∈ Submodule.span L (algebraMap Λ L '' (p : Set Λ)) →
      ∀ (hy : y ∈ m) (n : N), (⟨y, hy⟩ : m) ⊗ₜ[L] n ∈ σ.range := by
    intro y hy'
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro hy n
      exact AddMonoidHom.mem_range.mpr ⟨(⟨a, ha⟩ : p) ⊗ₜ[Λ] n, by
        rw [TensorProduct.liftAddHom_tmul]; rfl⟩
    | zero =>
      intro hy n
      have h : (⟨0, hy⟩ : m) = 0 := rfl
      rw [h, TensorProduct.zero_tmul]
      exact zero_mem _
    | add y₁ y₂ h₁ h₂ ih₁ ih₂ =>
      intro hy n
      have m₁ : y₁ ∈ m := by rw [← hm]; exact h₁
      have m₂ : y₂ ∈ m := by rw [← hm]; exact h₂
      have h : (⟨y₁ + y₂, hy⟩ : m) = ⟨y₁, m₁⟩ + ⟨y₂, m₂⟩ := rfl
      rw [h, TensorProduct.add_tmul]
      exact add_mem (ih₁ m₁ n) (ih₂ m₂ n)
    | smul l y h₁ ih =>
      intro hy n
      have m₁ : y ∈ m := by rw [← hm]; exact h₁
      have h : (⟨l • y, hy⟩ : m) = l • ⟨y, m₁⟩ := rfl
      rw [h, TensorProduct.smul_tmul]
      exact ih m₁ (l • n)
  have hsurj : ∀ z : m ⊗[L] N, z ∈ σ.range := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a n =>
      exact key a.1 (show (a : L) ∈ p.map (algebraMap Λ L) by rw [hm]; exact a.2) a.2 n
    | add x y hx hy => exact add_mem hx hy
  have hcomp : ∀ w : p ⊗[Λ] N, TensorProduct.lid L N (m.subtype.rTensor N (σ w))
      = TensorProduct.lid Λ N (p.subtype.rTensor N w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
      rw [TensorProduct.liftAddHom_tmul]
      change TensorProduct.lid L N (m.subtype.rTensor N ((⟨algebraMap Λ L a, hmem a⟩ : m) ⊗ₜ[L] n))
        = _
      simp [algebraMap_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨w, rfl⟩ := AddMonoidHom.mem_range.mp (hsurj z)
  have hw : p.subtype.rTensor N w = 0 := by
    apply (TensorProduct.lid Λ N).injective
    rw [← hcomp, hz, map_zero, map_zero]
  have hw0 : w = 0 := Module.Flat.rTensor_preserves_injective_linearMap p.subtype
    Subtype.val_injective (by rw [hw, map_zero])
  rw [hw0, map_zero]

theorem UpperTheory.V.AlgebraTools.IsCplAt.free_of_flat :
    ∀ (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (p : Ideal Λ) (L : Type) [CommRing L] [IsLocalRing L] [Algebra Λ L]
      (N : Type) [AddCommGroup N] [Module Λ N] [Module L N] [IsScalarTower Λ L N] [Module.Finite L N]
      [Module.Flat Λ N], IsCplAt Λ p L → Module.Free L N := by
  intro Λ _ _ p L _ _ _ N _ _ _ _ _ _ h
  haveI := h.noeth
  haveI : Module.FinitePresentation L N := Module.finitePresentation_of_finite L N
  apply Module.free_of_maximalIdeal_rTensor_injective
  exact rTensor_inj_of_map p _ (by simpa using IsCplAt.map_pow_eq Λ p L h 1) N
end

section
open IsLocalRing UpperTheory.V.AlgebraTools




theorem UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange :
    ∀ (Λ R : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Algebra Λ R]
      (p : Ideal Λ) (q : Ideal R) (L B : Type) [CommRing L] [IsLocalRing L] [CommRing B] [IsLocalRing B]
      [Algebra Λ L] [Algebra R B] [Algebra L B] [Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B]
      (M : Type) [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M] [Module.Flat Λ M],
      IsCplAt Λ p L → IsCplAt R q B → q.comap (algebraMap Λ R) = p →
      Module.Finite L (TensorProduct R B M) ∧ Module.Free L (TensorProduct R B M) :=
  _root_.UpperTheory.Reformulated.B.FlatnessPrecompleteProducts.finite_free_baseChange
end
