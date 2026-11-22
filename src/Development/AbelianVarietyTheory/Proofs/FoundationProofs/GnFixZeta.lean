module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerDlogModPrimePowLevelLStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1CoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassCupProductGeometricStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleValueExpansionEqLogDerivSmulStatement

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.EdgeLoc

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem pow_chain (f : ℕ → Ω) (hf : ∀ k, f (k + 1) ^ p = f k) (m k : ℕ) : f (m + k) ^ (p ^ k) = f m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, hf, ih]

theorem zeta_le (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) : T.ζ L ^ (p ^ (L - n)) = T.ζ n := by
  have := pow_chain T.ζ T.ζpow n (L - n)
  rwa [Nat.add_sub_cancel' h] at this

theorem gn_fix_zeta (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) {g : Gal p Ω} (hg : g ∈ Gn T L) :
    g (T.ζ n) = T.ζ n := by
  rw [← zeta_le T h, map_pow, ((Basic.mem_gn T L g).1 hg).1]

theorem kum_add (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) {r : Ω} (hr : r ≠ 0) {x : Gal p Ω → ZMod (p ^ n)}
    (hx : IsKum T n (Gn T L) r x) {g g' : Gal p Ω} (hg : g ∈ Gn T L) (hg' : g' ∈ Gn T L) :
    x (g * g') = x g + x g' := by
  obtain ⟨χ, hχ⟩ := Basic.exists_isCyc T n
  rw [Basic.isKum_mul hχ hr hx hg hg', (Basic.isCyc_eq_one_iff hχ g).2 (gn_fix_zeta T h hg), one_mul]

variable (p) in
theorem adjoin_top (L : ℕ) : Algebra.adjoin (O0 p) {xn p L, yn p L} = ⊤ := by
  obtain ⟨b, hb⟩ := GlobalTheory.K5.OnFree.on_free p L
  rw [eq_top_iff]
  intro s _
  have hs : s ∈ Submodule.span (O0 p) (Set.range b) := b.span_eq ▸ Submodule.mem_top
  refine (Submodule.span_le (p := (Algebra.adjoin (O0 p) {xn p L, yn p L}).toSubmodule)).2 ?_ hs
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rw [hb]
  show _ ∈ Algebra.adjoin (O0 p) {xn p L, yn p L}
  have hx : xn p L ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := Algebra.subset_adjoin (by simp)
  have hy : yn p L ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := Algebra.subset_adjoin (by simp)
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hx _) (Subalgebra.pow_mem _ hy _)

theorem emb_int (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (z : On p L) : IsInt (p := p) (ι z) := by
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p L
  haveI : Module.Finite (O0 p) (On p L) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p L) := Algebra.IsIntegral.of_finite _ _
  exact IsIntegral.map ι (Algebra.IsIntegral.isIntegral z)

theorem emb_fix (T : Tower p Ω) {L : ℕ} {ι : On p L →ₐ[O0 p] Ω} (hι : IsEmb T L ι) {g : Gal p Ω}
    (hg : g ∈ Gn T L) (z : On p L) : g (ι z) = ι z := by
  have h := AlgHom.ext_of_adjoin_eq_top (adjoin_top p L) (φ₁ := (g : Ω →ₐ[O0 p] Ω).comp ι) (φ₂ := ι) (by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · simp [hι.1, ((Basic.mem_gn T L g).1 hg).1]
    · simp [hι.2, ((Basic.mem_gn T L g).1 hg).2])
  exact congrArg (fun φ : On p L →ₐ[O0 p] Ω => φ z) h

theorem pint (k : ℕ) : IsInt (p := p) ((p : Ω) ^ k) := by
  have := Basic.isInt_intCast (p := p) (Ω := Ω) ((p : ℤ) ^ k)
  push_cast at this
  exact this

theorem qq_int (T : Tower p Ω) (L : ℕ) : IsInt (p := p) (T.qq L) := by
  refine ⟨Polynomial.X ^ (p ^ L) - Polynomial.C (qO p),
    Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Basic.qq_pow, sub_self]

theorem reb_mem {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (y : O0 p) :
    ψ y ∈ Algebra.adjoin (O0 p) {T.qq L} := by
  have h := ψ.mem_range_self y
  rw [hψ.rng] at h
  exact h

theorem reb_int {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (y : O0 p) :
    IsInt (p := p) (ψ y) := by
  have h : Algebra.adjoin (O0 p) {T.qq L} ≤ integralClosure (O0 p) Ω :=
    Algebra.adjoin_le (by rw [Set.singleton_subset_iff, SetLike.mem_coe, mem_integralClosure_iff]; exact qq_int T L)
  exact h (reb_mem hψ y)

theorem reb_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {g : Gal p Ω}
    (hg : g (T.qq L) = T.qq L) (y : O0 p) : g (ψ y) = ψ y := by
  have h : Algebra.adjoin (O0 p) {T.qq L} ≤ AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id (O0 p) Ω) :=
    Algebra.adjoin_le (by
      rw [Set.singleton_subset_iff, SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg)
  have h2 := h (reb_mem hψ y)
  rw [AlgHom.mem_equalizer] at h2
  simpa using h2

theorem ev_int {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {c : ℤ → Ω} {x x' : Ω}
    (h : Ev ψ c x x') : IsInt (p := p) x ∧ IsInt (p := p) x' := by
  obtain ⟨d, e, a, he, -, rfl, rfl⟩ := h
  exact ⟨(integralClosure (O0 p) Ω).sum_mem fun t _ => (he t).1.mul (reb_int hψ _),
    (integralClosure (O0 p) Ω).sum_mem fun t _ => (he t).1.mul (reb_int hψ _)⟩

theorem ev_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {c : ℤ → Ω} {x x' : Ω}
    (h : Ev ψ c x x') {g : Gal p Ω} (hg : g ∈ Ggeo p Ω ⊓ Gn T L) : g x = x ∧ g x' = x' := by
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have hq : g (T.qq L) = T.qq L := ((Basic.mem_gn T L g).1 hg2).2
  obtain ⟨d, e, a, he, -, rfl, rfl⟩ := h
  set_option synthInstance.maxHeartbeats 100000 in
    constructor <;> rw [map_sum] <;>
      refine Finset.sum_congr rfl fun t _ => ?_ <;>
      rw [map_mul, hg1 _ (he t).2, reb_fix hψ hq]

theorem conj_mem {T : Tower p Ω} {L : ℕ} {σ g : Gal p Ω} (hσ : σ ∈ Gn T L) (hg : g ∈ Ggeo p Ω ⊓ Gn T L) :
    σ * g * σ⁻¹ ∈ Ggeo p Ω ⊓ Gn T L := by
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_inf.2 ⟨fun z hz => ?_, (Gn T L).mul_mem ((Gn T L).mul_mem hσ hg2) ((Gn T L).inv_mem hσ)⟩
  have h1 : IsAlgZp p (σ⁻¹ z) := by
    obtain ⟨P, hP, e⟩ := hz
    refine ⟨P, hP, ?_⟩
    have := Polynomial.aeval_algHom_apply ((σ⁻¹ : Gal p Ω) : Ω →ₐ[O0 p] Ω) z (P.map (algebraMap ℤ_[p] (O0 p)))
    rw [e, map_zero] at this
    simpa using this
  show σ (g (σ⁻¹ z)) = z
  rw [hg1 _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem algZp_root {κ ρ : Ω} (hκ : IsAlgZp p κ) {m : ℕ} (hm : 0 < m) (h : ρ ^ m = κ) : IsAlgZp p ρ := by
  obtain ⟨P, hP, e⟩ := hκ
  refine ⟨Polynomial.expand ℤ_[p] m P, (Polynomial.expand_ne_zero hm).2 hP, ?_⟩
  rw [Polynomial.map_expand, Polynomial.expand_aeval, h, e]

end GlobalTheory.EdgeLoc

namespace GlobalTheory.EdgeLoc

end GlobalTheory.EdgeLoc
