import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseMatchingMonomialsRatioUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialsDifferByUnitsPositiveBoundaryCombinatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

open GlobalTheory.Poinc

theorem cone_gen_mem_of_common {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {r r' : ℕ} {ζ : Fin r → LinearMap.BilinForm ℤ X}
    {ζ' : Fin r' → LinearMap.BilinForm ℤ X} (hζ : IsCone bar φ ζ) (hζ' : IsCone bar φ ζ') (c : Fin r → ℕ)
    (c' : Fin r' → ℕ) (hc : ∀ j, 0 < c j) (he : ∑ j, c j • ζ j = ∑ j, c' j • ζ' j) (j : Fin r) :
    ∃ j', ζ j = ζ' j' := by
  obtain ⟨k, d, hk, hd⟩ := intCone_absorb hζ.mem hζ.nonneg hζ.linear hζ' c c' he j (hc j)
  have hd' : ∑ i, d i • ζ' i = ∑ l, (Pi.single j k : Fin r → ℕ) l • ζ l := by
    rw [← hd, Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_apply, hl]) (by simp)]
    simp
  have habs : ∀ i, 0 < d i → ∃ (k' : ℕ) (e : Fin r → ℕ), 0 < k' ∧ k' • ζ' i = ∑ l, e l • ζ l :=
    fun i hi => intCone_absorb hζ'.mem hζ'.nonneg hζ'.linear hζ d _ hd' i hi
  obtain ⟨f, hf⟩ := hζ.basis.exists_dual
  obtain ⟨g, hg⟩ := hζ'.basis.exists_dual
  let G : Fin r → balForms bar X := fun l => ⟨ζ l, hζ.mem l⟩
  let G' : Fin r' → balForms bar X := fun i => ⟨ζ' i, hζ'.mem i⟩
  have hfG : ∀ l m, f l (G m) = if l = m then 1 else 0 := hf
  have hgG : ∀ i m, g i (G' m) = if i = m then 1 else 0 := hg
  have hdG : k • G j = ∑ i, d i • G' i := Subtype.ext (by simp [G, G', hd])
  have hpos : ∀ i, 0 < d i → ∀ l, 0 ≤ f l (G' i) := by
    intro i hi l
    obtain ⟨k', e, hk', he'⟩ := habs i hi
    have h0 : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
    have h1 := congrArg (f l) h0
    rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      _root_.mul_one] at h1
    have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
    by_contra hneg
    push_neg at hneg
    have : (k' : ℤ) * f l (G' i) < 0 := mul_neg_of_pos_of_neg hk'' hneg
    linarith [Int.natCast_nonneg (e l)]
  have hex : ∃ i, 0 < d i := by
    by_contra hno
    push_neg at hno
    have h0 : k • ζ j = 0 := by
      rw [hd]
      exact Finset.sum_eq_zero fun i _ => by rw [Nat.le_zero.1 (hno i), zero_smul]
    refine hζ.linearIndependent.ne_zero j (LinearMap.ext₂ fun x y => ?_)
    have h1 := LinearMap.congr_fun₂ h0 x y
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hk.ne')
    · simpa using h2
  obtain ⟨i, hi⟩ := hex
  have hzero : ∀ l, l ≠ j → f l (G' i) = 0 := by
    intro l hl
    have h1 := congrArg (f l) hdG
    rw [map_nsmul, map_sum, hfG, if_neg hl, smul_zero] at h1
    simp only [map_nsmul, nsmul_eq_mul] at h1
    have hnn : ∀ i' ∈ Finset.univ, 0 ≤ (d i' : ℤ) * f l (G' i') := fun i' _ => by
      rcases Nat.eq_zero_or_pos (d i') with h | h
      · simp [h]
      · exact mul_nonneg (Int.natCast_nonneg _) (hpos i' h l)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1.symm i (Finset.mem_univ _)
    exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hi.ne')
  obtain ⟨k', e, hk', he'⟩ := habs i hi
  have hE : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
  have hem : ∀ m, (e m : ℤ) = k' * f m (G' i) := by
    intro m
    have h1 := congrArg (f m) hE
    rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      _root_.mul_one] at h1
    exact h1.symm
  have hEj : k' • G' i = e j • G j := by
    rw [hE]
    refine Finset.sum_eq_single j (fun m _ hm => ?_) (by simp)
    have h1 := hem m
    rw [hzero m hm, mul_zero] at h1
    rw [show e m = 0 by exact_mod_cast h1, zero_smul]
  have h1 := congrArg (g i) hEj
  simp only [map_nsmul, hgG, if_true, nsmul_eq_mul, _root_.mul_one] at h1
  have h2 := hem j
  have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
  have hu : f j (G' i) * g i (G j) = 1 := by
    have h3 : (k' : ℤ) * (f j (G' i) * g i (G j) - 1) = 0 := by
      rw [mul_sub, ← _root_.mul_assoc, ← h2, _root_.mul_one]
      linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hk''.ne')
  have hf1 : f j (G' i) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
    · exact h
    · have := Int.natCast_nonneg (e j)
      rw [h2, h] at this
      linarith
  have hej : e j = k' := by
    have := h2
    rw [hf1, _root_.mul_one] at this
    exact_mod_cast this
  rw [hej] at hEj
  refine ⟨i, LinearMap.ext₂ fun x y => ?_⟩
  have h3 := LinearMap.congr_fun₂ (congrArg Subtype.val hEj) x y
  simp only [G, G', Submodule.coe_smul, LinearMap.smul_apply, nsmul_eq_mul] at h3
  exact (mul_left_cancel₀ (by exact_mod_cast hk'.ne' : (k' : ℤ) ≠ 0) h3).symm

theorem coneSum_eq : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m m' : ℕ)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (δ' : Fin m' → LinearMap.BilinForm ℤ X), IsCone id φ δ → IsCone id φ δ' →
    ∀ (c : Fin m → ℕ) (c' : Fin m' → ℕ), (∀ k, 0 < c k) → (∀ k, 0 < c' k) →
    ∑ k, c k • δ k = ∑ k, c' k • δ' k → ∑ k, δ k = ∑ k, δ' k := by
  intro φ X _ _ m m' δ δ' hδ hδ' c c' hc hc' he
  classical
  have h1 : ∀ k, ∃ j, δ k = δ' j := cone_gen_mem_of_common hδ hδ' c c' hc he
  have h2 : ∀ j, ∃ k, δ' j = δ k := cone_gen_mem_of_common hδ' hδ c' c hc' he.symm
  have himg : Finset.univ.image δ = Finset.univ.image δ' := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨j, hj⟩ := h1 k
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := h2 j
      exact ⟨k, hk.symm⟩
  have e1 : ∑ x ∈ Finset.univ.image δ, x = ∑ k, δ k :=
    Finset.sum_image fun a _ b _ h => hδ.injective h
  have e2 : ∑ x ∈ Finset.univ.image δ', x = ∑ k, δ' k :=
    Finset.sum_image fun a _ b _ h => hδ'.injective h
  rw [← e1, ← e2, himg]

end GlobalTheory.TInj
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothCone_sum_generators_eq_of_common_interiorPoint : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m m' : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (δ' : Fin m' → LinearMap.BilinForm ℤ X), IsCone id φ δ → IsCone id φ δ' → ∀ (c : Fin m → ℕ) (c' : Fin m' → ℕ), (∀ k, 0 < c k) → (∀ k, 0 < c' k) → ∑ k, c k • δ k = ∑ k, c' k • δ' k → ∑ k, δ k = ∑ k, δ' k := by
  first | exact @GlobalTheory.TInj.coneSum_eq | exact GlobalTheory.TInj.coneSum_eq | (intros; apply GlobalTheory.TInj.coneSum_eq <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lattice_iso_eq_of_tautPts : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (ψ : InvFun ℤ) (m N n : ℕ) (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), 3 ≤ n → IsCone id ψ (fun k => ε (.inl k)) → (∀ x, x ≠ 0 → ∃ k, 0 < ε (.inl k) x x) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : (Fin m ⊕ Fin N) → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : (Fin m ⊕ Fin N) → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → Match D₁ D₂ b φ F → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ y, e₂ (φ y) = e₁ y := by
  intro o W _ _ _ T ψ m N n ε hn hcone hdef V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂
    hs₁ hu₁ hs₂ hu₂ hM hpts
  let ga : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e₁.symm.trans φ).trans e₂).toIntLinearEquiv
  have hga : ∀ a, ga a = e₂ (φ (e₁.symm a)) := fun _ => rfl

  have hcong : ∀ a, GlobalTheory.Poinc.CongMod n (ga a) a := by
    intro a
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpts a
    have h : e₂ p₂.y = e₂ (φ p₁.y) + n • e₂ z := by rw [hz, map_add, hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(e₂ z), ?_⟩
    rw [smul_neg, eq_add_neg_iff_add_eq, hga]
    exact h.symm

  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε n V D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F hτ₁ hτ₂ hF₁ hF₂ hM
  have hab : ∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) =
      algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i a b) := by
    intro a b
    obtain ⟨u, hu⟩ := hpu (e₁.symm a) (e₁.symm b)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hu
    exact ⟨u, hu⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r m N n (by omega) ε s₁ s₂ ga hs₁ hu₁ hs₂ hu₂ hab
  have hS := GlobalTheory.T.smoothCone_sum_generators_eq_of_common_interiorPoint ψ (Fin T.r → ℤ) m m (fun k => ε (.inl k)) (fun k => pull ga.toLinearMap (ε (.inl k))) hcone
    (hcone.pull_equiv ga) c₁ c₂ hc₁ hc₂ hsum

  have he : ∀ x y, (∑ k, ε (.inl k)) (ga x) (ga y) = (∑ k, ε (.inl k)) x y := by
    intro x y
    have h := LinearMap.congr_fun₂ hS x y
    simp only [LinearMap.sum_apply, pull_apply, LinearEquiv.coe_coe] at h ⊢
    exact h.symm
  have hpos : ∀ x, x ≠ 0 → 0 < (∑ k, ε (.inl k)) x x := by
    intro x hx
    obtain ⟨k, hk⟩ := hdef x hx
    simp only [LinearMap.sum_apply]
    exact Finset.sum_pos' (fun i _ => hcone.nonneg i x) ⟨k, Finset.mem_univ _, hk⟩
  have hrefl := GlobalTheory.Poinc.eq_refl_of_isometry_congMod (Fin T.r → ℤ) (∑ k, ε (.inl k)) hpos ga he n hn hcong
  intro y
  have h := DFunLike.congr_fun hrefl (e₁ y)
  rw [hga, AddEquiv.symm_apply_apply, LinearEquiv.refl_apply] at h
  exact h

end GlobalTheory.TInj
end
