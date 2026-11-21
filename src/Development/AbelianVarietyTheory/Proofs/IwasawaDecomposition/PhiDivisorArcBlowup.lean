import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.TorRef

theorem exists_sabMap_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.proved_CubePullSt f t
  exact ⟨_, ⟨m⟩⟩

theorem cmpSt_of_sabExtNormalSt : SabExtNormalSt → CmpSt := by
  intro hS E _ _ _ H D l Xo c O O' _ _ β β' Y Z ρ hρ hN
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  obtain ⟨t₀, ⟨n₁⟩⟩ := exists_sabMap_pull (genι Z) Z.t
  obtain ⟨t', ⟨n'⟩⟩ := exists_sabMap_pull (ρ ≫ genι Y) Y.t
  obtain ⟨a, ha⟩ := GlobalTheory.LevelCover.sab_cancel n₁ Z.m Z.jQ rfl
  obtain ⟨k, hk⟩ := GlobalTheory.LevelCover.sab_cancel Y.m0.toSABMap Z.m0.toSABMap (𝟙 _) (Category.id_comp _)
  obtain ⟨ky, hky⟩ := GlobalTheory.LevelCover.sab_comp k Y.m (e := Z.jQ ≫ ρ ≫ genι Y)
    (by rw [Category.id_comp, ← hρ, Category.assoc])
  obtain ⟨a', ha'⟩ := GlobalTheory.LevelCover.sab_cancel n' ky Z.jQ rfl
  have hdom : IsDominant Z.jQ := ⟨Z.jQ_dense⟩
  obtain ⟨b, hb⟩ := hS E H (gen Z) (Xo.XF c) Z.jQ hN Z.jQ_open hdom Z.oF.t t₀ t' a a' Z.oF.proper
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.LevelCover.sab_comp b n' (Category.id_comp _)
  refine ⟨t₀, n₁, n₂, fun T g g₁ g₂ h₁ h₂ h₃ h₄ => ?_⟩
  have hg : g = g₁ ≫ a.φ := by
    apply n₁.cart.1.hom_ext
    · rw [h₂, Category.assoc, ha]
    · rw [h₁, Category.assoc, a.cart.1.w]
  have hg₂ : g₁ ≫ k.φ = g₂ := by
    apply Y.m0.toSABMap.cart.1.hom_ext
    · rw [Category.assoc, hk, h₃]
    · rw [Category.assoc, k.cart.1.w, Category.comp_id, h₄]
  rw [hn₂, hg]
  simp only [Category.assoc]
  rw [reassoc_of% hb, ha', hky, reassoc_of% hg₂]

end GlobalTheory.TorRef
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem isUnit_natCast_of_primes {W : Type} [CommRing W] (h : ∀ p : ℕ, p.Prime → IsUnit (p : W)) (n : ℕ)
    (hn : n ≠ 0) : IsUnit (n : W) := by
  revert hn
  induction n using Nat.recOnMul with
  | zero => intro h0; exact absurd rfl h0
  | one => intro _; simp
  | prime p hp => intro _; exact h p hp
  | mul a b ha hb =>
    intro hab
    rw [Nat.cast_mul]
    exact (ha (left_ne_zero_of_mul hab)).mul (hb (right_ne_zero_of_mul hab))

theorem isUnit_map_of_ne_zero {K : Type} [Field K] [NumberField K] {W : Type} [CommRing W]
    (h : ∀ p : ℕ, p.Prime → IsUnit (p : W)) (f : 𝓞 K →+* W) {a : 𝓞 K} (ha : a ≠ 0) : IsUnit (f a) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hN : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha
  have e : f b * f a = (Ideal.absNorm (Ideal.span {a}) : W) := by rw [← map_mul, hb, map_natCast]
  exact isUnit_of_mul_isUnit_right (e ▸ isUnit_natCast_of_primes h _ hN)

theorem idlAlong_comap {X X' : Scheme.{0}} (k : X' ⟶ X) (I : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X') : idlAlong (I.comap k) ξ = idlAlong I (ξ ≫ k) := by
  unfold idlAlong
  rw [VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

theorem idlAlong_pow {X : Scheme.{0}} (I : X.IdealSheafData) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) : idlAlong (I ^ n) ξ = idlAlong I ξ ^ n := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
  rw [TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, ← Ideal.map_pow]
  congr 1

theorem blowOrd_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d' : ℕ) (φ : InvFun (𝓞 E)), IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∃ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be ∧ idlAlong EX.idealSheaf χ = Ideal.span {ϖ ^ m} := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d' φ hY hB W _ _ _ hW hp ϖ hϖ χ t mt P hr be hbe hmon
  obtain ⟨-, -, -, hjQ, -, hEX, -⟩ := hB
  have := c.fin
  have : NumberField c.F := {}

  let f : 𝓞 c.F →+* W := (Spec.preimage (χ ≫ Z.s)).hom
  let g : c.F →+* W := IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F) (g := f)
    fun y => isUnit_map_of_ne_zero hp f (nonZeroDivisors.ne_zero y.2)
  have hg : g.comp (algebraMap (𝓞 c.F) c.F) = f := IsLocalization.lift_comp _
  have hsq : χ ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, f, CommRingCat.ofHom_hom, Spec.map_preimage]
  let χ₀ : Sp W ⟶ gen Z := pullback.lift χ (spMap g) hsq
  have hχ : χ₀ ≫ genι Z = χ := pullback.lift_fst _ _ _

  have hI : idlAlong EX.idealSheaf χ = idlAlong BY.idealSheaf (χ₀ ≫ e.inv ≫ genι Y) ^ n := by
    calc idlAlong EX.idealSheaf χ = idlAlong EX.idealSheaf ((χ₀ ≫ e.inv) ≫ e.hom ≫ genι Z) := by
          rw [Category.assoc, e.inv_hom_id_assoc, hχ]
      _ = idlAlong (EX.idealSheaf.comap (e.hom ≫ genι Z)) (χ₀ ≫ e.inv) := (idlAlong_comap _ _ _).symm
      _ = idlAlong ((BY.idealSheaf ^ n).comap (genι Y)) (χ₀ ≫ e.inv) := by rw [hEX]
      _ = idlAlong (BY.idealSheaf ^ n) ((χ₀ ≫ e.inv) ≫ genι Y) := idlAlong_comap _ _ _
      _ = _ := by rw [idlAlong_pow, Category.assoc]

  have hZY : Z.jQ ≫ e.inv = Y.jQ := by rw [← hjQ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨t₀, n₁, n₂, -⟩ := cmpSt_of_sabExtNormalSt (sabExtNormalSt_of_homExtNormalSt homExtNormal) E H D l Xo c
    c.F (𝓞 c.F) (RingHom.id c.F) (algebraMap (𝓞 c.F) c.F) Y Z e.inv hZY
    (ModelRelCompare.normal_genericFibre Z (ModelRelCompare.isDedFrac_in_use c).1).1
  obtain ⟨a⟩ := TraitOrder.cancel hχ n₁ mt
  obtain ⟨b⟩ := TraitOrder.comp (h := χ₀ ≫ e.inv ≫ genι Y) rfl n₂ a

  have hr' : Set.range (jK W ≫ χ₀ ≫ e.inv ≫ genι Y) ⊆ Set.range Y.j := by
    rintro _ ⟨p, rfl⟩
    have hz : (jK W ≫ χ₀) p ∈ Set.range Z.jQ := by
      rw [← Z.ab_gen]
      obtain ⟨q, hq⟩ := hr ⟨p, rfl⟩
      show (jK W ≫ χ₀ ≫ genι Z) p ∈ abLocus Z.t.G
      rw [hχ, ← hq]
      show genι Z (Z.jQ q) ∈ abLocus Z.t.G
      rw [← Set.mem_preimage, Z.ab_gen]
      exact ⟨q, rfl⟩
    obtain ⟨q, hq⟩ := hz
    refine ⟨q, ?_⟩
    show (Y.jQ ≫ genι Y) q = _
    rw [← hZY]
    simp only [Scheme.Hom.comp_apply] at hq ⊢
    rw [hq]
  obtain ⟨m₀, hm₀, hid⟩ := hY W hW ϖ hϖ _ t b P hr' be hbe hmon
  refine ⟨n * m₀, ?_, ?_⟩
  · push_cast
    rw [hm₀]
    simp only [InvFun.evalZ, InvFun.eval, comb]
    push_cast
    ring
  · rw [hI, hid, Ideal.span_singleton_pow, pow_mul']

end GlobalTheory.TorRef
end
end
