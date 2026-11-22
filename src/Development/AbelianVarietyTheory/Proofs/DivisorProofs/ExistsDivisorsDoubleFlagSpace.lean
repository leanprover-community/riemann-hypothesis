module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorPullbackOfDominantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartierLocalEquationDiagonalOfAdaptedFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitStalkTransitionPulledBackFlagFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorTwoByTwoTriangularProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostLowerTriangularDiagMinorIsUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicMatrixFamilyDiagIsUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeDiagonalOfNotUnitTransitionEntryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitOffDiagonalTransitionOnCommonSectionStatement

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.DivOn

theorem unitAt_of {Z : Scheme.{0}} [IsIntegral Z] {z : Z} {u : Z.functionField} (h0 : u ≠ 0)
    (h : u ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range)
    (h' : u⁻¹ ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range) : UnitAt z u :=
  (unitAt_iff h0).2 ⟨h, h'⟩

theorem key {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) {gr : Root m → Y.Dv}
    {B : Mat m Y.Fn} (hB : B ∈ E'.S (genericPoint Y.X))
    (hgr : ∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t)
    (W : Dbl Y) (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) {τ : ι} {a b : Fin (m τ)} (hab : (b : ℕ) = a + 1)
    (hC : AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹)) {D₁ D₂ : Root m → CartierDiv W.Z}
    (hD₁ : ∀ x, IsPull W.p₁ (D₁ x) (gr x)) (hD₂ : ∀ x, IsPull W.p₂ (D₂ x) (gr x)) (z : W.Z)
    {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) :
    ∃ t₁ t₂ : Root m → W.Z.functionFieldˣ, (∀ x, (D₁ x).IsEqn z (t₁ x)) ∧ (∀ x, (D₂ x).IsEqn z (t₂ x)) ∧
      AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∧
      (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ →
        UnitAt z ((t₁ x : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) x.1 x.2 x.2 * t₂ x)) ∧
      UnitAt z ((t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (t₁ ⟨τ, b⟩ : W.Z.functionField)⁻¹ *
        minor τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) * (t₂ ⟨τ, a⟩ * t₂ ⟨τ, b⟩)) ∧
      (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b =
        (t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) τ a b * t₂ ⟨τ, b⟩ ∧
      RegAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨hP₁, h₁⟩ := GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame F Y ι m E' gr B hB hgr _ A₁ hA₁
  obtain ⟨hP₂, h₂⟩ := GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame F Y ι m E' gr B hB hgr _ A₂ hA₂
  choose s₁ e₁ q₁ using h₁
  choose s₂ e₂ q₂ using h₂
  have hT₁ : Par m ⊤ ((B * A₁⁻¹).map W.α₁) := hP₁.map W.α₁ fun _ _ => trivial
  have hT₂ : Par m ⊤ ((B * A₂⁻¹).map W.α₂) := hP₂.map W.α₂ fun _ _ => trivial
  have hloc := GlobalTheory.T.isUnit_stalk_transition_pulledBack_flagFrames F X Y ι m E E' φ f hf W hα z A₁ hA₁ A₂ hA₂
  have dB₁ : ∀ σ, (B.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dB₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dA₁ : ∀ σ, (A₁.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hA₁ σ)
  have eg : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ =
      ((B * A₁⁻¹).map W.α₁)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) * (B * A₂⁻¹).map W.α₂ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, Mat.mul_inv_rev, Mat.inv_inv dA₁, mul_assoc, mul_assoc,
      mul_assoc, ← mul_assoc (B.map W.α₂)⁻¹, Mat.inv_mul dB₂, one_mul, ← mul_assoc (B.map W.α₁)⁻¹, Mat.inv_mul dB₁,
      one_mul]
  obtain ⟨hal, hd, hab', hmin⟩ := GlobalTheory.T.minor_two_by_two_triangular_product ι m τ a b hab _ _ _ _ hT₁.inv hT₂ hC
  rw [← eg] at hal hd hab' hmin
  obtain ⟨hu, hm0, hm1⟩ := GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit ι m τ a b hab _ _ _ hal hloc
  have i₁ : ∀ x : Root m, ((B * A₁⁻¹).map W.α₁)⁻¹ x.1 x.2 x.2 = (W.α₁ (s₁ x))⁻¹ := fun x => by
    rw [(GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m _ ⊤ _ hT₁ x).2.2.1, ← e₁ x]; rfl
  have i₂ : ∀ x : Root m, ((B * A₂⁻¹).map W.α₂) x.1 x.2 x.2 = W.α₂ (s₂ x) := fun x => by
    rw [← e₂ x]; rfl
  refine ⟨fun x => Units.map W.α₁.toMonoidHom (s₁ x), fun x => Units.map W.α₂.toMonoidHom (s₂ x),
    fun x => hD₁ x _ _ (q₁ x) z rfl, fun x => hD₂ x _ _ (q₂ x) z rfl, hal, fun x hxa hxb => ?_, ?_, ?_,
    (hloc τ).1 a b⟩
  · have := unitAt_of (hu x hxa hxb).1 ((hloc x.1).1 x.2 x.2) (hu x hxa hxb).2
    rw [hd x hxa hxb, i₁, i₂] at this
    exact this
  · have hmem : minor τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∈
        (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range :=
      sub_mem (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _)) (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _))
    have := unitAt_of hm0 hmem hm1
    rw [hmin, i₁ ⟨τ, a⟩, i₁ ⟨τ, b⟩, i₂ ⟨τ, a⟩, i₂ ⟨τ, b⟩] at this
    exact this
  · rw [hab', i₁ ⟨τ, a⟩, i₂ ⟨τ, b⟩]
    rfl

end GlobalTheory.FlagPush.DivOn
