import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtFrRdA

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section LC

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

private lemma valprod_lemma {R : Type} [CommRing R] (φ : R →+* ℂ) (u : K → Rˣ) (ε : K → ℤ) :
    φ ↑(∏ k, u k ^ ε k) = ∏ k, φ ↑(u k) ^ ε k := by
  have key : ∀ x : Rˣ, φ ↑x = ((Units.map φ.toMonoidHom x : ℂˣ) : ℂ) := fun _ => rfl
  rw [key, map_prod, Units.coe_prod]
  simp only [map_zpow, Units.val_zpow_eq_zpow_val, key]

theorem vtf_val_prodU (p : Sp ℂ ⟶ Y) {V : Y.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : K → Γ(Y, V)ˣ) (ε : K → ℤ) :
    valAt' p V (∏ k, u k ^ ε k).val = ∏ k, valAt' p V (u k).val ^ ε k := by
  simp only [valAt', dif_pos h]
  unfold valAt
  simp only [← RingHom.comp_apply]
  exact valprod_lemma _ u ε

theorem vtf_val_lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p _ ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  calc valAt' p _ ((LB.LinComb L φ ε).g j j').val
      = valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j')
          (∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
            (inf_le_right.trans (LB.wchart_le L φ j' k)) :
              LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU (φ k) _ (L.g (j k) (j' k)))) ^ ε k).val := rfl
    _ = ∏ k, valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j')
          (res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
            (inf_le_right.trans (LB.wchart_le L φ j' k)) :
              LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU (φ k) _ (L.g (j k) (j' k)))).val ^ ε k := vtf_val_prodU p h _ ε
    _ = _ := Finset.prod_congr rfl fun k _ => by
        exact congrArg (· ^ ε k) ((vtf_val_res (U := φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) p _ h _).trans
          (vtf_val_pullU p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k))))


theorem vtf_isGen_val (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Sp ℂ ⟶ Y) (j j' : K → L.ι) (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p _ (t.s j).val =
      (∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' p _ (t.s j').val := by
  have h' : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') := h
  calc valAt' p _ (t.s j).val
      = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
          (res (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j)).val :=
        (vtf_val_res p _ h' _).symm
    _ = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
          ((LB.LinComb L φ ε).g j j' *
            res (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j')).val := by
        rw [ht j j']
    _ = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') ((LB.LinComb L φ ε).g j j').val *
          valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
            (res (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j')).val := by
        rw [Units.val_mul, valAt'_mul]
    _ = _ := by rw [vtf_val_lcg L φ ε p j j' h, vtf_val_res p _ h']


end LC

section Liou

variable {g : ℕ}


end Liou

structure VtFr {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) where
  e : (Fin g → ℂ) → (Over.mk x0 ⟶ A)
  lat : AddSubgroup (Fin g → ℂ)
  span : Submodule.span ℝ (lat : Set (Fin g → ℂ)) = ⊤
  e_add : ∀ z w, e (z + w) = e z * e w
  e_ker : ∀ z, e z = 1 ↔ z ∈ lat
  hol : IsHolFam (fun z => (e z).left)
  Hm : Matrix (Fin g) (Fin g) ℂ
  χ : (Fin g → ℂ) → ℂ
  fr : L.L.ι → (Fin g → ℂ) → ℂ
  fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ L.L.U j}
  fr_ne : ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ L.L.U j → fr j z ≠ 0
  fr_g : ∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
    fr j z = valAt' (e z).left _ (L.L.g j j').val * fr j' z
  fr_0 : ∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ L.L.U j →
    fr j 0 = valAt' x0 ((L.L.pull (eSec A)).U (fun _ => j)) (L.rig.s (fun _ => j)).val
  χ_norm : ∀ a ∈ lat, ‖χ a‖ = 1
  fr_per : ∀ a ∈ lat, ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ L.L.U j →
    fr j z = χ a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
