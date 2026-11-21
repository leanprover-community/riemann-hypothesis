import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem jFK_self : jFK (R := R) (FractionRing R) = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

def rhoK : TF (R := R) F ⟶ TF (R := R) (FractionRing R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))) (by
    show _ ≫ (jFK (R := R) (FractionRing R) ≫ jK R) = jFK (R := R) F ≫ jK R
    rw [jFK_self, Category.id_comp])


variable (D : DegPre R)

abbrev bcA : DegPre.BF D F ⟶ DegPre.BF D (FractionRing R) := rhoK F ▷ D.P.A


theorem bcA_snd : bcA F D ≫ snd _ _ = snd _ _ := whiskerRight_snd _ _


theorem formBC (k : ℕ) (α : D.X) :
    FormEq (fun i => (bcA F D).left ≫ DegPre.famφ D (FractionRing R) α i) (DegPre.famε k)
      (DegPre.famφ D F α) (DegPre.famε k) := fun U _ h =>
  Finset.prod_congr rfl fun i _ => by
    dsimp only
    rw [GC.famφ_eq, GC.famφ_eq, ← Category.assoc, ← Over.comp_left, bcA_snd]


section Descent

open IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_hasVal {ϖ : V} (hϖ : Irreducible ϖ) (x : FractionRing V) (hx : x ≠ 0) : ∃ n : ℤ, HasVal ϖ x n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨m1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨m2, u2, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  refine ⟨(m1 : ℤ) - m2, u1 * u2⁻¹, ?_⟩
  have hp : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
    exact fun h => hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) h)
  have hu2 : algebraMap V (FractionRing V) (u2 : V) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
    exact fun h => u2.ne_zero (IsFractionRing.injective V (FractionRing V) h)
  have hinv : algebraMap V (FractionRing V) ((u2⁻¹ : Vˣ) : V) =
      (algebraMap V (FractionRing V) (u2 : V))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  simp only [Units.val_mul, map_mul, map_pow, hinv]
  rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast]
  field_simp


variable {D : DegData V (maximalIdeal V)} (F : Type) [Field F] [Algebra (FractionRing V) F]



end Descent

def NuDescentSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
  ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q →
  ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
  ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre (FractionRing V) k) (s' : Fam D.toPre F k),
    (∀ α (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (s'.s α) (𝟙 _) y J = sval (s.s α) (bcA F D.toPre).left y J) →
    NuGe D Q F v k s' 0 → NuGe D Q (FractionRing V) vK k s 0


end ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC
