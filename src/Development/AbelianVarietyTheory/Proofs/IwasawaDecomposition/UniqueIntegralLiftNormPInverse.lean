import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharEqOfEqOnTorsionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDlogUniqueModuloPStatement

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsCharExt

theorem exists_hom_extend {G A : Type} [CommGroup G] [CommGroup A]
    (hA : ∀ n : ℕ, n ≠ 0 → ∀ a : A, ∃ b : A, b ^ n = a) (q : ℕ) (χ : G → A)
    (hχ : ∀ g g', g ^ q = 1 → g' ^ q = 1 → χ (g * g') = χ g * χ g') :
    ∃ κ : G →* A, ∀ g, g ^ q = 1 → κ g = χ g := by
  let T : Subgroup G := (powMonoidHom q : G →* G).ker
  let f : T →* A := MonoidHom.mk' (fun g => χ g) fun g g' => hχ g g' g.2 g'.2
  letI : DivisibleBy (Additive A) ℕ := divisibleByOfSMulRightSurj (Additive A) ℕ fun {n} hn a => by
    obtain ⟨b, hb⟩ := hA n hn a.toMul
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  letI : DivisibleBy (Additive A) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨k, hk⟩ := (Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom
    (MonoidHom.toAdditive T.subtype) (fun a b h => Subtype.ext h) (MonoidHom.toAdditive f)
  refine ⟨MonoidHom.toAdditive.symm k, fun g hg => ?_⟩
  exact DFunLike.congr_fun hk (Additive.ofMul (⟨g, hg⟩ : T))

section Ring

variable (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]

def intV : ValuationSubring C where
  toSubring := intO C
  mem_or_inv_mem' := fun x => by
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      change ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

theorem intO_valuationRing : ValuationRing ↥(intO C) := inferInstanceAs (ValuationRing ↥(intV C))

theorem intO_isFractionRing : IsFractionRing ↥(intO C) C := inferInstanceAs (IsFractionRing ↥(intV C) C)

theorem intO_units_root [IsAlgClosed C] (n : ℕ) (hn : n ≠ 0) (a : (↥(intO C))ˣ) : ∃ b : (↥(intO C))ˣ, b ^ n = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ↥(intO C)) : C) (Nat.pos_of_ne_zero hn)
  have h1 : ‖z‖ ≤ 1 := by
    have h : ‖((a : ↥(intO C)) : C)‖ ≤ 1 := (a : ↥(intO C)).2
    rw [← hz, norm_pow] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hn).1 h
  have h2 : (⟨z, h1⟩ : ↥(intO C)) ^ n = a := Subtype.ext hz
  have h3 : IsUnit (⟨z, h1⟩ : ↥(intO C)) := (isUnit_pow_iff hn).1 (h2 ▸ a.isUnit)
  exact ⟨h3.unit, Units.ext h2⟩

end Ring

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def pull {S S' : Scheme.{0}} {a : S ⟶ X} {a' : S' ⟶ X} (g : S' ⟶ S) (h : g ≫ a = a') :
    (Over.mk a ⟶ t.G) →* (Over.mk a' ⟶ t.G) where
  toFun w := (Over.homMk g h : Over.mk a' ⟶ Over.mk a) ≫ w
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

theorem pull_left {S S' : Scheme.{0}} {a : S ⟶ X} {a' : S' ⟶ X} (g : S' ⟶ S) (h : g ≫ a = a')
    (w : Over.mk a ⟶ t.G) : (pull t g h w).left = g ≫ w.left := rfl

theorem exists_char_of_finPart {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    (e : R ≃+* R') (x : Sp R ⟶ X) (q : ℕ) {B : Type} [CommRing B] [Algebra R' B]
    (u : Over.mk (spMap (algebraMap R' B) ≫ spMap (e : R →+* R') ≫ x) ⟶ t.G)
    (hu : IsFinPart t (spMap (e : R →+* R') ≫ x) q u)
    (hall : ∀ (S : Type) [CommRing S] [Algebra R S] [Module.Finite R S]
      (w : Over.mk (spMap (algebraMap R S) ≫ x) ⟶ t.G), w ^ q = 1 →
        Thru t u.left ((algebraMap R S).comp (e.symm : R' →+* R)) w.left)
    (κ : (Over.mk (spMap (algebraMap R R) ≫ x) ⟶ t.G) →* Rˣ) :
    ∃ c : TorsChar t x q, ∀ w, w ^ q = 1 → c.χ R w = κ w := by
  classical
  have he : ∀ (S : Type) [CommRing S] (φ : R →+* S),
      spMap (φ.comp (e.symm : R' →+* R)) ≫ spMap (e : R →+* R') ≫ x = spMap φ ≫ x := fun S _ φ => by
    rw [← Category.assoc, ← sp_comp]
    congr 2
    ext r; simp
  let pt : (B →ₐ[R'] R') → (Over.mk (spMap (algebraMap R R) ≫ x) ⟶ t.G) := fun σ =>
    pull t (spMap ((e.symm : R' →+* R).comp σ.toRingHom)) (by
      rw [← he R, ← Category.assoc, ← sp_comp]
      congr 2
      ext r; simp) u
  have hP : spMap (e.symm : R' →+* R) ≫ spMap (RingHom.id R') ≫ spMap (e : R →+* R') ≫ x =
      spMap (algebraMap R R) ≫ x := by
    rw [← he R, ← Category.assoc, ← sp_comp]
  have hpt : ∀ (σ : B →ₐ[R'] R') (w : Over.mk (spMap (RingHom.id R') ≫ spMap (e : R →+* R') ≫ x) ⟶ t.G),
      spMap σ.toRingHom ≫ u.left = w.left → pt σ = pull t _ hP w := fun σ w h => by
    ext1
    rw [pull_left, pull_left, ← h, sp_comp, Category.assoc]
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.T.torsion_character_cocycle_descent E H X t R' (spMap (e : R →+* R') ≫ x) q B u hu
    (fun σ => Units.map (e : R →* R') (κ (pt σ))) (fun σ σ' σ'' w w' h h' h'' => by
      rw [hpt _ _ h, hpt _ _ h', hpt _ _ h'', map_mul, map_mul, map_mul])
  let χ : ∀ (S : Type) [CommRing S] [Algebra R S] [Module.Finite R S],
      (Over.mk (spMap (algebraMap R S) ≫ x) ⟶ t.G) → Sˣ := fun S _ _ _ w =>
    if h : Thru t u.left ((algebraMap R S).comp (e.symm : R' →+* R)) w.left then
      Units.map (h.choose : B →* S) b else 1
  have hχ : ∀ (S : Type) [CommRing S] [Algebra R S] [Module.Finite R S]
      (w : Over.mk (spMap (algebraMap R S) ≫ x) ⟶ t.G) (β : B →+* S),
      β.comp (algebraMap R' B) = (algebraMap R S).comp (e.symm : R' →+* R) → spMap β ≫ u.left = w.left →
      (χ S w : S) = β b := fun S _ _ _ w β h₁ h₂ => by
    have h : Thru t u.left ((algebraMap R S).comp (e.symm : R' →+* R)) w.left := ⟨β, h₁, h₂⟩
    have h₃ : h.choose = β := hu.mono S _ _ (h.choose_spec.1.trans h₁.symm) (h.choose_spec.2.trans h₂.symm)
    simp only [χ, dif_pos h, h₃]
    rfl
  refine ⟨⟨χ, ?_, ?_⟩, ?_⟩
  · intro S _ _ _ w w' hw hw'
    obtain ⟨β, h₁, h₂⟩ := hall S w hw
    obtain ⟨β', h₁', h₂'⟩ := hall S w' hw'
    obtain ⟨β'', h₁'', h₂''⟩ := hall S (w * w') (by rw [mul_pow, hw, hw', _root_.one_mul])
    have hc : 𝟙 _ ≫ spMap (algebraMap R S) ≫ x =
        spMap ((algebraMap R S).comp (e.symm : R' →+* R)) ≫ spMap (e : R →+* R') ≫ x := by
      rw [he, Category.id_comp]
    ext
    rw [Units.val_mul, hχ S _ β h₁ h₂, hχ S _ β' h₁' h₂', hχ S _ β'' h₁'' h₂'']
    refine hb₂ S _ (pull t _ hc w) (pull t _ hc w') β β' β'' h₁ h₁' h₁'' ?_ ?_ ?_
    · rw [pull_left, Category.id_comp, h₂]
    · rw [pull_left, Category.id_comp, h₂']
    · rw [← map_mul, pull_left, Category.id_comp, h₂'']
  · intro S S' _ _ _ _ _ _ φ w w' hw h
    obtain ⟨β, h₁, h₂⟩ := hall S w hw
    rw [hχ S _ β h₁ h₂, hχ S' w' (φ.toRingHom.comp β) ?_ ?_]
    · rfl
    · rw [RingHom.comp_assoc, h₁]
      ext r; simp
    · rw [sp_comp, Category.assoc, h₂, h]
  · intro w hw
    obtain ⟨β, h₁, h₂⟩ := hall R w hw
    let σ : B →ₐ[R'] R' :=
      { (e : R →+* R').comp β with
        commutes' := fun r => by
          have := RingHom.congr_fun h₁ r
          simp only [RingHom.comp_apply] at this
          simp [this] }
    have h₃ : pt σ = w := by
      ext1
      rw [pull_left, ← h₂]
      congr 2
      ext r; simp [σ]
    ext
    apply e.injective
    refine (congrArg e (hχ R w β h₁ h₂)).trans ((hb₁ σ).trans ?_)
    rw [h₃]; rfl

theorem exists_char [IsLocallyNoetherian X] {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R]
    [IsLocalRing R] [IsAlgClosed (FractionRing R)] (x : Sp R ⟶ X) (q : ℕ) (hq : q ≠ 0)
    (κ : (Over.mk (spMap (algebraMap R R) ≫ x) ⟶ t.G) →* Rˣ) :
    ∃ c : TorsChar t x q, ∀ w, w ^ q = 1 → c.χ R w = κ w := by
  obtain ⟨f, B, _, _, u, hf, hu, hfib⟩ := GlobalTheory.T.exists_local_finite_torsion_splitting E H X t R x q hq (GlobalTheory.T.splitTors_algClosed_fraction_field E H X t R x q hq)
    (IsLocalRing.maximalIdeal R) inferInstance
  have hf' : IsUnit f := by simpa using hf
  let e : R ≃+* Localization.Away f :=
    (IsLocalization.atUnits R (Submonoid.powers f) (S := Localization.Away f)
      (Submonoid.powers_le.2 hf')).toRingEquiv
  have hee : (e : R →+* Localization.Away f) = algebraMap R _ := rfl
  haveI : IsDomain (Localization.Away f) := e.symm.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed (Localization.Away f) := IsIntegrallyClosed.of_equiv e
  refine exists_char_of_finPart t e x q u hu ?_ κ
  intro S _ _ _ w hw
  have hc : 𝟙 _ ≫ spMap (algebraMap R S) ≫ x =
      spMap ((algebraMap R S).comp (e.symm : Localization.Away f →+* R)) ≫
        spMap (algebraMap R (Localization.Away f)) ≫ x := by
    rw [Category.id_comp, ← Category.assoc, ← sp_comp, ← hee]
    congr 2
    ext r; simp
  have h := hu.isOpen S _ (pull t _ hc w) (by rw [← map_pow, hw, map_one]) fun 𝔪 h𝔪 => by
    letI := Ideal.Quotient.field 𝔪
    have hd : spMap (Ideal.Quotient.mk 𝔪) ≫ spMap ((algebraMap R S).comp (e.symm : Localization.Away f →+* R)) ≫
        spMap (algebraMap R (Localization.Away f)) ≫ x =
        spMap ((Ideal.Quotient.mk 𝔪).comp ((algebraMap R S).comp (e.symm : Localization.Away f →+* R))) ≫
        spMap (algebraMap R (Localization.Away f)) ≫ x := by
      rw [sp_comp _ (Ideal.Quotient.mk 𝔪), Category.assoc]
    refine hfib (S ⧸ 𝔪) _ ?_ (pull t _ hd (pull t _ hc w)) (by rw [← map_pow, ← map_pow, hw, map_one, map_one])
    rw [← IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) 𝔪), ← hee]
    ext r
    rw [RingHom.mem_ker, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  rwa [pull_left, Category.id_comp] at h

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q q' : ℕ), q' ≠ 0 → q ∣ q' → ∀ c : TorsChar t x q, ∃ c' : TorsChar t x q', ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c'.χ B w = c.χ B w := by
  intro E _ _ _ H X _ t C _ _ _ _ x q q' hq' hd c
  haveI := intO_valuationRing C
  haveI := intO_isFractionRing C
  haveI : IsIntegrallyClosed ↥(intO C) := inferInstanceAs (IsIntegrallyClosed ↥(intV C))
  haveI : IsAlgClosed (FractionRing ↥(intO C)) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv ↥(intO C) C).symm.toRingEquiv
  obtain ⟨κ, hκ⟩ := exists_hom_extend (intO_units_root C) q (c.χ ↥(intO C)) (c.mul ↥(intO C))
  obtain ⟨c', hc'⟩ := exists_char t x q' hq' κ
  obtain ⟨m, rfl⟩ := hd
  have up : ∀ {M : Type} [Monoid M] (g : M), g ^ q = 1 → g ^ (q * m) = 1 := fun g h => by
    rw [pow_mul, h, one_pow]
  let c'' : TorsChar t x q :=
    ⟨c'.χ, fun B _ _ _ g g' h h' => c'.mul B g g' (up g h) (up g' h'),
      fun B B' _ _ _ _ _ _ φ g g' h h' => c'.nat B B' φ g g' (up g h) h'⟩
  exact ⟨c', GlobalTheory.T.torsionChar_eq_of_eq_on_torsion E H X t C x q (left_ne_zero_of_mul hq') c'' c fun w hw =>
    (hc' w (up w hw)).trans (hκ w hw)⟩

end GlobalTheory.TorsCharExt
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionChar_extends_divisible_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q q' : ℕ), q' ≠ 0 → q ∣ q' → ∀ c : TorsChar t x q, ∃ c' : TorsChar t x q', ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c'.χ B w = c.χ B w := by
  first | exact @GlobalTheory.TorsCharExt.exists_extension | exact GlobalTheory.TorsCharExt.exists_extension | (intros; apply GlobalTheory.TorsCharExt.exists_extension <;> assumption)
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Ring

variable {O : Type} [CommRing O] {x : Sp O ⟶ X}

theorem base_eq (x : Sp O ⟶ X) (I : Ideal O) : spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x =
    spMap (algebraMap (O ⧸ I) (DualNumber (O ⧸ I))) ≫ spMap (Ideal.Quotient.mk I) ≫ x := by
  rw [← Category.assoc, Guard.sp_comp]

theorem red_ex (I : Ideal O) {v : Sp (DualNumber O) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x) ⟶ t.G,
      w.left = spMap (dualMap (Ideal.Quotient.mk I)) ≫ v :=
  ⟨Over.homMk (spMap (dualMap (Ideal.Quotient.mk I)) ≫ v)
    ((GlobalTheory.FactorDepth.isTanAtG_map t (Ideal.Quotient.mk I) hv).1.trans (base_eq x I).symm), rfl⟩

theorem red_tors (I : Ideal O) {q : ℕ} (hq : (q : O) ∈ I) {v : Sp (DualNumber O) ⟶ t.G.left} (hv : IsTanAtG t x v)
    (w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x) ⟶ t.G)
    (hw : w.left = spMap (dualMap (Ideal.Quotient.mk I)) ≫ v) : w ^ q = 1 := by
  have hv' := GlobalTheory.FactorDepth.isTanAtG_map t (Ideal.Quotient.mk I) hv
  have h0 := smT_zero_ovT hv'
  have key : ∀ n : ℕ, smT _ (n : O ⧸ I) (ovT hv') = ovT hv' ^ n := fun n => by
    induction n with
    | zero => rw [Nat.cast_zero, pow_zero]; exact h0
    | succ n ih => rw [Nat.cast_succ, smT_add _ _ h0, ih, smT_unit, pow_succ]
  have hq0 : (q : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hq
  have h1 : ovT hv' ^ q = 1 := by rw [← key, hq0, h0]
  let δ : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x) ⟶ tEpsG (spMap (Ideal.Quotient.mk I) ≫ x) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans (base_eq x I).symm)
  have h2 : w = Formalism.L2.Pj.preHom δ (ovT hv') := Over.OverMorphism.ext (hw.trans (Category.id_comp _).symm)
  rw [h2, ← map_pow, h1, map_one]

def res {q q' : ℕ} (h : q ∣ q') (c : TorsChar t x q') : TorsChar t x q where
  χ := c.χ
  mul B _ _ _ g g' hg hg' := by
    obtain ⟨k, rfl⟩ := h
    exact c.mul B g g' (by rw [pow_mul, hg, one_pow]) (by rw [pow_mul, hg', one_pow])
  nat B B' _ _ _ _ _ _ φ g g' hg hg' := by
    obtain ⟨k, rfl⟩ := h
    exact c.nat B B' φ g g' (by rw [pow_mul, hg, one_pow]) hg'

theorem dlog_down {p k n : ℕ} (hk : k ≤ n) (c : TorsChar t x (p ^ n)) (c₁ : TorsChar t x (p ^ k))
    (hc : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
      (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G), w ^ (p ^ k) = 1 → c.χ B w = c₁.χ B w)
    {g : ℕ} {e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i)) {D : Fin g → O}
    (hD : DlogIs t p n c e D) : DlogIs t p k c₁ e D := by
  intro a v hav w hw
  have hv := Guard.comb_tan he hav
  obtain ⟨w', hw'⟩ := red_ex (Ideal.span {(p : O) ^ n}) hv
  have hle : Ideal.span {(p : O) ^ n} ≤ Ideal.span {(p : O) ^ k} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hk)
  let φ : DualNumber (O ⧸ Ideal.span {(p : O) ^ n}) →ₐ[O] DualNumber (O ⧸ Ideal.span {(p : O) ^ k}) :=
    { dualMap (Ideal.Quotient.factor hle) with
      commutes' := fun r => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl'] }
  have h1 := c.nat _ _ φ w' w (red_tors _ (by rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _) hv w' hw') (by
    rw [hw, hw', ← Category.assoc, Guard.sp_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [dualMap, φ])
  rw [← hc _ w (red_tors _ (by rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _) hv w hw), h1]
  have h2 := hD a v hav w' hw'
  have h3 : ∀ z, (φ z).snd = Ideal.Quotient.factor hle z.snd := fun z => by simp [φ, dualMap]
  rw [h3, h2, Ideal.Quotient.factor_mk]

end Ring

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp ↥(intO C) ⟶ X}

theorem coords {g : ℕ} {e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)} (he : IsTanBasis t x e) {a : Fin g → C}
    {w : Sp (DualNumber C) ⟶ t.G.left}
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) a w) (s : C)
    {vO : Sp (DualNumber ↥(intO C)) ⟶ t.G.left} (hv : IsTanAtG t x vO)
    (hs : spMap (dualMap (intO C).subtype) ≫ vO = spMap (epsMul s) ≫ w) :
    ∃ b : Fin g → ↥(intO C), IsCombAtG t x e b vO ∧ ∀ i, (b i : C) = s * a i := by
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have h := he.2 _ (RingHom.id ↥(intO C)) vO
  simp only [h1, h3, Category.id_comp] at h
  obtain ⟨b, hb, -⟩ := h hv
  have heC := fun j => GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (he.1 j)
  have h4 := Guard.comb_smul heC hw s
  rw [← hs] at h4
  exact ⟨b, hb, congrFun ((he.2 C _ _ (GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hv)).unique
    (GlobalTheory.LatDRFree.comb_map t (intO C).subtype hb) h4)⟩

theorem mem_latHT_iff : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [CompleteSpace C], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (x : Sp ↥(intO C) ⟶ X), (∀ x' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ x' = spMap (intO C).subtype ≫ x → x' = x) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)), IsTanBasis t x e → ∀ (n : ℕ) (h : Fin n → Fin g → ↥(intO C)), (∀ c : TorsChar t x (p ^ 1), ∃ j, DlogIs t p 1 c e (h j)) → (∀ j, ∃ c : TorsChar t x (p ^ 1), DlogIs t p 1 c e (h j)) → ∀ (a : Fin g → C) (w : Sp (DualNumber C) ⟶ t.G.left), IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) a w → (w ∈ latHT t p (spMap (intO C).subtype ≫ x) ↔ (∀ j, ‖∑ i, (h j i : C) * a i‖ ≤ 1) ∧ ∀ i, ‖(p : C) * a i‖ ≤ 1) := by
  intro hB E _ _ _ H X _ t p hp C _ _ _ _ _ hn x hx g e he n h hc hj a w hw
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  constructor
  · intro hL
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
    have hpa : ∀ i, ‖(p : C) * a i‖ ≤ 1 := by
      obtain ⟨x', hx', vO, hv, hs⟩ := hB E H X t p C hn x hx w hL p (by
        rw [hn, ← Real.rpow_neg_one]
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
        rw [div_le_one (by linarith)]
        linarith)
      obtain rfl := hx x' hx'
      obtain ⟨b, -, hb⟩ := coords he hw _ hv hs
      exact fun i => hb i ▸ (b i).2
    refine ⟨fun j => ?_, hpa⟩
    obtain ⟨x', hx', m, vO, hv, hs, hd⟩ := hL
    obtain rfl := hx x' hx'
    obtain ⟨b, hbv, hb⟩ := coords he hw _ hv hs
    show _ ∈ intO C
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h j i).2 ?_
      have := (b i).2
      rwa [hb, pow_zero, _root_.one_mul] at this
    obtain ⟨c, hcj⟩ := hj j
    obtain ⟨c', hc'⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H X t C x' (p ^ 1) (p ^ m) (pow_ne_zero _ hp.out.ne_zero) (pow_dvd_pow _ hm) c
    obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x' p m c' g e he.1
    have hδ := (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x' p 1 c g e he.1).2 D (h j) (dlog_down hm c' c hc' he.1 hD) hcj
    choose δ hδ using fun i => Ideal.mem_span_singleton'.1 (hδ i)
    obtain ⟨w', hw'⟩ := red_ex (Ideal.span {(p : ↥(intO C)) ^ m}) hv
    have h1 := hd m c' w' hw'
    have h2 : (p : ↥(intO C) ⧸ Ideal.span {(p : ↥(intO C)) ^ m}) ^ m = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [hD b vO hbv w' hw', h2, Ideal.span_singleton_zero, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
    have h3 : ∑ i, (D i : C) * a i = r := by
      apply mul_right_cancel₀ (pow_ne_zero m hp0)
      have := congrArg (intO C).subtype hr
      simp only [map_mul, map_pow, map_natCast, map_sum, Subring.subtype_apply, hb] at this
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h4 : ∑ i, (h j i : C) * a i = r - ∑ i, (δ i : C) * ((p : C) * a i) := by
      rw [← h3, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrArg (intO C).subtype (hδ i)
      simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply] at this
      linear_combination (a i) * this
    rw [h4]
    exact Subring.sub_mem _ r.2 (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (δ i).2 (hpa i))
  · rintro ⟨h1, h2⟩
    let b : Fin g → ↥(intO C) := fun i => ⟨(p : C) * a i, h2 i⟩
    obtain ⟨vO, hv, hbv⟩ := Guard.exists_comb he.1 b
    have heC := fun j => GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (he.1 j)
    refine ⟨x, rfl, 1, vO, hv, ?_, fun k c w' hw' => ?_⟩
    · rw [pow_one]
      exact Guard.comb_unique heC (GlobalTheory.LatDRFree.comb_map t (intO C).subtype hbv) (Guard.comb_smul heC hw p)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (↥(intO C) ⧸ Ideal.span {(p : ↥(intO C)) ^ 0}) := by
        rw [Ideal.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one]
      rw [Subsingleton.elim (TrivSqZeroExt.snd _) 0]
      exact Ideal.zero_mem _
    obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p k c g e he.1
    obtain ⟨j, hcj⟩ := hc (res (pow_dvd_pow p hk) c)
    have hδ := (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p 1 _ g e he.1).2 D (h j)
      (dlog_down hk c _ (fun _ _ _ _ _ _ => rfl) he.1 hD) hcj
    choose δ hδ using fun i => Ideal.mem_span_singleton'.1 (hδ i)
    let s : ↥(intO C) := ⟨∑ i, (h j i : C) * a i, h1 j⟩
    have h3 : ∑ i, D i * b i = (s + ∑ i, δ i * b i) * (p : ↥(intO C)) ^ 1 := by
      apply (intO C).subtype_injective
      simp only [map_mul, map_pow, map_natCast, map_sum, map_add, Subring.subtype_apply, s, b]
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrArg (intO C).subtype (hδ i)
      simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply] at this
      linear_combination (-(p : C) * a i) * this
    rw [hD b vO hbv w' hw', h3, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.HTLevel
end
