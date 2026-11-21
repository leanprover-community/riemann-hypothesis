import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordModel

open AlgebraicGeometry CategoryTheory

variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]

def gen : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A Ω))

def pr (p : Spec (CommRingCat.of A)) : PrimeSpectrum A := p

def toSt (p : Spec (CommRingCat.of A)) : A →+* (Spec (CommRingCat.of A)).presheaf.stalk p :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec (CommRingCat.of A)).presheaf.germ ⊤ p trivial).hom

theorem isLoc (p : Spec (CommRingCat.of A)) :
    letI := (toSt A p).toAlgebra
    IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk p) (pr A p).asIdeal :=
  StructureSheaf.IsLocalization.to_stalk A (pr A p)

set_option backward.isDefEq.respectTransparency false in
theorem genMap_toSt (p : Cpt (gen A Ω)) (a : A) :
    genMap (gen A Ω) p (toSt A p.1 a) = algebraMap A Ω a := by
  have h1 := (Spec (CommRingCat.of A)).presheaf.germ_stalkSpecializes (U := ⊤) (y := p.1) trivial p.2
  have h2 := Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of A) (S := CommRingCat.of Ω)
    (CommRingCat.ofHom (algebraMap A Ω))
  have h3 : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Spec (CommRingCat.of A)).presheaf.germ ⊤ p.1 trivial) ≫
      ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (gen A Ω)) =
      CommRingCat.ofHom (algebraMap A Ω) := by
    rw [Category.assoc, ← Category.assoc ((Spec (CommRingCat.of A)).presheaf.germ ⊤ p.1 trivial), h1]
    erw [h2]
    simp
  exact congrArg (fun f => f.hom a) h3

theorem mem_regAt (p : Cpt (gen A Ω)) (a : Ω) :
    a ∈ regAt (gen A Ω) p ↔ ∃ r s : A, s ∉ (pr A p.1).asIdeal ∧ a * algebraMap A Ω s = algebraMap A Ω r := by
  letI := (toSt A p.1).toAlgebra
  haveI := isLoc A p.1
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj ((pr A p.1).asIdeal).primeCompl t
    refine ⟨r, s, s.2, ?_⟩
    rw [← genMap_toSt A Ω p, ← genMap_toSt A Ω p, ← map_mul]
    exact congrArg _ h
  · rintro ⟨r, s, hs, h⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units ((Spec (CommRingCat.of A)).presheaf.stalk p.1)
      (⟨s, hs⟩ : ((pr A p.1).asIdeal).primeCompl)
    refine ⟨toSt A p.1 r * ↑u⁻¹, ?_⟩
    have e : genMap (gen A Ω) p u = algebraMap A Ω s := by
      rw [hu]; exact genMap_toSt A Ω p s
    have e2 : genMap (gen A Ω) p u * genMap (gen A Ω) p ↑u⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [map_mul, genMap_toSt, ← h, ← e, mul_assoc, e2, mul_one]

variable [IsDomain A] [IsFractionRing A Ω]

theorem genPt_asIdeal : (pr A (genPt (gen A Ω))).asIdeal = ⊥ := by
  ext a
  change algebraMap A Ω a ∈ IsLocalRing.maximalIdeal Ω ↔ _
  simp

theorem spec_all (q : Spec (CommRingCat.of A)) : genPt (gen A Ω) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes (R := A) _ _).1 ?_
  change (pr A (genPt (gen A Ω))).asIdeal ≤ (pr A q).asIdeal
  rw [genPt_asIdeal]; exact bot_le



omit [IsDomain A] [IsFractionRing A Ω] in
theorem inv_mem {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤) (c : κ) (S : Subring Ω)
    (hA : ∀ a, algebraMap A Ω a ∈ S) (hS : ∀ j, algebraMap A Ω (x j) / algebraMap A Ω (x c) ∈ S) :
    (algebraMap A Ω (x c))⁻¹ ∈ S := by
  have key : ∀ a ∈ Ideal.span (Set.range x), algebraMap A Ω a / algebraMap A Ω (x c) ∈ S := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a h => obtain ⟨j, rfl⟩ := h; exact hS j
    | zero => simpa using S.zero_mem
    | add a b _ _ ha hb => rw [map_add, add_div]; exact S.add_mem ha hb
    | smul r a _ ha => rw [smul_eq_mul, map_mul, mul_div_assoc]; exact S.mul_mem (hA r) ha
  simpa using key 1 (hx ▸ Submodule.mem_top)

omit [IsDomain A] [IsFractionRing A Ω] in
theorem algebraMap_mem_regAt (p : Cpt (gen A Ω)) (a : A) : algebraMap A Ω a ∈ regAt (gen A Ω) p :=
  ⟨_, genMap_toSt A Ω p a⟩

theorem inChart_iff {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤) (c : κ) (p : Cpt (gen A Ω)) :
    InChart (gen A Ω) (fun j => algebraMap A Ω (x j)) c p ↔ x c ∉ (pr A p.1).asIdeal := by
  constructor
  · rintro ⟨h0, h⟩ hc
    obtain ⟨r, s, hs, e⟩ := (mem_regAt A Ω p _).1 (inv_mem A Ω hx c _ (algebraMap_mem_regAt A Ω p) h)
    have : s = x c * r := by
      apply IsFractionRing.injective A Ω
      rw [map_mul, ← e]; field_simp
    exact hs (this ▸ Ideal.mul_mem_right _ _ hc)
  · intro hc
    have h0 : algebraMap A Ω (x c) ≠ 0 := by
      intro h
      have : x c = 0 := by simpa using h
      exact hc (this ▸ Ideal.zero_mem _)
    exact ⟨h0, fun j => (mem_regAt A Ω p _).2 ⟨x j, x c, hc, by field_simp⟩⟩





section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X}

theorem valAt_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  obtain ⟨_, s', e, rfl⟩ := h'
  rw [hξ.inj ⟨centre z, hz⟩ e]

theorem valAt_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t * t', map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_inv {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : a ≠ 0 ∧ ValAt ξ z a⁻¹ ↑r⁻¹ := by
  obtain ⟨hz, t, rfl, e⟩ := h
  have ht : IsUnit t := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit t (by have := r.isUnit; rw [← e] at this; exact this)
  obtain ⟨u, rfl⟩ := ht
  refine ⟨(u.isUnit.map (genMap ξ ⟨centre z, hz⟩)).ne_zero, hz, ↑u⁻¹, map_units_inv _ u, ?_⟩
  refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
  rw [← e]
  exact (map_mul _ _ _).symm.trans ((congrArg _ u.mul_inv).trans (map_one _))

theorem exists_coordsAt {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (hz : genPt ξ ⤳ centre z)
    (h : ∀ k, ∃ c, InChart ξ (fun i => y ⟨k, i⟩) c ⟨centre z, hz⟩) (hξ : IsCptGen ξ) :
    ∃ w, CoordsAt ξ y z w := by
  choose c hc using h
  have hv : ∀ j : Σ k, ι k, ∃ r, ValAt ξ z (y j / y ⟨j.1, c j.1⟩) r := by
    rintro ⟨k, i⟩
    obtain ⟨s, hs⟩ := (hc k).2 i
    exact ⟨_, hz, s, hs, rfl⟩
  choose w hw using hv
  refine ⟨w, fun k => ⟨c k, ?_⟩, fun k d hd => ?_⟩
  · have h1 : ValAt ξ z 1 1 := ⟨hz, 1, map_one _, map_one _⟩
    have h2 := hw ⟨k, c k⟩
    rw [div_self (hc k).1] at h2
    rw [valAt_unique hξ h2 h1]; exact isUnit_one
  · obtain ⟨u, hu⟩ := hd
    have h1 := hw ⟨k, d⟩
    rw [← hu] at h1
    obtain ⟨h0, h2⟩ := valAt_inv h1
    have hd0 : y ⟨k, d⟩ ≠ 0 := fun e => h0 (by simp [e])
    refine ⟨hd0, fun i => ⟨w ⟨k, i⟩ * ↑u⁻¹, ?_, by rw [← hu]; simp⟩⟩
    have h3 := valAt_mul (hw ⟨k, i⟩) h2
    have hc0 : y ⟨k, c k⟩ ≠ 0 := (hc k).1
    convert h3 using 1
    field_simp




end General

end GlobalTheory.CompanionTheory.Ar.CoordModel
