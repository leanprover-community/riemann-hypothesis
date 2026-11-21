import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottComplex.StSpecOf

universe u v

namespace PIW.ENSpec

open MvPolynomial RingTheory.Sequence
open scoped Pointwise

section General

variable {S : Type u} [CommRing S]




theorem forall₂_ofFn {α β : Type*} {P : α → β → Prop} :
    ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → β), (∀ i, P (f i) (g i)) →
      List.Forall₂ P (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (forall₂_ofFn _ _ fun i => h i.succ)

end General

section Piece

variable {R : Type u} [CommRing R] {D : ℕ}

local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))

theorem homog_mem_pow {a : ℕ} {p : MvPolynomial (Fin D) R} (hp : p.IsHomogeneous a) : p ∈ 𝔛 ^ a := by
  rw [show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff]
  intro d hd
  have h0 := hp (mem_support_iff.1 hd)
  have h1 : d.degree = a := by rw [Finsupp.degree_eq_weight_one]; exact h0
  omega

theorem homog_mem_pow_succ {a : ℕ} {p : MvPolynomial (Fin D) R} (hp : p.IsHomogeneous a)
    (h : p ∈ 𝔛 ^ (a + 1)) : p = 0 := by
  rw [show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff] at h
  ext d
  by_contra hne
  have h0 := hp hne
  have h1 : d.degree = a := by rw [Finsupp.degree_eq_weight_one]; exact h0
  have h2 := h d (mem_support_iff.2 hne)
  omega


noncomputable def gmap (a : ℕ) : (MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) →ₗ[MvPolynomial (Fin D) R]
    (MvPolynomial (Fin D) R ⧸ 𝔛 ^ a) :=
  Submodule.factor (Ideal.pow_le_pow_right (Nat.le_succ a))

theorem gmap_mk (a : ℕ) (p : MvPolynomial (Fin D) R) :
    gmap a (Submodule.Quotient.mk p) = Submodule.Quotient.mk p :=
  Submodule.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ a)) p


noncomputable def emb (a : ℕ) : homogeneousSubmodule (Fin D) R a →+ LinearMap.ker (gmap (R := R) (D := D) a) where
  toFun h := ⟨Submodule.Quotient.mk h.1, by
    rw [LinearMap.mem_ker, gmap_mk, Submodule.Quotient.mk_eq_zero]; exact homog_mem_pow h.2⟩
  map_zero' := by ext; simp
  map_add' h h' := by ext; simp

theorem emb_injective (a : ℕ) : Function.Injective (emb (R := R) (D := D) a) := by
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  have h1 : (Submodule.Quotient.mk h.1 : MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) = 0 :=
    congrArg Subtype.val hh
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact Subtype.ext (homog_mem_pow_succ h.2 h1)

theorem emb_surjective (a : ℕ) : Function.Surjective (emb (R := R) (D := D) a) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearMap.mem_ker, gmap_mk, Submodule.Quotient.mk_eq_zero] at hq
  refine ⟨⟨homogeneousComponent a p, homogeneousComponent_mem a p⟩, ?_⟩
  apply Subtype.ext
  change (Submodule.Quotient.mk (homogeneousComponent a p) : MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) =
    Submodule.Quotient.mk p
  rw [Submodule.Quotient.eq, show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff']
  rw [show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff'] at hq
  intro d hd
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : d.degree = a
  · simp [h]
  · have : d.degree < a := by omega
    simp [h, hq d this]

theorem emb_smul (a : ℕ) (x : Fin D → R) (i : Fin D) (h : homogeneousSubmodule (Fin D) R a) :
    emb a ((-x i) • h) = (MvPolynomial.X i - MvPolynomial.C (x i)) • emb a h := by
  apply Subtype.ext
  change (Submodule.Quotient.mk ((-x i) • h.1) : MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) =
    (MvPolynomial.X i - MvPolynomial.C (x i)) • Submodule.Quotient.mk h.1
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_C_mul, smul_eq_mul]
  have : MvPolynomial.C (-x i) * h.1 - (MvPolynomial.X i - MvPolynomial.C (x i)) * h.1 =
      -(MvPolynomial.X i * h.1) := by rw [map_neg]; ring
  rw [this, pow_succ']
  exact neg_mem (Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (homog_mem_pow h.2))


end Piece


end PIW.ENSpec
