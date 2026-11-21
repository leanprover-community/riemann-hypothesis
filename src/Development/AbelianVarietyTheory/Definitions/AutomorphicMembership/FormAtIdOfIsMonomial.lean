import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef.StepCheck

section Fun

variable {O : Type} [CommRing O]

def posMin (O : Type) [CommRing O] : InvFun O where
  toFun n B := max 0 ((InvFun.minVal O).toFun n B)
  inv n m r hr B := by rw [(InvFun.minVal O).inv n m r hr]
  zero B := by rw [(InvFun.minVal O).zero, max_self]








variable {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]


variable {bar : O → O} {φ φ' : InvFun O}




end Fun

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)





variable {H} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


end CM

section Cones

variable {R : Type} [CommRing R] [IsDomain R] {Dg : DegPre R}


theorem inCone_of_isMonomial {m : ℕ} {t : Fin m → R} {γ : Fin m → LinearMap.BilinForm ℤ Dg.X}
    (hs : ∀ i y z, γ i y z = γ i z y) (h : IsMonomial Dg t γ) : InCone Dg γ := by
  intro W _ _ _ hW ϖ hϖ f be hbe hf
  have := hW.1
  classical
  let c : Fin m → ℕ := fun i => if h0 : f (t i) = 0 then 0 else
    (IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ).choose
  have hc : ∀ i, f (t i) ≠ 0 → Associated (f (t i)) (ϖ ^ c i) := fun i h0 => by
    simp only [c, dif_neg h0]
    exact (IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ).choose_spec
  have diag : ∀ y, be y y = ∑ i, (c i : ℤ) * γ i y y := fun y => by
    obtain ⟨r, n, hr, hn, ha⟩ := hf y
    obtain ⟨u, k, hk, rfl⟩ := h.coord hr
    have hne : f (u * ∏ i, t i ^ k i) ≠ 0 := ha.ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero)
    rw [map_mul, map_prod] at ha hne
    have h1 : Associated (∏ i, f (t i ^ k i)) (∏ i, ϖ ^ (c i * k i)) := Associated.prod _ _ _ fun i _ => by
      rcases Nat.eq_zero_or_pos (k i) with h0 | h0
      · simp [h0]
      · have : f (t i ^ k i) ≠ 0 := fun e => hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) e, mul_zero])
        rw [map_pow] at this ⊢
        rw [pow_mul]
        exact (hc i fun e => this (by rw [e, zero_pow h0.ne'])).pow_pow
    rw [Finset.prod_pow_eq_pow_sum] at h1
    have h2 : Associated (ϖ ^ n) (ϖ ^ ∑ i, c i * k i) :=
      ha.symm.trans ((associated_unit_mul_left _ _ (u.isUnit.map f)).trans h1)
    have h3 : n = ∑ i, c i * k i := by
      have := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 h2
      rw [hϖ.addVal_pow, hϖ.addVal_pow] at this
      exact_mod_cast this
    rw [hn, h3]
    simp only [hk]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨fun i => c i, fun i => (c i).cast_nonneg, LinearMap.ext₂ fun a b => ?_⟩
  have e : be a b = ∑ i, (c i : ℤ) * γ i a b := by
    have h1 := diag (a + b)
    simp only [map_add, LinearMap.add_apply, diag a, diag b, hbe b a, mul_add, Finset.sum_add_distrib, hs _ b a] at h1
    linarith
  simp [LinearMap.sum_apply, e]


end Cones

end GlobalTheory.TorRef.StepCheck
