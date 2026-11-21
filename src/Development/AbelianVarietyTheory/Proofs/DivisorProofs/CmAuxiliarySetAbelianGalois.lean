import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliarySetFieldDataCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbeddingStatement

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.XiSize

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

variable (R : Subring ℂ) [IsDiscreteValuationRing R]

theorem ord_nonneg {y : FractionRing R} (hy : y ≠ 0)
    (h : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) y ≤ 1) : 0 ≤ ord_vw R y := by
  unfold ord_vw
  have h0 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) y ≠ 0 := by simpa using hy
  have e := WithZero.exp_log h0
  rw [← e, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

theorem ord_inv (y : FractionRing R) : ord_vw R y⁻¹ = - ord_vw R y := by
  unfold ord_vw
  rw [map_inv₀, WithZero.log_inv]

theorem ord_nonneg_of_mem {y : FractionRing R} (hy : y ≠ 0) (r : R) (hr : algebraMap R (FractionRing R) r = y) :
    0 ≤ ord_vw R y := by
  refine ord_nonneg R hy ?_
  rw [← hr]
  exact (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one r

theorem xi_size : GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (R : Subring ℂ) [IsDiscreteValuationRing R],
    GlobalTheory.LatModel.IsPlaceRing E l lam R → ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (ξ : E) (e₀ : ℤˣ), ξ ∈ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polPos φ e₀ (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y) →
      GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y)) ξ →
      ξ ≠ 0 ∧ ∀ σ : E →+* FractionRing R, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ 0 := by
  intro hPM E _ _ _ I _ d φ hFD 𝔣 h𝔣 l _ Q hQ hQl y hy lam R _ hR j hj ξ e₀ hξ hgen
  obtain ⟨-, -, hUn, -, -, -, hCM, -⟩ := hFD
  obtain ⟨hne, hint, -⟩ := (hPM E hUn I φ hCM e₀).2 𝔣 Q h𝔣 hQ l Fact.out hQl y hy ξ hξ hgen
  refine ⟨hne, fun σ => ?_⟩
  have hl : l.Prime := Fact.out
  have hσ : σ ξ ≠ 0 := (map_ne_zero σ).2 hne
  obtain ⟨n, hn, hI⟩ := hint (j.comp σ)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' ((Nat.coprime_zero_left l).1 hn)
  have hnd : ¬ l ∣ n := (Nat.Prime.coprime_iff_not_dvd hl).1 hn.symm

  have e1 : (n : ℂ) * ((j.comp σ) ξ)⁻¹ = j ((n : FractionRing R) * (σ ξ)⁻¹) := by
    simp [map_inv₀]
  have hIR : IsIntegral R ((n : FractionRing R) * (σ ξ)⁻¹) := by
    obtain ⟨p, hp, hev⟩ := hI
    refine ⟨p.map (Int.castRingHom R), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    apply j.injective
    rw [Polynomial.hom_eval₂, ← e1, map_zero]
    have hs : j.comp ((algebraMap R (FractionRing R)).comp (Int.castRingHom R)) = algebraMap ℤ ℂ := Subsingleton.elim _ _
    rw [hs]
    exact hev
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hIR

  have hq : (((1 / n : ℚ)) : ℂ) ∈ R := hR.2.2.1 _ (by
    rw [one_div, padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]; simp)
  set u : R := ⟨_, hq⟩
  have hun : u * (n : R) = 1 := by
    apply Subtype.ext
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    simp [u]
    field_simp
  have e2 : algebraMap R (FractionRing R) (u * r) = (σ ξ)⁻¹ := by
    rw [map_mul, hr, ← _root_.mul_assoc, ← map_natCast (algebraMap R (FractionRing R)), ← map_mul, hun, map_one, _root_.one_mul]
  have h1 : ord_vw R (σ ξ) ≤ 0 := by
    have := ord_nonneg_of_mem R (inv_ne_zero hσ) _ e2
    rw [ord_inv] at this
    omega
  have hl0 : (l : FractionRing R) ≠ 0 := by
    rw [← map_natCast (algebraMap R (FractionRing R))]
    refine (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ?_
    intro h
    have := congrArg Subtype.val h
    simp [hl.ne_zero] at this
  have h2 : 0 ≤ ord_vw R (l : FractionRing R) :=
    ord_nonneg_of_mem R hl0 (l : R) (map_natCast _ _)
  unfold val_vp
  rw [if_neg hσ]
  have h3 : ((ord_vw R (σ ξ) : ℚ) / (ord_vw R (l : FractionRing R) : ℚ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact_mod_cast h3

end GlobalTheory.XiSize
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliary_set_l_adic_place : GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (R : Subring ℂ) [IsDiscreteValuationRing R],
    GlobalTheory.LatModel.IsPlaceRing E l lam R → ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (ξ : E) (e₀ : ℤˣ), ξ ∈ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polPos φ e₀ (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y) →
      GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y)) ξ →
      ξ ≠ 0 ∧ ∀ σ : E →+* FractionRing R, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ 0 := by
  atlas_forward_decl GlobalTheory.XiSize.xi_size
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem val_vp_sqrt_neg_prime : ∀ (E : Type) [Field E] (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R],
    (l : R) ∈ IsLocalRing.maximalIdeal R → (∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : R)) →
    ∀ (d : ℕ), d.Prime → ∀ (δ : E), δ ^ 2 = -(d : E) → ∀ σ : E →+* FractionRing R,
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ δ) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
  intro E _ l _ R _ _ _ _ hl hu d hd δ hδ σ
  have hK : ∀ n : ℕ, n ≠ 0 → (n : FractionRing R) ≠ 0 := fun n hn => by
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (Nat.cast_ne_zero.2 hn)
  have hsq : (σ δ) ^ 2 = -(d : FractionRing R) := by rw [← map_pow, hδ, map_neg, map_natCast]
  have hx : σ δ ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hsq
    exact hK d hd.ne_zero hsq
  have h2 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (d : FractionRing R) = 2 * GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ δ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw
    rw [show (d : FractionRing R) = -((σ δ) ^ 2) by rw [hsq, neg_neg], Valuation.map_neg, map_pow, WithZero.log_pow]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  by_cases hld : l = d
  · subst hld
    have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
    have h1 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (l : FractionRing R) < 1 := by
      rw [← map_natCast (algebraMap R (FractionRing R)), IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hl
    have h2' : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (l : FractionRing R) ≠ 0 := by
      simpa using hK l hl0
    have h3 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (l : FractionRing R) ≠ 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw
      intro h4
      have := WithZero.exp_log h2'
      rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
      exact h1.ne this.symm
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ δ) ≠ 0 := by
      intro h6; rw [h2, h6, mul_zero] at h3; exact h3 rfl
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, if_neg hx, if_pos rfl, h2]
    congr 1
    push_cast
    field_simp
  · have hunit : IsUnit (d : R) := hu d hd (Ne.symm hld)
    have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (d : FractionRing R) = 1 := by
      rw [← map_natCast (algebraMap R (FractionRing R)), IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact fun hm => (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ hm hunit)
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (d : FractionRing R) = 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw; rw [hv]; simp
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ δ) = 0 := by omega
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, if_neg hx, if_neg hld, h5]
    simp

end GlobalTheory
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_sqrt_neg_prime : ∀ (E : Type) [Field E] (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R],
    (l : R) ∈ IsLocalRing.maximalIdeal R → (∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : R)) →
    ∀ (d : ℕ), d.Prime → ∀ (δ : E), δ ^ 2 = -(d : E) → ∀ σ : E →+* FractionRing R,
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ δ) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
  atlas_forward_decl GlobalTheory.val_vp_sqrt_neg_prime
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValArith
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem ord_mul (x y : FractionRing R) (hx : x ≠ 0) (hy : y ≠ 0) :
    ord_vw R (x * y) = ord_vw R x + ord_vw R y := by
  unfold ord_vw
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]
  ring

theorem ord_inv (x : FractionRing R) (hx : x ≠ 0) : ord_vw R x⁻¹ = -ord_vw R x := by
  have h := ord_mul x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx] at h
  have h1 : ord_vw R (1 : FractionRing R) = 0 := by simp [ord_vw]
  omega

theorem ord_unit (u : Rˣ) : ord_vw R (algebraMap R (FractionRing R) (u : R)) = 0 := by
  unfold ord_vw
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.2 fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm u.isUnit]
  simp

theorem ord_pos (l : ℕ) (hm : (l : R) ∈ IsLocalRing.maximalIdeal R) (h0 : (l : R) ≠ 0) :
    0 < ord_vw R ((l : ℕ) : FractionRing R) := by
  have h0' : ((l : ℕ) : FractionRing R) ≠ 0 := by
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h0
  have h1 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) ((l : ℕ) : FractionRing R) < 1 := by
    rw [← map_natCast (algebraMap R (FractionRing R)), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hm
  have h2 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) ((l : ℕ) : FractionRing R) ≠ 0 := by
    simpa using h0'
  rw [← WithZero.exp_log h2, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold ord_vw
  omega

theorem val_sq_div_ge : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ),
    (l : R) ∈ IsLocalRing.maximalIdeal R → (l : R) ≠ 0 →
    ∀ (a b δ : FractionRing R) (u : Rˣ) (ca cd : ℚ), a ≠ 0 → b ≠ 0 → δ ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l a ≤ (ca : WithTop ℚ) → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l b ≤ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l δ = (cd : WithTop ℚ) →
      ((-(ca + cd) : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l ((algebraMap R (FractionRing R) (u : R)) ^ 2 / (a * (δ * b))) := by
  intro R _ _ _ l hm h0 a b δ u ca cd ha hb hd hva hvb hvd
  have hL := ord_pos (R := R) l hm h0
  set L : ℚ := (ord_vw R ((l : ℕ) : FractionRing R) : ℚ) with hLdef
  have hLq : (0 : ℚ) < L := by rw [hLdef]; exact_mod_cast hL
  set w := algebraMap R (FractionRing R) (u : R) with hw
  have hw0 : w ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 u.ne_zero
  have hx0 : w ^ 2 / (a * (δ * b)) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero 2 hw0) (mul_ne_zero ha (mul_ne_zero hd hb))
  have hord : ord_vw R (w ^ 2 / (a * (δ * b))) = -(ord_vw R a + ord_vw R δ + ord_vw R b) := by
    rw [div_eq_mul_inv, pow_two, ord_mul _ _ (mul_ne_zero hw0 hw0) (inv_ne_zero (mul_ne_zero ha (mul_ne_zero hd hb))),
      ord_mul _ _ hw0 hw0, ord_inv _ (mul_ne_zero ha (mul_ne_zero hd hb)), ord_mul _ _ ha (mul_ne_zero hd hb),
      ord_mul _ _ hd hb, hw, ord_unit]
    ring
  simp only [val_vp, if_neg ha, if_neg hb, if_neg hd, if_neg hx0] at hva hvb hvd ⊢
  rw [← hLdef] at hva hvb hvd ⊢
  have h1 : (ord_vw R a : ℚ) / L ≤ ca := by exact_mod_cast hva
  have h2 : (ord_vw R b : ℚ) / L ≤ 0 := by exact_mod_cast hvb
  have h3 : (ord_vw R δ : ℚ) / L = cd := by exact_mod_cast hvd
  rw [hord]
  have e : ((-(ord_vw R a + ord_vw R δ + ord_vw R b) : ℤ) : ℚ) / L
      = -((ord_vw R a : ℚ) / L) - (ord_vw R δ : ℚ) / L - (ord_vw R b : ℚ) / L := by
    push_cast; ring
  rw [e]
  exact_mod_cast (by linarith : -(ca + cd) ≤ -((ord_vw R a : ℚ) / L) - (ord_vw R δ : ℚ) / L - (ord_vw R b : ℚ) / L)

end GlobalTheory.ValArith
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_lower_bound_product : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ),
    (l : R) ∈ IsLocalRing.maximalIdeal R → (l : R) ≠ 0 →
    ∀ (a b δ : FractionRing R) (u : Rˣ) (ca cd : ℚ), a ≠ 0 → b ≠ 0 → δ ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l a ≤ (ca : WithTop ℚ) → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l b ≤ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l δ = (cd : WithTop ℚ) →
      ((-(ca + cd) : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l ((algebraMap R (FractionRing R) (u : R)) ^ 2 / (a * (δ * b))) := by
  atlas_forward_decl GlobalTheory.ValArith.val_sq_div_ge
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CxPtSizes

theorem val_le_of_gen {E : Type} [Field E] [NumberField E] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ)
    (hl : (l : R) ∈ IsLocalRing.maximalIdeal R) (hl0 : (l : R) ≠ 0) (σ : E →+* FractionRing R) (ξ ξ' : E) (h0 : ξ' ≠ 0) (n : ℕ) (hn : IsUnit (n : R))
    (a : OF E) (h : (n : E) * ξ' = algebraMap (OF E) E a * ξ) :
    ξ ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ') := by
  have hn0 : (n : E) ≠ 0 := by
    intro h; have : n = 0 := by exact_mod_cast h
    subst this; simp at hn
  have hξ : ξ ≠ 0 := by rintro rfl; simp [hn0, h0] at h
  refine ⟨hξ, ?_⟩
  have hint : IsIntegral ℤ (algebraMap (OF E) E a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (IsScalarTower.toAlgHom ℤ (OF E) E)
  have hint2 : IsIntegral R (σ (algebraMap (OF E) E a)) :=
    IsIntegral.map_of_comp_eq (algebraMap ℤ R) σ (RingHom.ext_int _ _) hint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint2
  set v := (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) with hv
  have h1 : v (σ (algebraMap (OF E) E a)) ≤ 1 := hb ▸ HeightOneSpectrum.valuation_le_one _ _
  have h2 : v (σ (n : E)) = 1 := by
    have : σ (n : E) = algebraMap R (FractionRing R) (n : R) := by simp
    rw [this, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm hn
  have h3 : v (σ ξ') ≤ v (σ ξ) := by
    have := congrArg (fun x => v (σ x)) h
    simp only [map_mul, h2, _root_.one_mul] at this
    rw [this]; exact mul_le_of_le_one_left' h1
  have hs : σ ξ ≠ 0 := (map_ne_zero σ).2 hξ
  have hs' : σ ξ' ≠ 0 := (map_ne_zero σ).2 h0
  have hlK : (l : FractionRing R) = algebraMap R (FractionRing R) (l : R) := by simp
  have hlv : v (l : FractionRing R) < 1 := by rw [hlK, HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hl
  have hlv0 : v (l : FractionRing R) ≠ 0 := by
    rw [hlK]; exact (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hl0)
  have hpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (l : FractionRing R) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw; rw [← hv]; have := (WithZero.log_lt_log hlv0 one_ne_zero).2 hlv; simp at this; omega
  have hle : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ ξ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ ξ') := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw; rw [← hv]
    have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hs') ((Valuation.ne_zero_iff _).2 hs)).2 h3; omega
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, hs, hs', if_false, WithTop.coe_le_coe]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by exact_mod_cast hpos.le)

theorem scale_size : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt)
      (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      (∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x)) →
    ∀ (D : R) (cv : ℚ), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D)) = (cv : WithTop ℚ) → (cv : ℝ) = c_vp 𝔣 l →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
      (∀ i, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D))) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A) (w : I → ℂ), (∀ i, U.IsCMVec i (yv i) (w i)) →
      (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
      (∀ i, ((e i (hL.toLie X₀.rm (eH.symm (f' i))) : R) : ℂ) = a i * w i) →
    ∀ i, (Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2 ≠ 0 ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0)
        (a i * (a i * ((Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2) / (D : ℂ)) * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ := by
  intro hPC hADR hADC hPM E _ _ _ _ I _ d φ hFD 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hcm hα j hj φK hφK
    e a he hL n eH c₀ ψ₀ hc₀ hgen hpol hCM hψ₀ D cv hD hcv e' f' hgens hval m hm ψ hψ yv ev w hcmv hyc hec hew
  obtain ⟨ξ, hξgen, hrat⟩ := GlobalTheory.T.auxiliary_set_field_data_congruence hPC hADR hADC hPM E I d φ hFD 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK
    e a he hL n eH c₀ ψ₀ hc₀ hgen hpol hCM hψ₀ D cv hD hcv e' f' hgens hval m hm ψ hψ yv ev w hcmv hyc hec hew
  obtain ⟨j', hj', hchar, hlm, -, -, hSz⟩ := GlobalTheory.PlaceRingFacts.place_ring_facts E l lam R hR
  have hgenv : ξ ≠ 0 ∧ ∀ σ : E →+* FractionRing R, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ 0 := by
    have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
    obtain ⟨ξ', hp', hg'⟩ := (((hPM E hFD.2.2.1 I φ hFD.2.2.2.2.2.2.1 1).1 _ hc y).2.2.2 l Fact.out).1
    obtain ⟨h0', hv'⟩ := GlobalTheory.T.auxiliary_set_l_adic_place hPM E I d φ hFD 𝔣 h𝔣 l Q hQ hQl y hy lam R hR j hj ξ' 1 hp' hg'
    obtain ⟨n', hn', a', ha'⟩ := hξgen.2 ξ' hg'.1
    have hl0 : (l : R) ≠ 0 := by
      haveI := hchar; exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hu : IsUnit (n' : R) := by
      have hc := (Nat.isCoprime_iff_coprime.2 hn').map (Int.castRingHom R)
      simp only [eq_intCast, Int.cast_natCast] at hc
      obtain ⟨s, t, hst⟩ := hc
      by_contra hnu
      have : (1 : R) ∈ IsLocalRing.maximalIdeal R := hst ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 hnu)) (Ideal.mul_mem_left _ _ hlm)
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
    exact ⟨by rintro rfl; have : (n' : E) ≠ 0 := (fun h => by have : n' = 0 := (by exact_mod_cast h); subst this; simp at hu); simp [this, h0'] at ha',
      fun σ => (val_le_of_gen R l hlm hl0 σ ξ ξ' h0' n' hu a' ha').2.trans (hv' σ)⟩
  obtain ⟨hξ0, hξv⟩ := hgenv
  have hjj : j' = j := IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun x => by simp [hj, hj'])
  subst hjj
  obtain ⟨δ, hδ2, hδφ⟩ := hFD.2.2.2.2.2.2.2
  have hdp : d.Prime := hFD.1
  intro i
  set P0 : R := ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) with hP0def
  obtain ⟨r, hr⟩ := hψ₀ i (e' i) (hgens i).1
  have hP0c : ((P0 : R) : ℂ) = ((r : R) : ℂ) * (a i * w i) := by
    rw [hP0def, hr, ← hew i]; push_cast; ring
  have vtop : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (0 : FractionRing R) = ⊤ := by simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp]
  have hD0 : D ≠ 0 := by
    rintro rfl; rw [map_zero, vtop] at hD; exact WithTop.top_ne_coe hD
  have hvP : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) P0) ≤ (cv : WithTop ℚ) := hD ▸ (hval i).2
  have hP00 : P0 ≠ 0 := by
    intro h0; rw [h0, map_zero, vtop] at hvP; exact absurd hvP (by simp)
  have hD0c : (D : ℂ) ≠ 0 := fun h => hD0 (Subtype.ext h)
  have hP0c0 : ((P0 : R) : ℂ) ≠ 0 := fun h => hP00 (Subtype.ext h)
  have hr0 : ((r : R) : ℂ) ≠ 0 := fun h => r.ne_zero (Subtype.ext h)
  have hφξ : φ i ξ ≠ 0 := (map_ne_zero (φ i)).2 hξ0
  obtain ⟨hh0, hrat'⟩ := hrat i
  have hhc : ((U.h i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh0
  have hψ0 : ψ (ev i) (yv i) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hrat'
    exact mul_ne_zero hhc hP0c0 hrat'.symm
  have haw : a i * w i ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hP0c; exact hP0c0 hP0c
  have ha0 : a i ≠ 0 := left_ne_zero_of_mul haw
  have hw0 : w i ≠ 0 := right_ne_zero_of_mul haw
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
    exact_mod_cast this.ne'
  refine ⟨?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpi hhc) (div_ne_zero hD0c hψ0)) (pow_ne_zero _ hw0)
  · have hunit : ∀ q : ℕ, q.Prime → q ≠ l → IsUnit (q : R) := by
      intro q hq hql
      haveI := Fact.mk hq
      have hv : 0 ≤ padicValRat l ((q : ℚ)⁻¹) := by
        rw [padicValRat.inv, padicValRat.of_nat, padicValNat_primes (Ne.symm hql)]; simp
      have hmem := hR.2.2.1 _ hv
      refine IsUnit.of_mul_eq_one (b := ⟨_, hmem⟩) (Subtype.ext ?_)
      have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
      simp [hq0]
    have hl0 : (l : R) ≠ 0 := by
      haveI := hchar; exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      have : ((d : ℕ) : E) = 0 := by simpa using hδ2
      exact hdp.ne_zero (by exact_mod_cast this)
    haveI := hchar
    have hvδ := GlobalTheory.T.valuation_sqrt_neg_prime E l R hlm hunit d hdp δ hδ2 (φK i)
    have hz := GlobalTheory.T.valuation_lower_bound_product R l hlm hl0 (algebraMap R (FractionRing R) P0) (φK i ξ) (φK i δ) r cv (if l = d then 1 / 2 else 0)
      ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hP00) ((map_ne_zero (φK i)).2 hξ0)
      ((map_ne_zero (φK i)).2 hδ0) hvP (hξv (φK i)) hvδ
    have hS := hSz _ (cv + if l = d then 1 / 2 else 0) (by simpa using hz)
    have hφj : ∀ t : E, j' (φK i t) = φ i t := fun t => by rw [← hφK i]; rfl
    have key : j' ((algebraMap R (FractionRing R) (r : R)) ^ 2 / (algebraMap R (FractionRing R) P0 * (φK i δ * φK i ξ))) =
        (a i * (a i * ((Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2) / (D : ℂ)) * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ := by
      have h2I : (2 * Complex.I * φ i ξ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hφξ
      have hψv : ψ (ev i) (yv i) = (U.h i : ℂ) * ((P0 : R) : ℂ) / (2 * Complex.I * φ i ξ) := eq_div_of_mul_eq h2I hrat'
      rw [map_div₀, map_pow, map_mul, map_mul, hj', hj', hφj, hφj, hδφ i, hψv, hP0c]
      field_simp
    have hcast : (((cv + if l = d then 1 / 2 else 0 : ℚ)) : ℝ) = c_vp 𝔣 l + if l = d then 1 / 2 else 0 := by
      rw [Rat.cast_add, hcv]; split_ifs <;> norm_num
    rw [← hcast, ← key]; exact hS

end GlobalTheory.CxPtSizes
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_auxiliary_set_abelian_galois : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt)
      (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      (∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x)) →
    ∀ (D : R) (cv : ℚ), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D)) = (cv : WithTop ℚ) → (cv : ℝ) = c_vp 𝔣 l →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
      (∀ i, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D))) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A) (w : I → ℂ), (∀ i, U.IsCMVec i (yv i) (w i)) →
      (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
      (∀ i, ((e i (hL.toLie X₀.rm (eH.symm (f' i))) : R) : ℂ) = a i * w i) →
    ∀ i, (Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2 ≠ 0 ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0)
        (a i * (a i * ((Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2) / (D : ℂ)) * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ := by
  atlas_forward_decl GlobalTheory.CxPtSizes.scale_size
end
