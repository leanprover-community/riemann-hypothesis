import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsUnitIffCharpolyCoeffZeroNe
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimaryStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobiusStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenCuspidalCharsByRegularCharsProof
import GroundTheory.PAdicHodge.AInfGalois
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Development.DiscreteGroups.GlobalIrreducibility.DzKSchur
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

section
open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {F : Type} [Field F] [Finite F]

def tor (F : Type) [Field F] [Finite F] (n : ℕ) : Set (AlgebraicClosure F) :=
  {α | α ^ (Nat.card F ^ n - 1) = 1}

theorem N_pos {n : ℕ} (hn : 0 < n) : 0 < Nat.card F ^ n - 1 := by
  have := Nat.one_lt_pow hn.ne' (Finite.one_lt_card (α := F))
  omega

theorem tor_finite {n : ℕ} (hn : 0 < n) : (tor F n).Finite := by
  refine (Polynomial.nthRoots (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset ?_
  intro α hα
  exact (Polynomial.mem_nthRoots (N_pos hn)).2 hα

def hT (n : ℕ) (ψ : F → ℂ) (β : AlgebraicClosure F) : ℂ :=
  ψ (-((minpoly F β) ^ (n / (minpoly F β).natDegree)).nextCoeff)

def aC (n : ℕ) (θ : AlgebraicClosure F →* ℂ) (h : AlgebraicClosure F → ℂ) (l : ℕ) : ℂ :=
  ((Nat.card F ^ n - 1 : ℕ) : ℂ)⁻¹ * ∑ᶠ β ∈ tor F n, h β * star (θ β ^ l)

theorem theta_pow_N {n : ℕ} (θ : AlgebraicClosure F →* ℂ) {β : AlgebraicClosure F} (hβ : β ∈ tor F n) :
    θ β ^ (Nat.card F ^ n - 1) = 1 := by
  rw [← map_pow, show β ^ (Nat.card F ^ n - 1) = 1 from hβ, map_one]

theorem star_eq_inv_of_pow {c : ℂ} {N : ℕ} (hN : 0 < N) (hc : c ^ N = 1) : star c = c⁻¹ := by
  have h1 : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hc hN.ne'
  have h0 : c ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hc; exact zero_ne_one hc
  refine eq_inv_of_mul_eq_one_left ?_
  have : star c * c = ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  rw [this, Complex.normSq_eq_norm_sq, h1]; simp

open scoped Classical in

theorem sum_pow_star {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    {β β' : AlgebraicClosure F} (hβ : β ∈ tor F n) (hβ' : β' ∈ tor F n) :
    ∑ l ∈ Finset.range (Nat.card F ^ n - 1), θ β ^ l * star (θ β' ^ l) =
      if β = β' then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  have hN := N_pos (F := F) hn
  have e1 := theta_pow_N θ hβ
  have e2 := theta_pow_N θ hβ'
  have h0 : θ β' ≠ 0 := by
    intro h; rw [h, zero_pow hN.ne'] at e2; exact zero_ne_one e2
  have hs : star (θ β') = (θ β')⁻¹ := star_eq_inv_of_pow hN e2
  have hw : ∀ l, θ β ^ l * star (θ β' ^ l) = (θ β * (θ β')⁻¹) ^ l := by
    intro l; rw [star_pow, hs, mul_pow, inv_pow]
  simp_rw [hw]
  have hwN : (θ β * (θ β')⁻¹) ^ (Nat.card F ^ n - 1) = 1 := by
    rw [mul_pow, inv_pow, e1, e2, inv_one, one_mul]
  split_ifs with hb
  · subst hb
    rw [mul_inv_cancel₀ h0]; simp
  · have hne : θ β * (θ β')⁻¹ ≠ 1 := by
      intro h
      have h' : θ β = θ β' := by
        rw [mul_inv_eq_one₀ h0] at h; exact h
      have n0 : ∀ {x : AlgebraicClosure F}, x ∈ tor F n → x ≠ 0 := by
        intro x hx h; rw [h] at hx
        have : (0 : AlgebraicClosure F) ^ (Nat.card F ^ n - 1) = 1 := hx
        rw [zero_pow hN.ne'] at this; exact zero_ne_one this
      exact hb (hθ _ _ (n0 hβ) (n0 hβ') h')
    rw [geom_sum_eq hne, hwN, sub_self, zero_div]

theorem sum_aC {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (h : AlgebraicClosure F → ℂ)
    {β : AlgebraicClosure F} (hβ : β ∈ tor F n) :
    ∑ l ∈ Finset.range (Nat.card F ^ n - 1), aC n θ h l * θ β ^ l = h β := by
  classical
  have hT := tor_finite (F := F) hn
  have hN : ((Nat.card F ^ n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (N_pos hn).ne'
  unfold aC
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ hT, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ β' ∈ hT.toFinset, ∑ l ∈ Finset.range (Nat.card F ^ n - 1),
      ((Nat.card F ^ n - 1 : ℕ) : ℂ)⁻¹ * (h β' * star (θ β' ^ l)) * θ β ^ l =
      ((Nat.card F ^ n - 1 : ℕ) : ℂ)⁻¹ * h β' * (if β = β' then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0) := by
    intro β' hb'
    rw [← sum_pow_star hn θ hθ hβ ((Set.Finite.mem_toFinset hT).1 hb'), Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl e]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq hT.toFinset β, if_pos ((Set.Finite.mem_toFinset hT).2 hβ)]
  field_simp

theorem minpoly_pow_card (β : AlgebraicClosure F) (i : ℕ) :
    minpoly F (β ^ Nat.card F ^ i) = minpoly F β := by
  obtain ⟨f, hf⟩ := exists_algHom_pow_card_pow (F := F) i
  rw [← hf]
  exact minpoly.algHom_eq f f.toRingHom.injective β

theorem hT_pow_card (n : ℕ) (ψ : F → ℂ) (β : AlgebraicClosure F) (i : ℕ) :
    hT n ψ (β ^ Nat.card F ^ i) = hT n ψ β := by
  unfold hT; rw [minpoly_pow_card]

theorem pow_mem_tor {n : ℕ} {β : AlgebraicClosure F} (hβ : β ∈ tor F n) (m : ℕ) : β ^ m ∈ tor F n := by
  show (β ^ m) ^ (Nat.card F ^ n - 1) = 1
  rw [← pow_mul, mul_comm, pow_mul, show β ^ (Nat.card F ^ n - 1) = 1 from hβ, one_pow]

theorem expand_primary {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (ψ : F → ℂ)
    (P f : F[X]) (m : ℕ) (hf : f.Monic) (hirr : Irreducible f) (hm : 0 < m) (hP : P = f ^ m)
    (hdeg : P.natDegree = n) (h0 : P.coeff 0 ≠ 0) :
    (n : ℂ) * ψ (-P.nextCoeff) =
      ∑ l ∈ Finset.range (Nat.card F ^ n - 1), aC n θ (hT n ψ) l * rootSum θ l P := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F) f
    (degree_pos_of_irreducible hirr).ne'
  have hmin : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hirr hα hf
  have hd : f.natDegree * m = n := by rw [← hdeg, hP, hf.natDegree_pow, mul_comm]
  have hdpos : 0 < f.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)
  have hmq : n / f.natDegree = m := by rw [← hd, Nat.mul_div_cancel_left _ hdpos]
  have hf0 : f.coeff 0 ≠ 0 := by
    intro hc; apply h0
    rw [hP, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, hc, zero_pow hm.ne']
  have hα0 : α ≠ 0 := by
    rintro rfl; apply hf0; rwa [aeval_def, eval₂_at_zero, map_eq_zero_iff _ (algebraMap F _).injective] at hα
  have hαt : α ∈ tor F n := by
    have h1 : α ^ Nat.card F ^ n = α :=
      (minpoly_natDegree_dvd_iff_pow α n).1 (by rw [← hmin, ← hd]; exact Dvd.intro m rfl)
    show α ^ (Nat.card F ^ n - 1) = 1
    have h2 : α ^ (Nat.card F ^ n - 1) * α = α * 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow n (Nat.card F) Nat.card_pos), h1, mul_one]
    exact mul_left_cancel₀ hα0 (by rw [mul_comm] at h2; exact h2)
  have hPα : P = minpoly F α ^ (n / (minpoly F α).natDegree) := by rw [← hmin, hmq, hP]
  have hr := (GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum F θ n hn α hαt).2.2
  have hnc : ψ (-P.nextCoeff) = hT n ψ α := by unfold hT; rw [← hPα]
  rw [hnc, hPα]
  simp_rw [hr, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ i ∈ Finset.range n, ∑ l ∈ Finset.range (Nat.card F ^ n - 1),
      aC n θ (hT n ψ) l * θ (α ^ Nat.card F ^ i) ^ l = hT n ψ α := by
    intro i _
    rw [sum_aC hn θ hθ _ (pow_mem_tor hαt _), hT_pow_card]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end DiscreteGroups.sglob.DzType.Kon
end
end

section
open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {F : Type} [Field F] [Finite F]

theorem aC_mod {n : ℕ} (θ : AlgebraicClosure F →* ℂ) (h : AlgebraicClosure F → ℂ) (l : ℕ) :
    aC n θ h (l % (Nat.card F ^ n - 1)) = aC n θ h l := by
  unfold aC
  congr 1
  refine finsum_mem_congr rfl fun β hβ => ?_
  have e := theta_pow_N θ hβ
  conv_rhs => rw [← Nat.mod_add_div l (Nat.card F ^ n - 1), pow_add, pow_mul, e, one_pow, mul_one]

theorem aC_frob {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ) (ψ : F → ℂ) (k i : ℕ) :
    aC n θ (hT n ψ) (k * Nat.card F ^ i) = aC n θ (hT n ψ) k := by
  unfold aC
  congr 1
  obtain ⟨f, hf⟩ := exists_algHom_pow_card_pow (F := F) i
  have hmaps : Set.MapsTo (fun β : AlgebraicClosure F => β ^ Nat.card F ^ i) (tor F n) (tor F n) :=
    fun β hβ => pow_mem_tor hβ _
  have hinj : Set.InjOn (fun β : AlgebraicClosure F => β ^ Nat.card F ^ i) (tor F n) := by
    intro x _ y _ hxy
    have : f x = f y := by rw [hf, hf]; exact hxy
    exact f.toRingHom.injective this
  have hbij := ((tor_finite (F := F) hn).injOn_iff_bijOn_of_mapsTo hmaps).1 hinj
  refine finsum_mem_eq_of_bijOn (fun β : AlgebraicClosure F => β ^ Nat.card F ^ i) hbij fun β _ => ?_
  rw [hT_pow_card, map_pow, mul_comm k, pow_mul]

theorem sum_filter_aC {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ) (ψ : F → ℂ) (k : ℕ) :
    ∑ l ∈ Finset.range (Nat.card F ^ n - 1), star (aC n θ (hT n ψ) l) *
      (((Finset.range n).filter fun i => k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1]).card : ℂ) =
      (n : ℂ) * star (aC n θ (hT n ψ) k) := by
  classical
  have hN := N_pos (F := F) hn
  simp_rw [Finset.natCast_card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ i ∈ Finset.range n, ∑ l ∈ Finset.range (Nat.card F ^ n - 1),
      star (aC n θ (hT n ψ) l) * (if k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1] then (1 : ℂ) else 0) =
      star (aC n θ (hT n ψ) k) := by
    intro i _
    have e2 : ∀ l ∈ Finset.range (Nat.card F ^ n - 1),
        star (aC n θ (hT n ψ) l) * (if k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1] then (1 : ℂ) else 0) =
        if (k * Nat.card F ^ i) % (Nat.card F ^ n - 1) = l then star (aC n θ (hT n ψ) l) else 0 := by
      intro l hl
      have hl' : l % (Nat.card F ^ n - 1) = l := Nat.mod_eq_of_lt (Finset.mem_range.1 hl)
      by_cases hc : (k * Nat.card F ^ i) % (Nat.card F ^ n - 1) = l
      · rw [if_pos hc, if_pos (show k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1] by
          unfold Nat.ModEq; rw [hl', hc]), mul_one]
      · rw [if_neg hc, if_neg (show ¬ k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1] by
          unfold Nat.ModEq; rw [hl']; exact hc), mul_zero]
    rw [Finset.sum_congr rfl e2, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (Nat.mod_lt _ hN)),
      aC_mod, aC_frob hn]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem mass_eq_zero_of_not_primary (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hn : 0 < Module.finrank F V) (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (P : F[X])
    (hP : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) :
    mass (psi (rootSum θ k) V) P = 0 := by
  have hadd := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
  have hcl : IsClassFn (psi (rootSum θ k) V) := fun e g => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F _ V V e g
  unfold mass
  refine finsum_mem_of_eqOn_zero fun g hg => ?_
  have hg' : LinearMap.charpoly g = P := hg
  exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V _ hcl (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hadd) hn g (by rw [hg']; exact hP)

def polys (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] : Finset F[X] := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  exact (Set.finite_range (fun g : Module.End F V => LinearMap.charpoly g)).toFinset.filter
    (fun P => P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0})

theorem mem_polys {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {P : F[X]} :
    P ∈ polys (F := F) V ↔ (∃ g : Module.End F V, LinearMap.charpoly g = P) ∧
      P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0} := by
  unfold polys
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_range]

theorem finsum_mass_eq (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ : Module.End F V → ℂ) (X : F[X] → ℂ) :
    ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0}, mass φ P * X P =
      ∑ P ∈ polys (F := F) V, mass φ P * X P := by
  rw [finsum_mem_def]
  rw [finsum_eq_sum_of_support_subset _ (s := polys (F := F) V) ?_]
  · refine Finset.sum_congr rfl fun P hP => ?_
    rw [Set.indicator_of_mem (mem_polys.1 hP).2]
  · intro P hP
    rw [Function.mem_support] at hP
    rw [Finset.mem_coe, mem_polys]
    by_cases hS : P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0}
    · refine ⟨?_, hS⟩
      by_contra hc
      apply hP
      rw [Set.indicator_of_mem hS]
      have hm : mass φ P = 0 := by
        unfold mass
        exact finsum_mem_of_eqOn_zero fun g hg => absurd ⟨g, hg⟩ hc
      rw [hm, zero_mul]
    · exact absurd (Set.indicator_of_notMem hS _) hP

theorem ipGL_psi_trace (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hn : 0 < Module.finrank F V) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (k : ℕ) (ψ : F → ℂ) :
    ipGL (psi (rootSum θ k) V) (fun x => ψ (-(LinearMap.charpoly x).nextCoeff)) =
      glCard F (Module.finrank F V) * star (aC (Module.finrank F V) θ (hT (Module.finrank F V) ψ) k) := by
  classical
  have hl : ∀ l, ∑ P ∈ polys (F := F) V, mass (psi (rootSum θ k) V) P * star (rootSum θ l P) =
      glCard F (Module.finrank F V) * (((Finset.range (Module.finrank F V)).filter fun i =>
        k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ Module.finrank F V - 1]).card : ℂ) := by
    intro l
    rw [← finsum_mass_eq, ← ipGL_charpoly_eq_finsum_mass F V _ (rootSum θ l)]
    exact GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn k l
  rw [ipGL_charpoly_eq_finsum_mass F V _ (fun P => ψ (-P.nextCoeff)), finsum_mass_eq]
  set n := Module.finrank F V with hndef
  set φ := psi (rootSum θ k) V with hφ
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have key : ∀ P ∈ polys (F := F) V,
      mass φ P * star (ψ (-P.nextCoeff)) = (n : ℂ)⁻¹ * ∑ l ∈ Finset.range (Nat.card F ^ n - 1),
        star (aC n θ (hT n ψ) l) * (mass φ P * star (rootSum θ l P)) := by
    intro P hP
    obtain ⟨hPm, hPd, hP0⟩ := (mem_polys.1 hP).2
    by_cases hpr : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
    · obtain ⟨f, m, hf, hirr, hm, hPf⟩ := hpr
      have e := expand_primary hn θ hθ ψ P f m hf hirr hm hPf hPd hP0
      have e' : ψ (-P.nextCoeff) = (n : ℂ)⁻¹ *
          ∑ l ∈ Finset.range (Nat.card F ^ n - 1), aC n θ (hT n ψ) l * rootSum θ l P := by
        rw [← e]; field_simp
      rw [e', star_mul', star_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [star_mul', star_inv₀, star_natCast]; ring
    · rw [mass_eq_zero_of_not_primary V hn θ k P hpr]; simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [hl]
  have e2 : ∀ l ∈ Finset.range (Nat.card F ^ n - 1), star (aC n θ (hT n ψ) l) * (glCard F n *
      (((Finset.range n).filter fun i => k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1]).card : ℂ)) =
      glCard F n * (star (aC n θ (hT n ψ) l) *
      (((Finset.range n).filter fun i => k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1]).card : ℂ)) :=
    fun l _ => by ring
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, sum_filter_aC hn θ ψ k]
  field_simp

end DiscreteGroups.sglob.DzType.Kon
end
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.GLq
open scoped IntermediateField

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

theorem trace_eq_nextCoeff {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (y : Mt g n) :
    Matrix.trace y = -(LinearMap.charpoly (Matrix.toLin' y)).nextCoeff := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Matrix.charpoly_toLin', Matrix.trace_eq_neg_charpoly_coeff, nextCoeff_of_natDegree_pos,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hn

theorem trace_eq_hT {g n : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    [FiniteDimensional (ZMod g) K] (hfr : Module.finrank (ZMod g) K = n)
    (ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g)) (ψ : ZMod g → ℂ) (z : K) :
    hT n ψ (ι z) = ψ (Algebra.trace (ZMod g) K z) := by
  unfold hT
  rw [minpoly.algHom_eq ι ι.injective z, trace_eq_finrank_mul_minpoly_nextCoeff]
  have hint : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  have hfd : Module.finrank (ZMod g) (ZMod g)⟮z⟯ = (minpoly (ZMod g) z).natDegree :=
    IntermediateField.adjoin.finrank hint
  have htow := Module.finrank_mul_finrank (ZMod g) (ZMod g)⟮z⟯ K
  rw [hfd, hfr] at htow
  have hd1 : 0 < (minpoly (ZMod g) z).natDegree := minpoly.natDegree_pos hint
  have hr : n / (minpoly (ZMod g) z).natDegree = Module.finrank (ZMod g)⟮z⟯ K := by
    rw [← htow, Nat.mul_div_cancel_left _ hd1]
  rw [hr, (minpoly.monic hint).nextCoeff_pow, nsmul_eq_mul]
  congr 1
  ring

theorem aC_eq_gs {g n : ℕ} [Fact g.Prime] (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Nat.card K = g ^ n) (θ₀ : AlgebraicClosure (ZMod g) →* ℂ)
    (ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g)) (θ : Kˣ →* ℂˣ) (k : ℕ)
    (hlink : ∀ u : Kˣ, ((θ u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) ^ k) (ψ₀ : AddChar (ZMod g) Circle) :
    aC n θ₀ (hT n fun a => ((ψ₀ a : Circle) : ℂ)) k =
      ((g ^ n - 1 : ℕ) : ℂ)⁻¹ * ∑ᶠ z : Kˣ, ((θ⁻¹ z : ℂˣ) : ℂ) * ((ψ₀ (Algebra.trace (ZMod g) K (z : K)) : Circle) : ℂ) := by
  classical
  have hgp : g.Prime := Fact.out
  have hKpos : 0 < Nat.card K := by rw [hK]; exact pow_pos hgp.pos _
  have : Finite K := Nat.finite_of_card_ne_zero hKpos.ne'
  let _ : Fintype K := Fintype.ofFinite K
  have : FiniteDimensional (ZMod g) K := Module.Finite.of_finite
  have hcard : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hcard] at h1
    exact (Nat.pow_right_injective hgp.two_le h1).symm
  have hq : Nat.card (ZMod g) = g := Nat.card_zmod g
  have hU : Fintype.card Kˣ = g ^ n - 1 := by rw [Fintype.card_units, hcard]
  unfold aC
  rw [hq]
  congr 1
  have hN : 0 < g ^ n - 1 := by
    have := Nat.one_lt_pow hn.ne' hgp.one_lt; omega
  have htor : tor (ZMod g) n = {α | α ^ (g ^ n - 1) = 1} := by unfold tor; rw [hq]
  have hmaps : Set.MapsTo (fun z : Kˣ => ι (z : K)) Set.univ (tor (ZMod g) n) := by
    intro z _
    rw [htor]
    show ι (z : K) ^ (g ^ n - 1) = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hU, pow_card_eq_one, Units.val_one, map_one]
  have hinj : Set.InjOn (fun z : Kˣ => ι (z : K)) Set.univ :=
    fun x _ y _ h => Units.ext (ι.injective h)
  have hfinT : (tor (ZMod g) n).Finite := by
    rw [htor]
    refine (Polynomial.nthRoots (g ^ n - 1) (1 : AlgebraicClosure (ZMod g))).finite_toSet.subset ?_
    intro α hα
    exact (Polynomial.mem_nthRoots hN).2 hα
  have hsurj : Set.SurjOn (fun z : Kˣ => ι (z : K)) Set.univ (tor (ZMod g) n) := by
    have hsub : (fun z : Kˣ => ι (z : K)) '' Set.univ ⊆ tor (ZMod g) n := hmaps.image_subset
    have hle : (tor (ZMod g) n).ncard ≤ ((fun z : Kˣ => ι (z : K)) '' Set.univ).ncard := by
      have hinj' : Function.Injective (fun z : Kˣ => ι (z : K)) := fun x y h => Units.ext (ι.injective h)
      rw [Set.ncard_image_of_injective _ hinj', Set.ncard_univ,
        Nat.card_eq_fintype_card, hU]
      calc (tor (ZMod g) n).ncard
          ≤ ((Polynomial.nthRoots (g ^ n - 1) (1 : AlgebraicClosure (ZMod g))).toFinset : Set _).ncard := by
            refine Set.ncard_le_ncard (t := ((Polynomial.nthRoots (g ^ n - 1)
              (1 : AlgebraicClosure (ZMod g))).toFinset : Set (AlgebraicClosure (ZMod g)))) ?_ (Finset.finite_toSet _)
            intro α hα
            rw [htor] at hα
            exact Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots hN).2 hα)
        _ = (Polynomial.nthRoots (g ^ n - 1) (1 : AlgebraicClosure (ZMod g))).toFinset.card :=
            Set.ncard_coe_finset _
        _ ≤ (Polynomial.nthRoots (g ^ n - 1) (1 : AlgebraicClosure (ZMod g))).card := Multiset.toFinset_card_le _
        _ ≤ g ^ n - 1 := Polynomial.card_nthRoots _ _
    have heq := Set.eq_of_subset_of_ncard_le hsub hle hfinT
    rw [← heq]
    exact Set.surjOn_image _ _
  have hbij : Set.BijOn (fun z : Kˣ => ι (z : K)) Set.univ (tor (ZMod g) n) := ⟨hmaps, hinj, hsurj⟩
  rw [← finsum_mem_univ (fun z : Kˣ => ((θ⁻¹ z : ℂˣ) : ℂ) * ((ψ₀ (Algebra.trace (ZMod g) K (z : K)) : Circle) : ℂ))]
  symm
  refine finsum_mem_eq_of_bijOn (fun z : Kˣ => ι (z : K)) hbij fun z _ => ?_
  rw [trace_eq_hT hfr ι, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hlink z, mul_comm]
  congr 1
  have hpow : (θ₀ (ι (z : K)) ^ k) ^ (g ^ n - 1) = 1 := by
    rw [← hlink z, ← Units.val_pow_eq_pow_val, ← map_pow, ← hU, pow_card_eq_one, map_one, Units.val_one]
  exact (star_eq_inv_of_pow hN hpow).symm

end DiscreteGroups.sglob.DzType.Kon
end
end

section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.CuspGL
open scoped Classical

set_option linter.style.haveILetI false

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

open GlobalTheory.GreenRegular

theorem explicit_family : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d →
    ∃ (θ₀ : AlgebraicClosure (ZMod g) →* ℂ) (_ : ∀ x y : AlgebraicClosure (ZMod g), x ≠ 0 → y ≠ 0 → θ₀ x = θ₀ y → x = y)
      (ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g)) (kOf : (Kˣ →* ℂˣ) → ℕ),
      (∀ (θ : Kˣ →* ℂˣ) (u : Kˣ), ((θ u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) ^ kOf θ) ∧
      ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ,
      (∀ θ x, τ θ x = (-1) ^ (d - 1) *
        psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod g)))) ∧
      (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧
        ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 →
          τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧
      (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) := by
  intro g _ d hd K _ _ hK
  have hgp : g.Prime := Fact.out
  have hg : 0 < g := hgp.pos
  have hcF : Nat.card (ZMod g) = g := Nat.card_zmod g
  haveI : FiniteDimensional (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hK]
  have hcardU : Nat.card Kˣ = g ^ d - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
  have hN0 : 0 < g ^ d - 1 := by
    have := Nat.one_lt_pow hd.ne' hgp.one_lt
    omega
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField (ZMod g)
  let ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g) := IsAlgClosed.lift
  let lam : Kˣ →* ℂˣ := (Units.map θ₀).comp (Units.map (ι : K →* AlgebraicClosure (ZMod g)))
  have hlam : ∀ u : Kˣ, ((lam u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) := fun u => rfl
  have hlam_inj : Function.Injective lam := by
    intro u v h
    have h' := congrArg Units.val h
    rw [hlam, hlam] at h'
    exact Units.ext (ι.injective (hθ₀ _ _ ((map_ne_zero ι).2 u.ne_zero) ((map_ne_zero ι).2 v.ne_zero) h'))
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hprim : IsPrimitiveRoot (lam γ) (g ^ d - 1) := by
    rw [← hcardU, ← orderOf_eq_card_of_forall_mem_zpowers hγ, ← orderOf_injective lam hlam_inj γ]
    exact IsPrimitiveRoot.orderOf _
  have hmod : ∀ u : Kˣ, u ^ (g ^ d - 1) = 1 := fun u => by
    rw [← hcardU]; exact pow_card_eq_one'
  have hpow_eq : ∀ a b : ℕ, lam ^ a = lam ^ b ↔ a ≡ b [MOD g ^ d - 1] := by
    intro a b
    constructor
    · intro h
      have h1 := congrArg (fun f : Kˣ →* ℂˣ => f γ) h
      simp only [MonoidHom.pow_apply] at h1
      rwa [pow_eq_pow_iff_modEq, ← hprim.eq_orderOf] at h1
    · intro h
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.pow_apply, pow_eq_pow_iff_modEq]
      exact Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hmod, map_one])) h
  have hpow : ∀ θ : Kˣ →* ℂˣ, ∃ k, θ = lam ^ k := by
    intro θ
    have h1 : θ γ ^ (g ^ d - 1) = 1 := by rw [← map_pow, hmod, map_one]
    haveI : NeZero (g ^ d - 1) := ⟨hN0.ne'⟩
    have h1' : ((θ γ : ℂˣ) : ℂ) ^ (g ^ d - 1) = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨k, -, hk0⟩ := (IsPrimitiveRoot.coe_units_iff.2 hprim).eq_pow_of_pow_eq_one h1'
    have hk : lam γ ^ k = θ γ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk0)
    refine ⟨k, MonoidHom.ext fun u => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
    rw [map_zpow, map_zpow, MonoidHom.pow_apply, hk]
  let kOf : (Kˣ →* ℂˣ) → ℕ := fun θ => (hpow θ).choose
  have hkOf : ∀ θ, θ = lam ^ kOf θ := fun θ => (hpow θ).choose_spec
  have hreg : ∀ θ, IsRegularChar g d θ → ∀ i : ℕ, 0 < i → i < d →
      ¬ kOf θ * Nat.card (ZMod g) ^ i ≡ kOf θ [MOD Nat.card (ZMod g) ^ d - 1] := by
    intro θ hθ i hi hid hc
    rw [hcF] at hc
    have e : θ ^ g ^ i = θ ^ g ^ 0 := by
      rw [hkOf θ, ← pow_mul, ← pow_mul, pow_zero, mul_one]
      exact (hpow_eq _ _).2 hc
    exact absurd (hθ i 0 hid hd e) hi.ne'
  have hadd : ∀ k, IsAdditive (rootSum θ₀ k) := fun k => (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod g) θ₀ k).1
  have hfr : 0 < Module.finrank (ZMod g) (Fin d → ZMod g) := by rw [Module.finrank_fin_fun]; exact hd
  have hlink : ∀ (θ : Kˣ →* ℂˣ) (u : Kˣ), ((θ u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) ^ kOf θ := by
    intro θ u
    conv_lhs => rw [hkOf θ]
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hlam]
  refine ⟨θ₀, hθ₀, ι, kOf, hlink,
    fun θ x => (-1) ^ (d - 1) *
    psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod g))),
    fun θ x => rfl, fun θ hθ => ⟨?_, ?_, ?_⟩, fun θ θ' hθ hθ' => ?_⟩
  · exact GlobalTheory.ParamLabel.isCusp_psi θ₀ hθ₀ hd (hreg θ hθ)
  · show (-1) ^ (d - 1) * psi _ _ (Matrix.toLin' ((1 : Gn g d) : Matrix (Fin d) (Fin d) (ZMod g))) = _
    have h1 := GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico (ZMod g) (Fin d → ZMod g) (rootSum θ₀ (kOf θ)) (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod g) θ₀ (kOf θ)).2 hfr
    rw [Units.val_one, Matrix.toLin'_one, ← Module.End.one_eq_id, h1, Module.finrank_fin_fun, hcF,
      show ((-1 : ℂ)) ^ (d - 1) = ∏ i ∈ Finset.Ico 1 d, (-1 : ℂ) by rw [Finset.prod_const, Nat.card_Ico],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  · intro y hy z hz
    show (-1) ^ (d - 1) * psi _ _ _ = _
    have h := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible (ZMod g) (Fin d → ZMod g) _ (hadd (kOf θ)) (Matrix.toLin' (y : Mt g d))
      (by rw [Matrix.charpoly_toLin']; exact hy)
    rw [h, Matrix.charpoly_toLin']
    congr 1
    have hz' : aeval (ι (z : K)) (y : Mt g d).charpoly = 0 := by rw [aeval_algHom_apply, hz, map_zero]
    have hnd : (y : Mt g d).charpoly.natDegree = d := by simp
    change ((Formalism.CyclotomicNorms.rootsBar _).map _).sum = _
    rw [GlobalTheory.GreenExists.rootsBar_eq hy hz', hnd, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    conv_rhs => rw [hkOf θ]
    show θ₀ (ι ↑z ^ g ^ i) ^ kOf θ = _
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hlam, Units.val_pow_eq_pow_val, map_pow ι]
  · have hsign : ((-1 : ℂ) ^ (d - 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    have hunit : ∀ G : Module.End (ZMod g) (Fin d → ZMod g), IsUnit G →
        ∃ x : Gn g d, Matrix.toLin' (x : Mt g d) = G := by
      intro G hG
      have hM : IsUnit (LinearMap.toMatrix' G) :=
        hG.map (LinearMap.toMatrixAlgEquiv' : Module.End (ZMod g) (Fin d → ZMod g) ≃ₐ[ZMod g] Mt g d)
      exact ⟨hM.unit, by rw [IsUnit.unit_spec, Matrix.toLin'_toMatrix']⟩
    have hxU : ∀ x : Gn g d, IsUnit (Matrix.toLin' (x : Mt g d)) := fun x =>
      x.isUnit.map (Matrix.toLinAlgEquiv' : Mt g d ≃ₐ[ZMod g] Module.End (ZMod g) (Fin d → ZMod g))
    have heqU : ∀ k k' : ℕ, (∀ x : Gn g d, psi (rootSum θ₀ k) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) =
        psi (rootSum θ₀ k') (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d))) → ∀ l : ℕ,
        ipGL (psi (rootSum θ₀ k) (Fin d → ZMod g)) (fun G => rootSum θ₀ l (LinearMap.charpoly G)) =
          ipGL (psi (rootSum θ₀ k') (Fin d → ZMod g)) (fun G => rootSum θ₀ l (LinearMap.charpoly G)) := by
      intro k k' h l
      refine finsum_mem_congr rfl fun G hG => ?_
      obtain ⟨x, rfl⟩ := hunit G hG
      rw [h x]
    have hgram : ∀ k l : ℕ, ipGL (psi (rootSum θ₀ k) (Fin d → ZMod g))
        (fun G => rootSum θ₀ l (LinearMap.charpoly G)) = glCard (ZMod g) d *
          (((Finset.range d).filter fun i => k * g ^ i ≡ l [MOD g ^ d - 1]).card : ℂ) := by
      intro k l
      have h := GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius (ZMod g) (Fin d → ZMod g) θ₀ hθ₀ hfr k l
      rwa [Module.finrank_fin_fun, hcF] at h
    have hGL : glCard (ZMod g) d ≠ 0 := by
      unfold glCard
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    constructor
    · intro hτ
      have hx : ∀ x : Gn g d, psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) =
          psi (rootSum θ₀ (kOf θ')) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) :=
        fun x => mul_left_cancel₀ hsign (congrFun hτ x)
      have e1 := heqU _ _ hx (kOf θ')
      rw [hgram, hgram] at e1
      have h2 := mul_left_cancel₀ hGL e1
      have hmem : 0 ∈ (Finset.range d).filter fun i => kOf θ' * g ^ i ≡ kOf θ' [MOD g ^ d - 1] := by
        rw [Finset.mem_filter, Finset.mem_range, pow_zero, mul_one]
        exact ⟨hd, Nat.ModEq.refl _⟩
      have hne : ((Finset.range d).filter fun i => kOf θ * g ^ i ≡ kOf θ' [MOD g ^ d - 1]).Nonempty := by
        rw [← Finset.card_pos]
        refine Nat.pos_of_ne_zero fun h0 => ?_
        have h3 := (Finset.card_pos.2 ⟨0, hmem⟩).ne'
        rw [h0, Nat.cast_zero] at h2
        exact h3 (by exact_mod_cast h2.symm)
      obtain ⟨i, hi⟩ := hne
      rw [Finset.mem_filter, Finset.mem_range] at hi
      refine ⟨i, hi.1, ?_⟩
      rw [hkOf θ', hkOf θ, ← pow_mul]
      exact ((hpow_eq _ _).2 hi.2).symm
    · rintro ⟨i, hi, hθi⟩
      have hk : kOf θ' ≡ kOf θ * g ^ i [MOD g ^ d - 1] := by
        rw [← hpow_eq, pow_mul, ← hkOf θ, ← hkOf θ']
        exact hθi
      funext x
      refine congrArg (fun t : ℂ => (-1 : ℂ) ^ (d - 1) * t) ?_
      have hcl : ∀ k : ℕ, IsClassFn (psi (rootSum θ₀ k) (Fin d → ZMod g)) := fun k e G =>
        GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj (ZMod g) _ _ _ e G
      have hexp := fun k : ℕ => GlobalTheory.T.primitiveClassFunction_expansion_rootSums (ZMod g) (Fin d → ZMod g) θ₀ hθ₀ _ (hcl k)
        (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse (ZMod g) (Fin d → ZMod g) _ (hadd k)) hfr _ (hxU x)
      have e1 := hexp (kOf θ)
      have e2 := hexp (kOf θ')
      rw [Module.finrank_fin_fun, hcF] at e1 e2
      have hsum : ∀ l : ℕ, ipGL (psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g))
          (fun G => rootSum θ₀ l (LinearMap.charpoly G)) = ipGL (psi (rootSum θ₀ (kOf θ')) (Fin d → ZMod g))
          (fun G => rootSum θ₀ l (LinearMap.charpoly G)) := by
        intro l
        rw [hgram, hgram, filter_modEq_congr hk, card_filter_shift hg hd _ _ _ hi.le]
      rw [Finset.sum_congr rfl fun l _ => by rw [hsum l]] at e1
      exact mul_left_cancel₀ (mul_ne_zero hGL (Nat.cast_ne_zero.2 hd.ne')) (e1.trans e2.symm)

open GlobalTheory.GreenRegularCharactersInertiaEigenvalues in

theorem named_family : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d →
    ∃ (θ₀ : AlgebraicClosure (ZMod g) →* ℂ) (_ : ∀ x y : AlgebraicClosure (ZMod g), x ≠ 0 → y ≠ 0 → θ₀ x = θ₀ y → x = y)
      (ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g)) (kOf : (Kˣ →* ℂˣ) → ℕ),
      (∀ (θ : Kˣ →* ℂˣ) (u : Kˣ), ((θ u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) ^ kOf θ) ∧
      ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ,
      (∀ θ x, τ θ x = (-1) ^ (d - 1) *
        psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod g)))) ∧
      (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧
        ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 →
          τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧
      (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) ∧
      ∀ χ : Gn g d → ℂ, IsCusp χ → ∃ θ, IsRegularChar g d θ ∧ χ = τ θ := by
  intro g _ d hd K _ _ hK
  obtain ⟨θ₀, hθ₀, ι, kOf, hlink, τ, hτe, hτ1, hτ2⟩ := explicit_family g d hd K hK
  refine ⟨θ₀, hθ₀, ι, kOf, hlink, τ, hτe, hτ1, hτ2, ?_⟩
  have hex : ∀ e, ∃ L : (ZMod g)[X] → Gn g e → ℂ,
      (∀ P, IsPrimeLab e P → IsCusp (L P)) ∧
      (∀ P P', IsPrimeLab e P → IsPrimeLab e P' → L P = L P' → P = P') ∧
      (∀ _ : e = d, ∀ P, IsPrimeLab e P → ∃ θ, IsRegularChar g d θ ∧ (⟨e, L P⟩ : Pc g) = ⟨d, τ θ⟩) := by
    intro e
    by_cases hed : e = d
    · subst hed
      obtain ⟨L, hL1, hL2⟩ := family g e hd K hK τ (fun θ hθ => (hτ1 θ hθ).1) hτ2
      refine ⟨L, fun P hP => (hL1 P hP).1, hL2, fun _ P hP => ?_⟩
      obtain ⟨θ, hθ, he⟩ := (hL1 P hP).2
      exact ⟨θ, hθ, by rw [he]⟩
    · by_cases he0 : e = 0
      · refine ⟨fun _ _ => 0, fun P hP => absurd (isPrimeLab_pos hP) (by omega),
          fun P _ hP _ _ => absurd (isPrimeLab_pos hP) (by omega), fun h => absurd h hed⟩
      · have hpos : 0 < e := Nat.pos_of_ne_zero he0
        obtain ⟨τ', hτ'1, hτ'2⟩ := GlobalTheory.T.exists_cuspidalCharacter_of_regularCharacter_GLn g e hpos (GaloisField g e) (GaloisField.finrank g he0)
        obtain ⟨L, hL1, hL2⟩ := family g e hpos (GaloisField g e) (GaloisField.finrank g he0) τ'
          (fun θ hθ => (hτ'1 θ hθ).1) hτ'2
        exact ⟨L, fun P hP => (hL1 P hP).1, hL2, fun h => absurd h hed⟩
  choose Lf hc hi hdd using hex
  intro χ hχ
  by_contra hno
  push_neg at hno
  refine count d hd Lf hc hi χ hχ ?_
  intro P hP heq
  obtain ⟨θ, hθ, hs⟩ := hdd d rfl P hP
  have : Lf d P = τ θ := sigma_mk_injective hs
  exact hno θ hθ (heq ▸ this)

end DiscreteGroups.sglob.DzType.Kon
end
end

section
open Polynomial GlobalTheory.GLq GlobalTheory.Published

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

def fo (g n : ℕ) {K : Type} [Field K] (θ : Kˣ →* ℂˣ) (z : Kˣ) : ℂ :=
  ∑ i ∈ Finset.range n, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)

section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem charSum (χ : Kˣ →* ℂˣ) :
    ∑ z : Kˣ, ((χ z : ℂˣ) : ℂ) = if χ = 1 then (Fintype.card Kˣ : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · have hne : (Units.coeHom ℂ).comp χ ≠ 1 := by
      intro hc
      apply h
      ext z
      have := congrArg (fun f : Kˣ →* ℂ => f z) hc
      simpa using this
    exact sum_hom_units_eq_zero _ hne

theorem norm_val (θ : Kˣ →* ℂˣ) (z : Kˣ) : ‖((θ z : ℂˣ) : ℂ)‖ = 1 := by
  have h : (θ z) ^ Fintype.card Kˣ = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card Kˣ) ?_ Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem norm_fo_le (g n : ℕ) (θ : Kˣ →* ℂˣ) (z : Kˣ) : ‖fo g n θ z‖ ≤ n := by
  unfold fo
  refine (norm_sum_le _ _).trans ?_
  simp [norm_val]

theorem sum_fo_mul (g n : ℕ) (θ θ' : Kˣ →* ℂˣ) :
    ∑ z : Kˣ, fo g n θ z * fo g n θ' z⁻¹ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if θ ^ g ^ i = θ' ^ g ^ j then (Fintype.card Kˣ : ℂ) else 0 := by
  unfold fo
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ z : Kˣ, ((θ (z ^ g ^ i) : ℂˣ) : ℂ) * ((θ' (z⁻¹ ^ g ^ j) : ℂˣ) : ℂ) =
      (((θ ^ g ^ i * (θ' ^ g ^ j)⁻¹) z : ℂˣ) : ℂ) := by
    intro z
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, map_pow, inv_pow, map_inv,
      Units.val_mul]
  rw [Finset.sum_congr rfl fun z _ => e z, charSum]
  simp only [mul_inv_eq_one]

end

theorem char_pow_period {g n : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K] (hK : Fintype.card K = g ^ n)
    (θ : Kˣ →* ℂˣ) (hg : 0 < g) (a : ℕ) : θ ^ g ^ a = θ ^ g ^ (a % n) := by
  have hN : ∀ z : Kˣ, z ^ (g ^ n - 1) = 1 := fun z => by
    rw [← hK, ← Fintype.card_units]; exact pow_card_eq_one
  have hper : θ ^ g ^ n = θ := by
    ext z
    rw [MonoidHom.pow_apply, ← map_pow]
    have : z ^ g ^ n = z := by
      have h1 : 1 ≤ g ^ n := Nat.one_le_pow _ _ hg
      conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ, hN, one_mul]
    rw [this]
  have ha : g ^ a = (g ^ n) ^ (a / n) * g ^ (a % n) := by
    conv_lhs => rw [← Nat.mod_add_div a n]
    rw [pow_add, pow_mul, mul_comm]
  have : ∀ m : ℕ, θ ^ (g ^ n) ^ m = θ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hper]
  rw [ha, pow_mul, this]

end DiscreteGroups.sglob.DzType.Kon
end
end

section
open Polynomial GlobalTheory.GLq GlobalTheory.Published
open scoped IntermediateField

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

theorem exists_elliptic [FiniteDimensional (ZMod g) K] (hfr : Module.finrank (ZMod g) K = n) (z : Kˣ)
    (hz : (minpoly (ZMod g) (z : K)).natDegree = n) :
    ∃ y : Gn g n, Irreducible (y : Mt g n).charpoly ∧ aeval (z : K) (y : Mt g n).charpoly = 0 := by
  let b : Module.Basis (Fin n) (ZMod g) K := Module.finBasisOfFinrankEq (ZMod g) K hfr
  let L := Algebra.leftMulMatrix b
  refine ⟨Units.map (L : K →* Matrix (Fin n) (Fin n) (ZMod g)) z, ?_⟩
  have hy : ((Units.map (L : K →* Matrix (Fin n) (Fin n) (ZMod g)) z : Gn g n) : Mt g n) = L (z : K) := rfl
  rw [hy]
  have hc : aeval (z : K) (L (z : K)).charpoly = 0 := by
    have h1 := Matrix.aeval_self_charpoly (L (z : K))
    rw [aeval_algHom_apply] at h1
    exact Algebra.leftMulMatrix_injective b (h1.trans (map_zero L).symm)
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  have hdvd := minpoly.dvd (ZMod g) (z : K) hc
  have heq : (L (z : K)).charpoly = minpoly (ZMod g) (z : K) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (Matrix.charpoly_monic _) hdvd
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hz])
  rw [heq]
  exact ⟨minpoly.irreducible hint, minpoly.aeval _ _⟩

theorem bad_of_deg [FiniteDimensional (ZMod g) K] (hn : 0 < n) (hfr : Module.finrank (ZMod g) K = n) (z : Kˣ)
    (hz : (minpoly (ZMod g) (z : K)).natDegree ≠ n) : ∃ i ∈ Finset.Icc 1 (n / 2), z ^ g ^ i = z := by
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  set d := (minpoly (ZMod g) (z : K)).natDegree with hd
  have hd1 : 0 < d := minpoly.natDegree_pos hint
  have hfd : Module.finrank (ZMod g) (ZMod g)⟮(z : K)⟯ = d := IntermediateField.adjoin.finrank hint
  have htow := Module.finrank_mul_finrank (ZMod g) (ZMod g)⟮(z : K)⟯ K
  rw [hfd, hfr] at htow
  set r := Module.finrank (ZMod g)⟮(z : K)⟯ K
  have hr1 : r ≠ 1 := by
    intro h1; rw [h1, mul_one] at htow; exact hz htow
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, mul_zero] at htow; omega
  have h2d : d * 2 ≤ n := by
    rw [← htow]; exact Nat.mul_le_mul_left _ (by omega)
  refine ⟨d, Finset.mem_Icc.2 ⟨hd1, (Nat.le_div_iff_mul_le (by norm_num)).2 h2d⟩, ?_⟩
  have : Finite K := Module.finite_of_finite (ZMod g)
  have : Finite (ZMod g)⟮(z : K)⟯ := Finite.of_injective _ Subtype.val_injective
  letI : Fintype (ZMod g)⟮(z : K)⟯ := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod g)⟮(z : K)⟯ = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hfd]
  have hx := FiniteField.pow_card (⟨(z : K), IntermediateField.mem_adjoin_simple_self _ _⟩ : (ZMod g)⟮(z : K)⟯)
  rw [hcard] at hx
  have hx' := congrArg Subtype.val hx
  simp only [IntermediateField.coe_pow] at hx'
  exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hx')

theorem card_fixed_le [Fintype K] [DecidableEq K] (i : ℕ) (hi : 0 < i) :
    (Finset.univ.filter fun z : Kˣ => z ^ g ^ i = z).card ≤ g ^ i := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hq : 1 < g ^ i := Nat.one_lt_pow hi.ne' hg
  have hne := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  calc (Finset.univ.filter fun z : Kˣ => z ^ g ^ i = z).card
      ≤ ((X ^ g ^ i - X : K[X]).roots.toFinset).card := by
        refine Finset.card_le_card_of_injOn (fun z : Kˣ => (z : K)) ?_ ?_
        · intro z hz
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz
          simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X]
          rw [← Units.val_pow_eq_pow_val, hz, sub_self]
        · intro x _ y _ h; exact Units.ext h
    _ ≤ (X ^ g ^ i - X : K[X]).roots.card := Multiset.toFinset_card_le _
    _ ≤ (X ^ g ^ i - X : K[X]).natDegree := card_roots' _
    _ = g ^ i := hdeg

end DiscreteGroups.sglob.DzType.Kon
end
end

section
open Polynomial GlobalTheory.GLq GlobalTheory.Published

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

open scoped Classical in
theorem card_bad_le [Fintype K] [DecidableEq K] :
    (Finset.univ.filter fun z : Kˣ => ∃ i ∈ Finset.Icc 1 (n / 2), z ^ g ^ i = z).card ≤
      (n / 2) * g ^ (n / 2) := by
  have hg : 1 ≤ g := (Fact.out : g.Prime).one_lt.le
  calc (Finset.univ.filter fun z : Kˣ => ∃ i ∈ Finset.Icc 1 (n / 2), z ^ g ^ i = z).card
      ≤ ((Finset.Icc 1 (n / 2)).biUnion fun i => Finset.univ.filter fun z : Kˣ => z ^ g ^ i = z).card := by
        refine Finset.card_le_card fun z hz => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨i, hi, hzi⟩ := hz
        exact Finset.mem_biUnion.2 ⟨i, hi, by simp [hzi]⟩
    _ ≤ ∑ i ∈ Finset.Icc 1 (n / 2), (Finset.univ.filter fun z : Kˣ => z ^ g ^ i = z).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.Icc 1 (n / 2), g ^ (n / 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_Icc.1 hi
        exact (card_fixed_le (K := K) i hi'.1).trans (Nat.pow_le_pow_right hg hi'.2)
    _ = (n / 2) * g ^ (n / 2) := by rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]

theorem orbit_of_agree (hn : 2 ≤ n) (hbig : 16 * n ^ 2 < g) (hK : Nat.card K = g ^ n) (θ θ' : Kˣ →* ℂˣ)
    (hθ : IsRegularChar g n θ)
    (h : ∀ z : Kˣ, (∃ y : Gn g n, Irreducible (y : Mt g n).charpoly ∧ aeval (z : K) (y : Mt g n).charpoly = 0) →
      fo g n θ z = fo g n θ' z) : ∃ i < n, θ' = θ ^ g ^ i := by
  classical
  have hgp : g.Prime := Fact.out
  have hg : 1 < g := hgp.one_lt
  have hn0 : 0 < n := by omega
  have hKpos : 0 < Nat.card K := by rw [hK]; exact pow_pos hgp.pos _
  have : Finite K := Nat.finite_of_card_ne_zero hKpos.ne'
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : FiniteDimensional (ZMod g) K := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hcard] at h1
    exact (Nat.pow_right_injective hgp.two_le h1).symm
  by_contra hno
  push_neg at hno
  have hne : ∀ i < n, ∀ j < n, θ ^ g ^ i ≠ θ' ^ g ^ j := by
    intro i hi j hj heq
    apply hno ((i + (n - j)) % n) (Nat.mod_lt _ hn0)
    have e1 : θ' = (θ' ^ g ^ j) ^ g ^ (n - j) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hj.le, char_pow_period hcard θ' hgp.pos n, Nat.mod_self,
        pow_zero, pow_one]
    rw [e1, ← heq, ← pow_mul, ← pow_add, char_pow_period hcard θ hgp.pos]
  have hS' : ∑ z : Kˣ, fo g n θ z * fo g n θ' z⁻¹ = 0 := by
    rw [sum_fo_mul]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    rw [if_neg (hne i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj))]
  have hS : ∑ z : Kˣ, fo g n θ z * fo g n θ z⁻¹ = (n : ℂ) * (Fintype.card Kˣ : ℂ) := by
    rw [sum_fo_mul]
    have e : ∀ i ∈ Finset.range n, (∑ j ∈ Finset.range n,
        if θ ^ g ^ i = θ ^ g ^ j then (Fintype.card Kˣ : ℂ) else 0) = Fintype.card Kˣ := by
      intro i hi
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intro j hj hji
        rw [if_neg (fun h' => hji (hθ i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h').symm)]
      · intro h'; exact absurd hi h'
    rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set B := Finset.univ.filter fun z : Kˣ => ∃ i ∈ Finset.Icc 1 (n / 2), z ^ g ^ i = z with hB
  have hgood : ∀ z : Kˣ, z ∉ B → fo g n θ z⁻¹ = fo g n θ' z⁻¹ := by
    intro z hz
    apply h
    apply exists_elliptic hfr
    by_contra hd
    obtain ⟨i, hi, hzi⟩ := bad_of_deg hn0 hfr z⁻¹ hd
    apply hz
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨i, hi, ?_⟩
    rw [inv_pow] at hzi; exact inv_injective hzi
  have hdiff : (n : ℂ) * (Fintype.card Kˣ : ℂ) =
      ∑ z ∈ B, fo g n θ z * (fo g n θ z⁻¹ - fo g n θ' z⁻¹) := by
    rw [← hS, ← sub_zero (∑ z : Kˣ, fo g n θ z * fo g n θ z⁻¹), ← hS', ← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_univ B)]
    · exact Finset.sum_congr rfl fun z _ => by ring
    · intro z _ hz; rw [hgood z hz]; ring
  have hnorm : (n : ℝ) * (Fintype.card Kˣ : ℝ) ≤ (B.card : ℝ) * ((n : ℝ) * (2 * n)) := by
    have h1 := congrArg norm hdiff
    rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast] at h1
    rw [h1]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
    rw [norm_mul]
    refine mul_le_mul (norm_fo_le g n θ z) ((norm_sub_le _ _).trans ?_) (norm_nonneg _) (Nat.cast_nonneg _)
    linarith [norm_fo_le g n θ z⁻¹, norm_fo_le g n θ' z⁻¹]
  have hU : Fintype.card Kˣ = g ^ n - 1 := by rw [Fintype.card_units, hcard]
  have hnat : n * (g ^ n - 1) ≤ B.card * (n * (2 * n)) := by
    rw [← hU]; exact_mod_cast hnorm
  have h2 : g ^ n - 1 ≤ B.card * (2 * n) := by
    have : n * (g ^ n - 1) ≤ n * (B.card * (2 * n)) := by
      calc n * (g ^ n - 1) ≤ B.card * (n * (2 * n)) := hnat
        _ = n * (B.card * (2 * n)) := by ring
    exact Nat.le_of_mul_le_mul_left this hn0
  have hcB := card_bad_le (g := g) (n := n) (K := K)
  set m := n / 2 with hm
  have hm2 : 2 * m ≤ n := Nat.mul_div_le n 2
  have hmn : m + 1 ≤ n := by omega
  have h3 : g ^ n - 1 ≤ n * n * g ^ m := by
    calc g ^ n - 1 ≤ B.card * (2 * n) := h2
      _ ≤ (m * g ^ m) * (2 * n) := Nat.mul_le_mul_right _ hcB
      _ = (2 * m) * n * g ^ m := by ring
      _ ≤ n * n * g ^ m := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm2)
  have h4 : g ^ m * g ≤ g ^ n := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right hgp.pos hmn
  have hgm : 0 < g ^ m := pow_pos hgp.pos _
  have h5 : g ^ m * (16 * n ^ 2 + 1) ≤ g ^ m * g := Nat.mul_le_mul_left _ hbig
  have h6 : n * n * g ^ m + 1 < g ^ n := by nlinarith
  omega

end DiscreteGroups.sglob.DzType.Kon
end
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.GLq GlobalTheory.Published

noncomputable section

namespace DiscreteGroups.sglob.DzType

open Kon

set_option linter.style.haveILetI false

theorem lKondo : LKondo := by
  intro g _ n hn2 hbig K _ _ hK ψ₀ hψ₀
  classical
  have hgp : g.Prime := Fact.out
  have hn0 : 0 < n := by omega
  have hKpos : 0 < Nat.card K := by rw [hK]; exact pow_pos hgp.pos _
  have : Finite K := Nat.finite_of_card_ne_zero hKpos.ne'
  let _ : Fintype K := Fintype.ofFinite K
  have : FiniteDimensional (ZMod g) K := Module.Finite.of_finite
  have hcard : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hcard] at h1
    exact (Nat.pow_right_injective hgp.two_le h1).symm
  obtain ⟨θ₀, hθ₀, ι, kOf, hlink, τE, hτe, hτ1, hτ2, hex⟩ := named_family g n hn0 K hfr
  have hN : 0 < g ^ n - 1 := by have := Nat.one_lt_pow hn0.ne' hgp.one_lt; omega
  have hD0 : (∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have hi1 := (Finset.mem_Ico.1 hi).1
    have h1 : ((g ^ i : ℕ) : ℂ) ≠ 1 := by
      rw [Ne, Nat.cast_eq_one]; exact (Nat.one_lt_pow (by omega) hgp.one_lt).ne'
    rw [sub_ne_zero]; exact_mod_cast h1
  have hGL : glCard (ZMod g) n ≠ 0 := by unfold glCard; exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hNc : ((g ^ n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hε : ((-1 : ℂ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  refine ⟨(-1) ^ (n - 1) * glCard (ZMod g) n / (((g ^ n - 1 : ℕ) : ℂ) * ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)),
    div_ne_zero (mul_ne_zero hε hGL) (mul_ne_zero hNc hD0), ?_⟩
  intro θ hθ τ hτ hf
  have hname : ∀ x, τ.character x = τE θ x := by
    obtain ⟨θ', hθ', heq⟩ := hex τ.character hτ
    obtain ⟨i, hi, hii⟩ := orbit_of_agree hn2 hbig hK θ θ' hθ (fun z hz => by
      obtain ⟨y, hy, hzy⟩ := hz
      have e1 := hf y hy z hzy
      have e2 := (hτ1 θ' hθ').2.2 y hy z hzy
      rw [heq] at e1
      show fo g n θ z = fo g n θ' z
      exact mul_left_cancel₀ hε (e1.symm.trans e2))
    have h3 : τE θ = τE θ' := (hτ2 θ θ' hθ hθ').2 ⟨i, hi, hii⟩
    intro x; rw [heq, ← h3]
  have hsimple := simple_of_isIrr τ hτ.2.1
  let fψ : Gn g n → ℂ := fun y => ((ψ₀ (Matrix.trace (y : Mt g n)) : Circle) : ℂ)
  have hfcl : ∀ x y : Gn g n, fψ (y * x * y⁻¹) = fψ x := by
    intro x y
    simp only [fψ, Units.val_mul]
    rw [Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨c, hc1, hc2⟩ := central_scalar τ fψ hfcl
  have hdim : (Module.finrank ℂ τ : ℂ) = ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1) := by
    rw [← FDRep.char_one, hname, (hτ1 θ hθ).2.1]
  have hip := ipGL_psi_trace (F := ZMod g) (Fin n → ZMod g) (by rw [Module.finrank_fin_fun]; exact hn0) θ₀ hθ₀
    (kOf θ) (fun a => ((ψ₀ a : Circle) : ℂ))
  rw [Module.finrank_fin_fun] at hip
  rw [(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties (ZMod g) n (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype] at hip
  have e : ∀ y : Gn g n, fψ y * τ.character y⁻¹ =
      star (psi (rootSum θ₀ (kOf θ)) (Fin n → ZMod g) (Matrix.toLin' (y : Mt g n)) *
        star ((ψ₀ (-(LinearMap.charpoly (Matrix.toLin' (y : Mt g n))).nextCoeff) : Circle) : ℂ)) * (-1) ^ (n - 1) := by
    intro y
    rw [GlobalTheory.BadShare.ZCalc.character_inv, hname, hτe, ← trace_eq_nextCoeff hn0]
    simp only [fψ, starRingEnd_apply, star_mul', star_pow, star_neg, star_one, star_star]
    ring
  have hsum : ∑ y : Gn g n, fψ y * τ.character y⁻¹ =
      (-1) ^ (n - 1) * glCard (ZMod g) n * aC n θ₀ (hT n fun a => ((ψ₀ a : Circle) : ℂ)) (kOf θ) := by
    rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.sum_mul, ← star_sum]
    rw [show (∑ y : Gn g n, psi (rootSum θ₀ (kOf θ)) (Fin n → ZMod g) (Matrix.toLin' (y : Mt g n)) *
        star ((ψ₀ (-(LinearMap.charpoly (Matrix.toLin' (y : Mt g n))).nextCoeff) : Circle) : ℂ)) =
        glCard (ZMod g) n * star (aC n θ₀ (hT n fun a => ((ψ₀ a : Circle) : ℂ)) (kOf θ)) from hip]
    rw [star_mul', star_star, glCard, star_natCast]
    ring
  have hgs := aC_eq_gs hn0 hK θ₀ ι θ (kOf θ) (hlink θ) ψ₀
  rw [hdim, hsum, hgs] at hc2
  have hcval : c = (-1) ^ (n - 1) * glCard (ZMod g) n /
      (((g ^ n - 1 : ℕ) : ℂ) * ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)) * gs ψ₀ θ⁻¹ := by
    unfold gs
    have h4 : c = (c * ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)) / ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1) := by
      field_simp
    rw [h4, hc2]
    field_simp
  intro v
  rw [finsum_eq_sum_of_fintype]
  exact (hc1 v).trans (by rw [hcval])

end DiscreteGroups.sglob.DzType
end
end
