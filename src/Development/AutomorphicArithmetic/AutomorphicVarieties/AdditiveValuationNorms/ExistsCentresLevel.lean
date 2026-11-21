import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsUnitAddMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLen
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.PowIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenComp

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.lift :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X →
      ∃ S : Matrix (Fin R) (Fin R) ℤ_[l], ∀ c : ℤ_[l], cokLen (c • g - 1) ≤ vl l (c • S - 1).det := by
  intro l _ X _ _ R g hgen
  obtain ⟨π, hπ⟩ := hgen
  choose s hs using fun j : Fin R => hπ (g (π (Pi.single j 1)))
  refine ⟨Matrix.of fun i j => s j i, fun c => ?_⟩
  have hcomm : ∀ v : Fin R → ℤ_[l], π (Matrix.mulVec (Matrix.of fun i j => s j i) v) = g (π v) := by
    have h : π ∘ₗ (Matrix.of fun i j => s j i).mulVecLin = g ∘ₗ π := by
      ext j
      simp [Matrix.mulVec_single_one]
      rw [← hs j]
      rfl
    intro v
    simpa using LinearMap.congr_fun h v
  set A : Matrix (Fin R) (Fin R) ℤ_[l] := c • (Matrix.of fun i j => s j i) - 1 with hA
  have hcommA : ∀ v, π (A.mulVecLin v) = (c • g - 1) (π v) := by
    intro v
    simp only [hA, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, map_sub, map_smul, hcomm, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
  let φ : (Fin R → ℤ_[l]) →ₗ[ℤ_[l]] X ⧸ LinearMap.range (c • g - 1) :=
    (LinearMap.range (c • g - 1)).mkQ ∘ₗ π
  have hker : LinearMap.range A.mulVecLin ≤ LinearMap.ker φ := by
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [hcommA]
    exact LinearMap.mem_range_self _ _
  have hsurj : Function.Surjective ((LinearMap.range A.mulVecLin).liftQ φ hker) := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨v, rfl⟩ := hπ y
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  have hlen := Module.length_le_of_surjective _ hsurj
  have hdet := KStar.Selmer.length_cokernel_eq_addVal_det A
  unfold cokLen
  exact hlen.trans_eq hdet
end

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.detFactor :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Matrix (Fin n) (Fin n) K),
      ∃ z : Fin n → K, ∀ c : K, (c • S - 1).det = ∏ i, (c * z i - 1) := by
  intro K _ _ n S
  classical
  set p := S.charpoly with hp
  have hmon : p.Monic := Matrix.charpoly_monic S
  have hprod : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod = p :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon IsAlgClosed.card_roots_eq_natDegree
  have hcard : Multiset.card p.roots = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have heval : ∀ x : K, (Matrix.scalar (Fin n) x - S).det = (p.roots.map (fun a => x - a)).prod := by
    intro x
    rw [← Matrix.eval_charpoly, ← hp]
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hz : ∃ z : Fin n → K, ∀ f : K → K, (p.roots.map f).prod = ∏ i, f (z i) := by
    obtain ⟨L, hL⟩ : ∃ L : List K, (L : Multiset K) = p.roots := ⟨_, Multiset.coe_toList _⟩
    have hlen : L.length = n := by rw [← hcard, ← hL, Multiset.coe_card]
    refine ⟨fun i => L.get (Fin.cast hlen.symm i), fun f => ?_⟩
    rw [← hL, Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp [hlen]
  obtain ⟨z, hz⟩ := hz
  refine ⟨z, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc
    simp [Matrix.det_neg]
  · have hmat : c • S - 1 = (-c) • (Matrix.scalar (Fin n) c⁻¹ - S) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.sub_apply, Matrix.one_apply]
        field_simp
        ring
      · simp [Matrix.sub_apply, Matrix.one_apply, hij]
    rw [hmat, Matrix.det_smul, heval, hz, Fintype.card_fin, ← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    field_simp
    ring
end

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.helly :
    ∀ (l : ℕ) [Fact l.Prime] (x : ℕ → ℤ_[l]) (r : ℕ → ℝ), (∀ a b, ‖x a - x b‖ ≤ max (r a) (r b)) →
      ∃ s : ℤ_[l], ∀ a, ‖s - x a‖ ≤ r a := by
  intro l _ x r hx
  have hne : ∀ u : Finset ℕ,
      ((Set.univ : Set ℤ_[l]) ∩ ⋂ a ∈ u, Metric.closedBall (x a) (r a)).Nonempty := by
    intro u
    rcases u.eq_empty_or_nonempty with hu | hu
    · exact ⟨0, by simp [hu]⟩
    · obtain ⟨a0, ha0, hmin⟩ := u.exists_min_image r hu
      refine ⟨x a0, Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter, Metric.mem_closedBall, dist_eq_norm]
      intro a ha
      exact (hx a0 a).trans (max_le (hmin a ha) le_rfl)
  obtain ⟨s, -, hs⟩ := isCompact_univ.inter_iInter_nonempty
    (fun a => Metric.closedBall (x a) (r a)) (fun a => Metric.isClosed_closedBall) hne
  refine ⟨s, fun a => ?_⟩
  have h1 := Set.mem_iInter.1 hs a
  rw [Metric.mem_closedBall, dist_eq_norm] at h1
  exact h1
end

section
open UpperTheory.V UpperTheory.V.PropA

private theorem norm_le_of_dvd' {l : ℕ} [Fact l.Prime] {x y : ℤ_[l]} (h : x ∣ y) : ‖y‖ ≤ ‖x‖ := by
  obtain ⟨z, rfl⟩ := h
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)

private theorem norm_eq_of_addVal {l : ℕ} [Fact l.Prime] {x y : ℤ_[l]}
    (h : IsDiscreteValuationRing.addVal ℤ_[l] x = IsDiscreteValuationRing.addVal ℤ_[l] y) :
    ‖x‖ = ‖y‖ := by
  have h1 : x ∣ y := IsDiscreteValuationRing.addVal_le_iff_dvd.mp h.le
  have h2 : y ∣ x := IsDiscreteValuationRing.addVal_le_iff_dvd.mp h.ge
  exact le_antisymm (norm_le_of_dvd' h2) (norm_le_of_dvd' h1)

theorem UpperTheory.V.PropA.lteNorm :
    ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (c : ℕ), IsLevel l u c → ‖u‖ = 1 ∧ (l : ℤ_[l]) ∣ u - 1 ∧
      ∀ j a b : ℕ, ‖(u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b‖ = ((l : ℝ) ^ (j + c))⁻¹ * ‖(a : ℤ_[l]) - b‖ := by
  intro l _ u c hc
  obtain ⟨hv, hc1, hc2⟩ := hc
  have hval1 : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p
  have hl : (l : ℤ_[l]) ∣ u - 1 := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hval1]
    simp only [vl] at hv
    rw [hv]
    exact_mod_cast hc1
  have hn1 : ‖u - 1‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).2 hl
  have hu : ‖u‖ = 1 := by
    have := PadicInt.norm_eq_of_norm_add_lt_right (z1 := u) (z2 := -1)
      (by rw [norm_neg, norm_one, ← sub_eq_add_neg]; exact hn1)
    rwa [norm_neg, norm_one] at this
  refine ⟨hu, hl, ?_⟩
  intro j a b
  have hunit : IsUnit u := PadicInt.isUnit_iff.2 hu
  set v := hunit.unit with hvdef
  have hvu : (v : ℤ_[l]) = u := hunit.unit_spec
  have hvmem : v ∈ abelian₂.oneUnits ℤ_[l] := by
    show (v : ℤ_[l]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[l]
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, hvu]
    exact hn1
  let U : abelian₂.oneUnits ℤ_[l] := ⟨v, hvmem⟩
  set n : ℤ := ((l ^ j * a : ℕ) : ℤ) - ((l ^ j * b : ℕ) : ℤ) with hndef
  have hlm : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hptU : IsDiscreteValuationRing.addVal ℤ_[l] ↑(abelian₂.pt U) = c := by
    rw [abelian₂.coe_pt]
    simp only [vl] at hv
    rw [show ((U : ℤ_[l]ˣ) : ℤ_[l]) = u from hvu]
    exact hv
  have hcond : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) <
      ↑(l - 1) * IsDiscreteValuationRing.addVal ℤ_[l] ↑(abelian₂.pt U) := by
    rw [hval1, hptU]
    have hlt : 1 < (l - 1) * c := by
      have hp := (Fact.out : l.Prime).two_le
      rcases Nat.lt_or_ge l 3 with h | h
      · have h2 : l = 2 := by omega
        have := hc2 h2
        subst h2
        omega
      · have h3 : 2 ≤ l - 1 := by omega
        calc 1 < 2 * 1 := by norm_num
          _ ≤ (l - 1) * c := Nat.mul_le_mul h3 hc1
    exact_mod_cast hlt
  have key := abelian₂.lte ℤ_[l] l Fact.out hlm U hcond n
  have hfac : (u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b = (u ^ l ^ j) ^ b * ↑(abelian₂.pt (U ^ n)) := by
    rw [abelian₂.coe_pt]
    have h1 : ((U ^ n : abelian₂.oneUnits ℤ_[l]) : ℤ_[l]ˣ) = v ^ n := rfl
    have h2 : v ^ ((l ^ j * a : ℕ) : ℤ) = v ^ ((l ^ j * b : ℕ) : ℤ) * v ^ n := by
      rw [← zpow_add]
      congr 1
      rw [hndef]
      ring
    have h3 : ∀ k : ℕ, (u ^ l ^ j) ^ k = ((v ^ ((l ^ j * k : ℕ) : ℤ) : ℤ_[l]ˣ) : ℤ_[l]) := by
      intro k
      rw [zpow_natCast, Units.val_pow_eq_pow_val, hvu, pow_mul]
    rw [h1, h3 a, h3 b, h2, Units.val_mul]
    ring
  rw [hfac, norm_mul, norm_pow, norm_pow, hu, one_pow, one_pow, one_mul]
  rw [norm_eq_of_addVal (y := (l : ℤ_[l]) ^ (j + c) * ((a : ℤ_[l]) - (b : ℤ_[l])))]
  · rw [norm_mul, PadicInt.norm_p_pow, zpow_neg, zpow_natCast]
  · have hcast : ((n : ℤ) : ℤ_[l]) = (l : ℤ_[l]) ^ j * ((a : ℤ_[l]) - (b : ℤ_[l])) := by
      rw [hndef]
      push_cast
      ring
    rw [key, hptU, hcast, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hval1]
    simp only [nsmul_eq_mul, mul_one]
    push_cast
    ring
end

section
open UpperTheory.V UpperTheory.V.PropA

private theorem padic_units_distance_le_max (l : ℕ) [Fact l.Prime] (a b : ℤ_[l]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (z : PadicAlgCl l) :
    ‖a - b‖ ≤ max ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l]) * z - 1‖
      ‖algebraMap ℚ_[l] (PadicAlgCl l) (b : ℚ_[l]) * z - 1‖ := by
  set A := algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])
  set B := algebraMap ℚ_[l] (PadicAlgCl l) (b : ℚ_[l])
  have hA : ‖A‖ = 1 := by
    simp only [A, PadicAlgCl.norm_extends, ← PadicInt.norm_def, ha]
  have hAB : ‖A - B‖ = ‖a - b‖ := by
    simp only [A, B, ← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, ← PadicInt.norm_def]
  have hdiff : A * z - 1 - (B * z - 1) = (A - B) * z := by ring
  have hmax : ‖A * z - 1 - (B * z - 1)‖ ≤ max ‖A * z - 1‖ ‖B * z - 1‖ := by
    have := IsUltrametricDist.norm_add_le_max (A * z - 1) (-(B * z - 1))
    rwa [norm_neg, ← sub_eq_add_neg] at this
  rcases le_or_gt 1 ‖z‖ with hz | hz
  · calc ‖a - b‖ ≤ ‖a - b‖ * ‖z‖ := le_mul_of_one_le_right (norm_nonneg _) hz
      _ = ‖A * z - 1 - (B * z - 1)‖ := by rw [hdiff, norm_mul, hAB]
      _ ≤ _ := hmax
  · have hAz : ‖A * z‖ < 1 := by rw [norm_mul, hA, one_mul]; exact hz
    have h1 : (1 : ℝ) ≤ ‖A * z - 1‖ := by
      have := IsUltrametricDist.norm_add_le_max (A * z) (-(A * z - 1))
      rw [norm_neg, show A * z + -(A * z - 1) = 1 by ring, norm_one] at this
      rcases le_max_iff.mp this with h | h
      · exact absurd h (not_le.mpr hAz)
      · exact h
    calc ‖a - b‖ ≤ 1 := PadicInt.norm_le_one _
      _ ≤ ‖A * z - 1‖ := h1
      _ ≤ _ := le_max_left _ _

theorem UpperTheory.V.PropA.ball :
    ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (c : ℕ), IsLevel l u c → ∀ (j : ℕ) (z : PadicAlgCl l), ∃ s : ℤ_[l], ∀ e : ℕ,
      ((l : ℝ) ^ (j + c))⁻¹ * ‖s - e‖ ≤ ‖algebraMap ℚ_[l] (PadicAlgCl l) (((u ^ l ^ j) ^ e : ℤ_[l]) : ℚ_[l]) * z - 1‖ := by
  intro l _ u c hc j z
  obtain ⟨hu, -, hdist⟩ := lteNorm l u c hc
  have hK : (0 : ℝ) < (l : ℝ) ^ (j + c) := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  set r : ℕ → ℝ := fun e =>
    (l : ℝ) ^ (j + c) * ‖algebraMap ℚ_[l] (PadicAlgCl l) (((u ^ l ^ j) ^ e : ℤ_[l]) : ℚ_[l]) * z - 1‖ with hr
  have hunit : ∀ e : ℕ, ‖((u ^ l ^ j) ^ e : ℤ_[l])‖ = 1 := by
    intro e
    rw [← pow_mul, norm_pow, hu, one_pow]
  obtain ⟨s, hs⟩ := helly l (fun e : ℕ => (e : ℤ_[l])) r (by
    intro a b
    have key := padic_units_distance_le_max l _ _ (hunit a) (hunit b) z
    have h := hdist j a b
    have : ‖(a : ℤ_[l]) - b‖ = (l : ℝ) ^ (j + c) * ‖(u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b‖ := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
    simp only [this, hr]
    rw [← mul_max_of_nonneg _ _ hK.le]
    exact mul_le_mul_of_nonneg_left key hK.le)
  refine ⟨s, fun e => ?_⟩
  have := hs e
  simp only [hr] at this
  rw [inv_mul_le_iff₀ hK]
  exact this
end

section
open UpperTheory.V UpperTheory.V.PropA

private theorem dvd_of_norm_le' {l : ℕ} [Fact l.Prime] {d y : ℤ_[l]} (h : ‖y‖ ≤ ‖d‖) : d ∣ y := by
  by_cases hy : y = 0
  · subst hy
    exact dvd_zero d
  by_cases hd : d = 0
  · subst hd
    rw [norm_zero, norm_le_zero_iff] at h
    exact absurd h hy
  have hav : ∀ x : ℤ_[l], x ≠ 0 → IsDiscreteValuationRing.addVal ℤ_[l] x = x.valuation :=
    fun x hx => IsDiscreteValuationRing.addVal_def x (PadicInt.unitCoeff hx) PadicInt.irreducible_p _
      (PadicInt.unitCoeff_spec hx)
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hav d hd, hav y hy, Nat.cast_le]
  rw [PadicInt.norm_eq_zpow_neg_valuation hd, PadicInt.norm_le_pow_iff_le_valuation y hy] at h
  exact h

private theorem vl_prod {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → ℤ_[l]) :
    vl l (∏ i ∈ s, f i) = ∑ i ∈ s, vl l (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    exact IsDiscreteValuationRing.addVal_mul

theorem UpperTheory.V.PropA.normVal :
    ∀ (l : ℕ) [Fact l.Prime] (R c : ℕ) (d : ℤ_[l]) (x : Fin R → ℤ_[l]),
      ∏ i, (((l : ℝ) ^ c)⁻¹ * ‖x i‖) ≤ ‖d‖ → vl l d ≤ ∑ i, ((c : ℕ∞) + vl l (x i)) := by
  intro l _ R c d x h
  have h1 : ‖∏ i, ((l : ℤ_[l]) ^ c * x i)‖ = ∏ i, (((l : ℝ) ^ c)⁻¹ * ‖x i‖) := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_mul, norm_pow, PadicInt.norm_p, inv_pow]
  have h2 : d ∣ ∏ i, ((l : ℤ_[l]) ^ c * x i) := dvd_of_norm_le' (h1 ▸ h)
  have h3 : vl l (∏ i, ((l : ℤ_[l]) ^ c * x i)) = ∑ i, ((c : ℕ∞) + vl l (x i)) := by
    rw [vl_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (PadicInt.irreducible_p (p := l)).addVal_pow c
    unfold vl
    rw [IsDiscreteValuationRing.addVal_mul, this]
  rw [← h3]
  exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr h2
end

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.detBound :
    ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (c : ℕ), IsLevel l u c → ∀ (j R : ℕ) (S : Matrix (Fin R) (Fin R) ℤ_[l]),
      ∃ s : Fin R → ℤ_[l], ∀ e : ℕ, vl l ((u ^ l ^ j) ^ e • S - 1).det ≤ ∑ i, (((j + c : ℕ) : ℕ∞) + vl l (s i - e)) := by
  intro l _ u c hc j R S
  let φ : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  have hφ : ∀ x, ‖φ x‖ = ‖x‖ := by
    intro x
    show ‖algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l])‖ = ‖x‖
    rw [← PadicInt.padic_norm_e_of_padicInt]
    exact PadicAlgCl.norm_extends l (x : ℚ_[l])
  obtain ⟨z, hz⟩ := detFactor (PadicAlgCl l) R (S.map φ)
  choose s hs using fun i => ball l u c hc j (z i)
  refine ⟨s, fun e => ?_⟩
  apply normVal l R (j + c) _ (fun i => s i - e)
  set a : ℤ_[l] := (u ^ l ^ j) ^ e with ha
  have hdet : φ (a • S - 1).det = ∏ i, (φ a * z i - 1) := by
    rw [RingHom.map_det, ← hz (φ a)]
    congr 1
    ext p q
    simp [Matrix.sub_apply, Matrix.one_apply, RingHom.mapMatrix_apply]
  rw [← hφ, hdet, norm_prod]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    exact hs i e
end

section
open UpperTheory.V UpperTheory.V.PropA

private theorem nilLen_range_succ {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (f : Module.End A M) (k : ℕ) :
    LinearMap.range (f ^ (k + 1)) = (LinearMap.range (f ^ k)).map f := by
  rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]

private theorem nilLen_lt {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (f : Module.End A M) (hf : IsNilpotent f) (k : ℕ) (hk : f ^ k ≠ 0) :
    LinearMap.range (f ^ (k + 1)) < LinearMap.range (f ^ k) := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [pow_succ, Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  · intro h
    apply hk
    obtain ⟨n, hn⟩ := hf
    have key : ∀ j, LinearMap.range (f ^ (k + j)) = LinearMap.range (f ^ k) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [← add_assoc, nilLen_range_succ, ih, ← nilLen_range_succ, h]
    have hkn := key n
    rw [pow_add, hn, mul_zero, LinearMap.range_zero] at hkn
    exact LinearMap.range_eq_bot.mp hkn.symm

theorem UpperTheory.V.PropA.nilLen :
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (f : Module.End A M) (n : ℕ), IsNilpotent f →
      Module.length A M ≤ n → f ^ n = 0 := by
  intro A M _ _ _ f n hf hlen
  by_contra hne
  have hm : ∀ m, m ≤ n → f ^ m ≠ 0 := fun m hm h0 => hne (pow_eq_zero_of_le hm h0)
  have key : ∀ j m, m + j = n → (j : ℕ∞) + 1 ≤ Order.height (LinearMap.range (f ^ m)) := by
    intro j
    induction j with
    | zero =>
      intro m hmj
      have hlt : (⊥ : Submodule A M) < LinearMap.range (f ^ m) := by
        rw [bot_lt_iff_ne_bot, Ne, LinearMap.range_eq_bot]
        exact hm m (by omega)
      have h0 := Order.height_add_one_le hlt
      simp only [Nat.cast_zero, zero_add]
      exact le_trans le_add_self h0
    | succ j ih =>
      intro m hmj
      have h1 := ih (m + 1) (by omega)
      have h2 := Order.height_add_one_le (nilLen_lt f hf m (hm m (by omega)))
      calc ((j + 1 : ℕ) : ℕ∞) + 1 = ((j : ℕ∞) + 1) + 1 := by push_cast; rfl
        _ ≤ Order.height (LinearMap.range (f ^ (m + 1))) + 1 := by gcongr
        _ ≤ _ := h2
  have h3 := key n 0 (by omega)
  rw [Module.length_eq_height] at hlen
  have h4 : Order.height (LinearMap.range (f ^ 0)) ≤ Order.height (⊤ : Submodule A M) :=
    Order.height_mono le_top
  have h5 : ((n : ℕ) : ℕ∞) + 1 ≤ (n : ℕ∞) := h3.trans (h4.trans hlen)
  norm_cast at h5
  omega
end

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.unipPow :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X → Unip g → InPow 1 ((g - 1) ^ R) := by
  intro l _ X _ _ R g hgen hu
  obtain ⟨N, hN⟩ := hu
  let p : Submodule ℤ_[l] X := LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X))
  have memp : ∀ v : X, v ∈ p ↔ ∃ y, v = (l : ℤ_[l]) ^ 1 • y := by
    intro v
    simp only [p, LinearMap.mem_range, LinearMap.smul_apply, Module.End.one_apply, pow_one]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  have hp : p ≤ p.comap (g - 1) := by
    intro v hv
    obtain ⟨y, rfl⟩ := (memp v).mp hv
    rw [Submodule.mem_comap, map_smul]
    exact (memp _).mpr ⟨(g - 1) y, rfl⟩
  let F : Module.End ℤ_[l] (X ⧸ p) := p.mapQ p (g - 1) hp
  have hFx : ∀ x : X, F (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((g - 1) x) :=
    fun x => Submodule.mapQ_apply _ _ _ x
  have key : ∀ (k : ℕ) (x : X), (F ^ k) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (((g - 1) ^ k) x) := by
    intro k
    induction k with
    | zero =>
      intro x
      simp
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, hFx, ih, pow_succ, Module.End.mul_apply]
  have hnil : IsNilpotent F := by
    refine ⟨N, ?_⟩
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p z
    rw [Submodule.mkQ_apply, key, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, memp]
    exact hN x
  have hlen : Module.length ℤ_[l] (X ⧸ p) ≤ R := cokL l X R hgen
  have hF0 := nilLen ℤ_[l] (X ⧸ p) F R hnil hlen
  intro x
  have hk := key R x
  rw [hF0, LinearMap.zero_apply, eq_comm, Submodule.Quotient.mk_eq_zero, memp] at hk
  exact hk
end

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.phi :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Module.Finite ℤ_[l] X] (w : Module.End ℤ_[l] X), InPow 2 (w - 1) →
      LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) ≤ LinearMap.range (∑ i ∈ Finset.range l, w ^ i) := by
  intro l _ X _ _ _ w hw
  have hpow : ∀ (i : ℕ) (x : X), ∃ y : X, (w ^ i) x = x + (l : ℤ_[l]) ^ 2 • y := by
    intro i
    induction i with
    | zero => intro x; exact ⟨0, by simp⟩
    | succ i ih =>
      intro x
      obtain ⟨y, hy⟩ := ih (w x)
      obtain ⟨z, hz⟩ := hw x
      refine ⟨z + y, ?_⟩
      rw [pow_succ, Module.End.mul_apply, hy, smul_add, ← hz]
      simp only [LinearMap.sub_apply, Module.End.one_apply]
      abel
  have hsum : ∀ (n : ℕ) (x : X), ∃ y : X,
      (∑ i ∈ Finset.range n, w ^ i) x = (n : ℤ_[l]) • x + (l : ℤ_[l]) ^ 2 • y := by
    intro n x
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := hpow n x
      refine ⟨y + z, ?_⟩
      rw [Finset.sum_range_succ, LinearMap.add_apply, hy, hz, smul_add, Nat.cast_succ, add_smul, one_smul]
      abel
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(l : ℤ_[l])}) ?_ ?_ ?_
  · exact IsNoetherian.noetherian _
  · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hsum l x
    have e : ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) x
        = (∑ i ∈ Finset.range l, w ^ i) x + (l : ℤ_[l]) • (((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) (-y)) := by
      rw [hy]
      simp only [LinearMap.smul_apply, Module.End.one_apply, smul_neg, pow_two, mul_smul]
      abel
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (LinearMap.mem_range_self _ _))
end

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.step :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (w : Module.End ℤ_[l] X), GenBy l R X → InPow 2 (w - 1) →
      cokLen (w ^ l - 1) ≤ cokLen (w - 1) + R := by
  intro l _ X _ _ R w hG hw
  haveI : Module.Finite ℤ_[l] X := by
    obtain ⟨π, hπ⟩ := hG
    exact Module.Finite.of_surjective π hπ
  have h1 := (UpperTheory.V.Base.lenComp ℤ_[l] X (∑ i ∈ Finset.range l, w ^ i) (w - 1)).2
  rw [geom_sum_mul] at h1
  have h2 := cokLen_le_of_range_le (phi l X w hw)
  have h3 := cokL l X R hG
  calc cokLen (w ^ l - 1) ≤ cokLen (∑ i ∈ Finset.range l, w ^ i) + cokLen (w - 1) := h1
    _ ≤ R + cokLen (w - 1) := add_le_add_left (h2.trans h3) _
    _ = cokLen (w - 1) + R := add_comm _ _
end

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.mono :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (a b : ℕ), a ∣ b →
      cokLen (g ^ a - 1) ≤ cokLen (g ^ b - 1) := by
  intro l _ X _ _ g a b hab
  apply cokLen_le_of_range_le
  obtain ⟨k, rfl⟩ := hab
  rw [pow_mul, ← mul_geom_sum]
  exact LinearMap.range_comp_le_range _ _
end

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.growth :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X → Unip g → ∀ m : ℕ,
      cokLen (g ^ l ^ m - 1) ≤ cokLen (g ^ l ^ jZero l R - 1) + ((R * (m - jZero l R) : ℕ) : ℕ∞) := by
  intro l _ X _ _ R g hG hU m
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.log l R + 1 := ⟨_, rfl⟩
  have hRk : R ≤ l ^ k := by
    rw [hk]
    exact (Nat.lt_pow_succ_log_self hl R).le
  have hA : InPow 1 ((g - 1) ^ l ^ k) := by
    have h0 := unipPow l X R g hG hU
    have hsplit : (g - 1) ^ l ^ k = (g - 1) ^ (l ^ k - R) * (g - 1) ^ R := by
      rw [← pow_add, Nat.sub_add_cancel hRk]
    intro x
    obtain ⟨y, hy⟩ := h0 x
    refine ⟨((g - 1) ^ (l ^ k - R)) y, ?_⟩
    rw [hsplit, Module.End.mul_apply, hy, map_smul]
  have hB : InPow 2 (g ^ l ^ (k + 1) - 1) := by
    have h := (powIn l X (g ^ l ^ k)).2 ((frob l X g k).1 hA)
    rwa [← pow_mul, ← pow_succ] at h
  have hC : ∀ n, k + 1 ≤ n → InPow 2 (g ^ l ^ n - 1) := by
    intro n hn
    have h := (powIn l X (g ^ l ^ (k + 1))).1 2 (l ^ (n - (k + 1))) hB
    rwa [← pow_mul, ← pow_add, Nat.add_sub_cancel' hn] at h
  have hstep : ∀ n, k + 1 ≤ n → cokLen (g ^ l ^ (n + 1) - 1) ≤ cokLen (g ^ l ^ n - 1) + R := by
    intro n hn
    have h := step l X R (g ^ l ^ n) hG (hC n hn)
    rwa [← pow_mul, ← pow_succ] at h
  have main : ∀ d, cokLen (g ^ l ^ (jZero l R + d) - 1) ≤
      cokLen (g ^ l ^ jZero l R - 1) + ((R * d : ℕ) : ℕ∞) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      calc cokLen (g ^ l ^ (jZero l R + (d + 1)) - 1) = cokLen (g ^ l ^ (jZero l R + d + 1) - 1) := rfl
        _ ≤ cokLen (g ^ l ^ (jZero l R + d) - 1) + R := hstep _ (by simp only [jZero]; omega)
        _ ≤ cokLen (g ^ l ^ jZero l R - 1) + ((R * d : ℕ) : ℕ∞) + R := add_le_add_left ih _
        _ = cokLen (g ^ l ^ jZero l R - 1) + ((R * (d + 1) : ℕ) : ℕ∞) := by
            push_cast
            ring
  rcases le_total m (jZero l R) with hm | hm
  · rw [Nat.sub_eq_zero_of_le hm, mul_zero, Nat.cast_zero, add_zero]
    exact mono l X g _ _ (pow_dvd_pow l hm)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left]
    exact main d
end

section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.twist :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (a : ℤ_[l]), (l : ℤ_[l]) ∣ a - 1 →
      Unip g → Unip (a • g) := by
  intro l _ X _ _ g a ha hg
  obtain ⟨N, hN⟩ := hg
  obtain ⟨c, hc⟩ := ha
  have left : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (h * f) := by
    intro f h hf v
    obtain ⟨w, hw⟩ := hf v
    exact ⟨h w, by rw [Module.End.mul_apply, hw, map_smul]⟩
  have right : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (f * h) := by
    intro f h hf v
    exact hf (h v)
  have zero : InPow 1 (0 : Module.End ℤ_[l] X) := fun v => ⟨0, by simp⟩
  have add : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 h → InPow 1 (f + h) := by
    intro f h hf hh v
    obtain ⟨w, hw⟩ := hf v
    obtain ⟨u, hu⟩ := hh v
    exact ⟨w + u, by rw [LinearMap.add_apply, hw, hu, smul_add]⟩
  have hB : InPow 1 ((a - 1) • g) := by
    intro v
    refine ⟨c • g v, ?_⟩
    rw [LinearMap.smul_apply, hc, mul_smul, pow_one]
  have hcomm : Commute (g - 1) ((a - 1) • g) :=
    ((Commute.refl g).sub_left (Commute.one_left g)).smul_right (a - 1)
  have hsplit : a • g - 1 = (g - 1) + (a - 1) • g := by
    rw [sub_smul, one_smul]
    abel
  refine ⟨N, ?_⟩
  rw [hsplit, hcomm.add_pow]
  refine Finset.sum_induction _ (InPow 1) add zero ?_
  intro m hm
  rcases Nat.lt_or_ge m N with hlt | hge
  · obtain ⟨k, hk⟩ : ∃ k, N - m = k + 1 := ⟨N - m - 1, by omega⟩
    rw [hk, pow_succ']
    apply right
    rw [← mul_assoc]
    apply right
    exact left _ _ hB
  · have hmN : m = N := by
      simp only [Finset.mem_range] at hm
      omega
    subst hmN
    exact right _ _ (right _ _ hN)
end

section
open UpperTheory.V UpperTheory.V.PropA

namespace UpperTheory.V.PropA

variable {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module ℤ_[l] X]

theorem twLen_le_growth {R c : ℕ} {γ : Module.End ℤ_[l] X} {u : ℤ_[l]} (hX : GenBy l R X) (hγ : Unip γ) (hu : IsLevel l u c)
    (e m : ℕ) : twLen γ u e m ≤ twLen γ u e (jZero l R) + ((R * (m - jZero l R) : ℕ) : ℕ∞) := by
  have h1 := (lteNorm l u c hu).2.1
  have hd : (l : ℤ_[l]) ∣ u ^ e - 1 := h1.trans (by simpa using sub_dvd_pow_sub_pow u 1 e)
  exact growth l X R _ hX (twist l X γ _ hd hγ) m

theorem exists_centres_level {R c : ℕ} (γ : Module.End ℤ_[l] X) {u : ℤ_[l]} (hX : GenBy l R X) (hu : IsLevel l u c) (j : ℕ) :
    ∃ s : Fin R → ℤ_[l], ∀ e : ℕ, twLen γ u e j ≤ ∑ i, (((j + c : ℕ) : ℕ∞) + vl l (s i - e)) := by
  obtain ⟨S, hS⟩ := lift l X R (γ ^ l ^ j) hX
  obtain ⟨s, hs⟩ := detBound l u c hu j R S
  refine ⟨s, fun e => ?_⟩
  have hpow : (u ^ e • γ) ^ l ^ j = (u ^ l ^ j) ^ e • γ ^ l ^ j := by
    rw [smul_pow, ← pow_mul, ← pow_mul, mul_comm]
  show cokLen ((u ^ e • γ) ^ l ^ j - 1) ≤ _
  rw [hpow]
  exact (hS _).trans (hs e)

theorem exists_centres {R c : ℕ} {γ : Module.End ℤ_[l] X} {u : ℤ_[l]} (hX : GenBy l R X) (hγ : Unip γ) (hu : IsLevel l u c) :
    ∃ s : Fin R → ℤ_[l], ∀ e m : ℕ,
      twLen γ u e m ≤ ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e)) := by
  obtain ⟨s, hs⟩ := exists_centres_level γ hX hu (jZero l R)
  refine ⟨s, fun e m => ?_⟩
  refine (twLen_le_growth hX hγ hu e m).trans ?_
  have hm : max m (jZero l R) + c = (jZero l R + c) + (m - jZero l R) := by omega
  have key : ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e))
      = ∑ i, (((jZero l R + c : ℕ) : ℕ∞) + vl l (s i - e)) + ((R * (m - jZero l R) : ℕ) : ℕ∞) := by
    rw [hm]
    simp only [Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [key]
  gcongr
  exact hs e

theorem vl_le_of_norm {x : ℤ_[l]} {B : ℕ} (h : (l : ℝ) ^ (-(B : ℤ)) ≤ ‖x‖) : vl l x ≤ B := by
  have h' : ∏ _i : Fin 1, ((l : ℝ) ^ B)⁻¹ * ‖(1 : ℤ_[l])‖ ≤ ‖x‖ := by
    simpa [zpow_neg, zpow_natCast] using h
  have := normVal l 1 B x (fun _ => 1) h'
  simpa [vl] using this

theorem exists_centres_norm {R c : ℕ} {γ : Module.End ℤ_[l] X} {u : ℤ_[l]} (hX : GenBy l R X) (hγ : Unip γ)
    (hu : IsLevel l u c) : ∃ s : Fin R → ℤ_[l], ∀ e m B : ℕ, (∀ i, (l : ℝ) ^ (-(B : ℤ)) ≤ ‖s i - e‖) →
      twLen γ u e m ≤ ((R * (max m (jZero l R) + c + B) : ℕ) : ℕ∞) := by
  obtain ⟨s, hs⟩ := exists_centres hX hγ hu
  refine ⟨s, fun e m B hB => (hs e m).trans ?_⟩
  calc ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e))
        ≤ ∑ _i : Fin R, (((max m (jZero l R) + c + B : ℕ) : ℕ∞)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Nat.cast_add _ B]
          gcongr
          exact vl_le_of_norm (hB i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]

end UpperTheory.V.PropA
end
