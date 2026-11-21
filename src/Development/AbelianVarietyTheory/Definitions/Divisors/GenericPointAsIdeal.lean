import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArithBase GlobalTheory.CechPic

namespace GlobalTheory.ArInt.Model

def IsConst (L : HermLB (𝟙 (Sp ℤ))) (t : ℝ) : Prop :=
  ∀ i, (∀ x, x ∈ L.B.U i) ∧ ∀ σ y, (L.φ σ).φ i y = 2 * t



variable {L M : HermLB (𝟙 (Sp ℤ))} {s t : ℝ}

theorem IsConst.tens (h : IsConst L s) (h' : IsConst M t) : IsConst (L.tens M) (s + t) :=
  fun i => ⟨fun x => ⟨(h i.1).1 x, (h' i.2).1 x⟩, fun σ y =>
    (congrArg₂ (· + ·) ((h i.1).2 σ y) ((h' i.2).2 σ y)).trans (by ring)⟩

theorem IsConst.dual (h : IsConst L s) : IsConst L.dual (-s) :=
  fun i => ⟨(h i).1, fun σ y => (congrArg (- ·) ((h i).2 σ y)).trans (by ring)⟩

theorem IsConst.pow (h : IsConst L s) (m : ℕ) : IsConst (L.pow m) (m * s) :=
  fun i => ⟨fun x => Set.mem_iInter.2 fun _ => (h _).1 x, fun σ y =>
    ((L.φ σ).zpow_φ _ i y).trans (by rw [(h _).2]; push_cast; ring)⟩

theorem IsConst.zp (h : IsConst L s) (n : ℤ) : IsConst (zp L n) (n * s) := by
  have := (h.pow n.toNat).tens (h.pow (-n).toNat).dual
  have e : (n : ℝ) = (n.toNat : ℝ) - ((-n).toNat : ℝ) := by exact_mod_cast (Int.toNat_sub_toNat_neg n).symm
  rw [show (n : ℝ) * s = n.toNat * s + -((-n).toNat * s) by rw [← sub_eq_add_neg, ← sub_mul, ← e]]
  exact this


open Classical in

theorem IsConst.isArithHeight (h : IsConst L t) : L.IsArithHeight fun x =>
    if x.asIdeal = ⊥ then t else Real.log (Nat.card (ℤ ⧸ x.asIdeal)) where
  vertical Z i _ _ κ _ _ _ d hd := by
    have := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
    have hinj := (algebraMap κ Γ(Z, ⊤)).injective
    have hb : Function.Bijective (algebraMap κ Γ(Z, ⊤)) := ⟨hinj, fun a =>
      have ⟨n, hn⟩ := surjective_intCast i a
      ⟨n, (map_intCast _ n).trans hn⟩⟩
    obtain rfl : d = 0 := by
      rw [IsHomeomorph.topologicalKrullDim_eq _ Z.isoSpec.hom.homeomorph.isHomeomorph] at hd
      have := hd.symm.trans ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans
        ((ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)).symm.trans (ringKrullDim_eq_zero_of_field κ)))
      exact_mod_cast this
    have h0 := (isArithHeight_trivShift t).vertical Z i κ 0 hd
    rw [topSelfIntersection, interNum_of_isEmpty] at h0 ⊢
    exact h0
  point Z i _ _ _ hc _ r hr := by
    have := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
    let e := RingEquiv.ofBijective (Int.castRingHom Γ(Z, ⊤))
      ⟨Int.cast_injective, surjective_intCast i⟩
    have h0 : (i (genericPoint Z)).asIdeal = ⊥ := eq_bot_iff.2 fun n hn =>
      Int.cast_eq_zero.1 ((mem_asIdeal_iff i n).1 hn)
    let σ := Int.castRingHom ℂ
    let y : CxPts (i ≫ 𝟙 _) σ := ofHom (isAffineOpen_top Z) (σ.comp e.symm) fun a =>
      RingHom.congr_fun (RingHom.ext_int ((σ.comp e.symm.toRingHom).comp
        (DVR.FlatBC.algX (i ≫ 𝟙 _) ⊤)) σ) a
    have hy (y' : CxPts (i ≫ 𝟙 _) σ) : y' = y :=
      Subtype.ext ((cancel_mono (i ≫ 𝟙 _)).1 (y'.2.trans y.2.symm))
    let j := pick ((L.restr i).φ σ).isLB y
    have hj (z : Z) : ((L.restr i).div hr).mult z = Scheme.ord (r j : Z.functionField) z :=
      ((presents_divOfRatSec _ hr).isEqn j z (Set.mem_iInter.2 fun _ => (h _).1 _)).mult_eq
    have e' : ((L.restr i).φ σ).φ j y = 2 * t := ((L.φ σ).pull_φ i rfl j y).trans ((h _).2 _ _)
    rw [if_pos h0, HermLB.curveDeg, finsum_eq_single _ σ fun σ' h => absurd (RingHom.ext_int _ _) h,
      finsum_eq_single _ y fun y' h => absurd (hy y') h, logNorm]
    simp only [hj]
    rw [(product_formula e y (r j).ne_zero).2]
    rw [e']
    ring
  recursion Z i _ _ _ _ e he hd := by
    have := hd.ge.trans (i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      isArithVar_int.dim_eq.le)
    norm_cast at this
    omega

theorem genericPoint_asIdeal : (genericPoint (Sp ℤ)).asIdeal = ⊥ := Ideal.ext fun n =>
    (mem_asIdeal_iff (𝟙 (Sp ℤ)) n).trans (have := isArithVar_int.charZero; Int.cast_eq_zero)

theorem IsConst.isSelfInter (h : IsConst L t) : L.IsSelfInter t :=
  ⟨_, h.isArithHeight, if_pos genericPoint_asIdeal⟩

def linFun {ι : Type} [Fintype ι] (t : ι → ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
  ∑ i, t i • lcoeff ℝ (Finsupp.single i 1)




theorem arVol_nonneg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (D : ℕ) : 0 ≤ arVol L D := by
  refine le_limsup_of_frequently_le (Frequently.of_forall fun m => ?_)
  refine mul_nonneg ?_ (EReal.coe_nonneg.2 (by positivity))
  rw [ENNReal.zero_le_log_iff]
  exact_mod_cast Set.one_le_encard_iff_nonempty.2 ⟨_, (L.pow m).zero_mem_smallSec⟩

theorem eq_zero_of_pow {ι : Type} [Fintype ι] (d : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (h : ∀ n : ι → ℤ, Φ (lin (fun i => (n i : ℝ)) ^ d) = 0)
    (h' : ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d → P.IsHomogeneous e → Φ P = 0) : Φ = 0 := by
  classical
  let Q : MvPolynomial ι ℝ := ∑ a ∈ (Finset.univ : Finset ι).piAntidiag d,
    monomial (Finsupp.equivFunOnFinite.symm a) ((Nat.multinomial Finset.univ a : ℝ) *
      Φ (monomial (Finsupp.equivFunOnFinite.symm a) 1))
  have hQ (x : ι → ℝ) : eval x Q = Φ (lin x ^ d) := by
    rw [lin, Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e : (Nat.multinomial Finset.univ a : MvPolynomial ι ℝ) * ∏ i, (C (x i) * MvPolynomial.X i) ^ a i =
        ((Nat.multinomial Finset.univ a : ℝ) * ∏ i, x i ^ a i) • monomial (Finsupp.equivFunOnFinite.symm a) (1 : ℝ) := by
      rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), smul_eq_C_mul]
      simp [mul_pow, Finset.prod_mul_distrib, mul_assoc]
    rw [e, map_smul, eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp only [Finsupp.coe_equivFunOnFinite_symm, smul_eq_mul]
    ring
  have h0 : Q = 0 := by
    refine funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    choose n hn using fun i => hx i trivial
    rw [hQ, map_zero, ← h n]
    congr 3
    exact funext fun i => (hn i).symm
  refine (basisMonomials ι ℝ).ext fun a => ?_
  rw [coe_basisMonomials]
  by_cases ha : a.degree = d
  · have := congrArg (coeff a) h0
    simp only [Q, coeff_sum, coeff_monomial, Equiv.symm_apply_eq, Finset.sum_ite_eq', coeff_zero] at this
    rw [if_pos (by simp [← ha, Finsupp.degree_eq_sum])] at this
    simpa [(Nat.multinomial_pos _ _).ne'] using this
  · exact h' _ _ ha (isHomogeneous_monomial _ rfl)

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem lin_pow_eq_eval_sum_multinomial {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ) (r : ι → ℝ) :
    Ψ (_root_.GlobalTheory.ArInt.lin r ^ m) =
      MvPolynomial.eval r (∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial Finset.univ k : ℝ) *
            Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1))) := by
  unfold _root_.GlobalTheory.ArInt.lin
  rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∏ i, (MvPolynomial.C (r i) * MvPolynomial.X i) ^ k i =
      MvPolynomial.C (∏ i, r i ^ k i) *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [mul_pow, Finset.prod_mul_distrib, map_prod]
  rw [hk, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← mul_assoc, ← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ), ← map_mul,
    ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
  simp
  ring

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero {ι : Type} [Fintype ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ)
    (hΨ : ∀ n : ι → ℤ, Ψ (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ m) = 0)
    {P : MvPolynomial ι ℝ} (hP : P.IsHomogeneous m) : Ψ P = 0 := by
  classical
  set Q : MvPolynomial ι ℝ := ∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) *
        Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1)) with hQdef
  have hQ : Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    choose n hn using fun i => hx i (Set.mem_univ i)
    have hxn : x = fun i => (n i : ℝ) := funext fun i => (hn i).symm
    rw [map_zero, hxn, hQdef, ← lin_pow_eq_eval_sum_multinomial, hΨ]
  have hmon : ∀ d : ι →₀ ℕ, (Finsupp.weight 1) d = m →
      Ψ (MvPolynomial.monomial d 1) = 0 := by
    intro d hd
    have hmem : ⇑d ∈ (Finset.univ : Finset ι).piAntidiag m := by
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp
    have hc := congrArg (MvPolynomial.coeff d) hQ
    rw [hQdef, MvPolynomial.coeff_sum, Finset.sum_eq_single (⇑d)] at hc
    · rw [Finsupp.equivFunOnFinite_symm_coe, MvPolynomial.coeff_monomial, if_pos rfl,
        MvPolynomial.coeff_zero] at hc
      have hne : (Nat.multinomial Finset.univ ⇑d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.multinomial_pos _ _).ne'
      exact (mul_eq_zero.mp hc).resolve_left hne
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro heq
      apply hb
      rw [← heq]
      simp
    · intro h
      exact absurd hmem h
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hP (MvPolynomial.mem_support_iff.mp hd)
  have hsm : MvPolynomial.monomial d (MvPolynomial.coeff d P) =
      MvPolynomial.coeff d P • MvPolynomial.monomial d (1 : ℝ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, hmon d hw, smul_zero]

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in

theorem _root_.GlobalTheory.ArInt.Model.isArFun_unique {k : Type} [CommRing k] {X : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {D E : ℕ} (hX : _root_.GlobalTheory.IsArithVar p E)
    {ι : Type} [Fintype ι] {L : ι → _root_.GlobalTheory.HermLB p}
    {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : _root_.GlobalTheory.ArInt.IsArFun L D Φ)
    (h' : _root_.GlobalTheory.ArInt.IsArFun L D Φ') :
    Φ = Φ' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hpow : ∀ n : ι → ℤ,
      (Φ - Φ') (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ (D + 1)) = 0 := by
    intro n
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact _root_.GlobalTheory.HermLB.IsSelfInter.unique hX
      (h1 n) (h1' n)
  have hhom : ∀ (P : MvPolynomial ι ℝ) (d : ℕ), P.IsHomogeneous d → Φ P = Φ' P := by
    intro P d hP
    by_cases hd : d = D + 1
    · subst hd
      exact sub_eq_zero.mp (eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero (Φ - Φ') (D + 1) hpow hP)
    · rw [h2 P d hd hP, h2' P d hd hP]
  refine LinearMap.ext fun P => ?_
  rw [← MvPolynomial.sum_homogeneousComponent P, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    hhom _ j (MvPolynomial.homogeneousComponent_isHomogeneous j P)

theorem isGeoFun_unique {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    {ι : Type} [Fintype ι] {L : ι → HermLB p} {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : IsGeoFun L D Φ) (h' : IsGeoFun L D Φ') :
    Φ = Φ' :=
  sub_eq_zero.1 (eq_zero_of_pow D _ (fun n => sub_eq_zero.2 ((h.1 n).trans (h'.1 n).symm))
    fun P e he hP => sub_eq_zero.2 ((h.2 P e he hP).trans (h'.2 P e he hP).symm))








end GlobalTheory.ArInt.Model
