import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois
import GroundTheory.GlobalFields.ComplexMultiplication.DualDescent
import GroundTheory.GlobalFields.ComplexMultiplication.IsogenyDegreeOne
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionNumberField
import GroundTheory.GlobalFields.ComplexMultiplication.GoodReductionAlmostAll
import GroundTheory.GlobalFields.ComplexMultiplication.PrimeLocalization
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionGauss
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent

section
namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IsDedekindDomain
open scoped nonZeroDivisors

universe u

section VC

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E₁ E₁' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E₁.IsElliptic]
  [E₁'.IsElliptic]

theorem homConstSet_vc_pair (C C' : VariableChange F) (h : C • E = E₁) (h' : C' • E' = E₁') :
    ∃ c : F, c ≠ 0 ∧ (homConstSet E₁ E₁' : Set F) = (c * ·) '' homConstSet E E' ∧
      (homConstSet E₁' E₁ : Set F) = (c⁻¹ * ·) '' homConstSet E' E := by
  set Q := vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)
  set R := vcHom C' h'
  set Q' := vcHom C h
  set R' := vcHom C'⁻¹ (inv_smul_eq_of_smul_eq C' h')
  have e1 : homConst E₁ E Q * homConst E E₁ Q' = 1 := homConst_vcHom_mul_inv C h
  have e2 : homConst E₁' E' R' * homConst E' E₁' R = 1 := homConst_vcHom_mul_inv C' h'
  set c := homConst E' E₁' R * homConst E₁ E Q
  have hc : c * (homConst E₁' E' R' * homConst E E₁ Q') = 1 := by
    linear_combination (homConst E₁' E' R' * homConst E' E₁' R) * e1 + e2
  have hcinv : c⁻¹ = homConst E E₁ Q' * homConst E₁' E' R' := by
    rw [inv_eq_of_mul_eq_one_right hc, mul_comm]
  refine ⟨c, left_ne_zero_of_mul_eq_one hc, ?_, ?_⟩
  · ext z
    simp only [SetLike.mem_coe, Set.mem_image]
    constructor
    · intro hz
      refine ⟨homConst E₁' E' R' * z * homConst E E₁ Q', homConstSet_le_mul Q' R' hz, ?_⟩
      linear_combination z * hc
    · rintro ⟨w, hw, rfl⟩
      have := homConstSet_le_mul Q R hw
      convert this using 1
      ring
  · ext z
    simp only [SetLike.mem_coe, Set.mem_image]
    constructor
    · intro hz
      refine ⟨homConst E₁ E Q * z * homConst E' E₁' R, homConstSet_le_mul R Q hz, ?_⟩
      rw [hcinv]
      linear_combination z * hc
    · rintro ⟨w, hw, rfl⟩
      have := homConstSet_le_mul R' Q' hw
      convert this using 1
      rw [hcinv]
      ring

end VC

section Invariant

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem invConst_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    invConst (ψ.comp φ) = invConst ψ * invConst φ := by
  rw [← homConst_toHom, ← Isogeny.homComp_toHom, homConst_homComp, homConst_toHom, homConst_toHom]

theorem invConst_mem_homConstSet (φ : Isogeny E E') : invConst φ ∈ homConstSet E E' :=
  mem_homConstSet.2 ⟨φ.toHom, homConst_toHom φ⟩

theorem invConst_dualOver_mul (φ : Isogeny E E') :
    invConst (dualOver φ) * invConst φ = φ.degree := by
  rw [← invConst_comp, dualOver_comp, invConst_mulIsogeny]
  push_cast
  rfl

variable [CharZero F]

theorem invConst_ne_zero (φ : Isogeny E E') : invConst φ ≠ 0 := by
  intro h
  have := invConst_dualOver_mul φ
  rw [h, mul_zero] at this
  exact (Nat.cast_ne_zero.2 φ.degree_pos.ne') this.symm

end Invariant

section Lattice

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ)

theorem idealLattice_one_mul_lattice (L : PeriodPair) (hL : latticeEnd L = cmRing σ₀) :
    idealLattice σ₀ 1 * L.lattice = L.lattice := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm l hl
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ₀).1 hm
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    have ha : σ₀ (algebraMap (𝓞 K) K a) ∈ latticeEnd L := hL ▸ (mem_cmRing σ₀).2 ⟨a, rfl⟩
    exact ha l hl
  · intro l hl
    have h1 : (1 : ℂ) ∈ idealLattice σ₀ 1 :=
      (mem_idealLattice σ₀).2 ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, map_one σ₀⟩
    simpa using Submodule.mul_mem_mul h1 hl

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]

theorem homConstSet_pair_of_smul {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll) :
    ∃ c : ℂ, c ≠ 0 ∧ (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ ∧
      (homConstSet E'.curve E.curve : Set ℂ) = (c⁻¹ * ·) '' idealLattice σ₀ ↑𝔞 := by
  obtain ⟨L, C, hL, hC, hE⟩ := E.exists_lattice σ₀ hK
  obtain ⟨L', hL'lat, hL'⟩ := exists_lattice_mul σ₀ hK L hL 𝔞
  have h1 := classGroup_smul_ellOf σ₀ hK L L' hL hL' 𝔞 hL'lat
  have h2 : E'.toEll = (CMCurve.ofLattice σ₀ L' hL').toEll := by
    rw [← h, ← hE]
    exact h1
  obtain ⟨C', hC'⟩ := (CMCurve.toEll_eq_iff _ _).1 h2
  have hC'' : C' • E'.curve = weierstrassCurve L' := hC'
  obtain ⟨d, hd, hset, hset'⟩ := homConstSet_vc_pair C C' hC hC''
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL'lat] at hset
  have hLL : L.lattice = idealLattice σ₀ ↑𝔞 * L'.lattice := by
    rw [hL'lat, ← mul_assoc, ← idealLattice_mul, Units.mul_inv, idealLattice_one_mul_lattice σ₀ L hL]
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L' L hL' 𝔞 hLL] at hset'
  exact ⟨d⁻¹, inv_ne_zero hd, eq_image_mul_inv hd hset, eq_image_mul_inv (inv_ne_zero hd) hset'⟩

include hK in

theorem homConstSet_symm {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {b : ℂ} (hb : b ≠ 0)
    (hset : (homConstSet E.curve E'.curve : Set ℂ) = (b * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    (homConstSet E'.curve E.curve : Set ℂ) = (b⁻¹ * ·) '' idealLattice σ₀ ↑𝔞 := by
  obtain ⟨c, hc, h1, h2⟩ :=
    homConstSet_pair_of_smul σ₀ hK (smul_toEll_of_homConstSet σ₀ hK hb hset)

  have e : (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = ((c⁻¹ * b) * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [← image_mul_image_mul, ← hset, h1, image_mul_image_mul, inv_mul_cancel₀ hc]
    simp

  have e' := idealLattice_mul_homothetic σ₀ (↑𝔞⁻¹) (↑𝔞 * ↑𝔞) e
  have hmul : (↑𝔞 * ↑𝔞 * ↑𝔞⁻¹ : FractionalIdeal (𝓞 K)⁰ K) = ↑𝔞 := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [← idealLattice_mul, hmul] at e'
  rw [h2]
  calc (c⁻¹ * ·) '' (idealLattice σ₀ ↑𝔞 : Set ℂ)
      = (c⁻¹ * ·) '' (((c⁻¹ * b)⁻¹ * ·) '' (idealLattice σ₀ ↑𝔞 : Set ℂ)) := by
        rw [← eq_image_mul_inv (mul_ne_zero (inv_ne_zero hc) hb) e']
    _ = (b⁻¹ * ·) '' (idealLattice σ₀ ↑𝔞 : Set ℂ) := by
        rw [image_mul_image_mul]
        congr 2
        field_simp

end Lattice

section Prime

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def primeUnit : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)

theorem primeUnit_val : ((primeUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
    v.asIdeal :=
  rfl

theorem primeUnit_inv_val :
    (((primeUnit v)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, primeUnit_val]

theorem classGroup_mk_primeUnit :
    ClassGroup.mk K (primeUnit v) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  rw [← ClassGroup.mk_mk0 K]
  rfl

theorem absNorm_dvd_of_natCast_mem (hv : (Ideal.absNorm v.asIdeal).Prime) {n : ℕ}
    (hn : (n : 𝓞 K) ∈ v.asIdeal) : Ideal.absNorm v.asIdeal ∣ n := by
  by_contra h
  have hcop : Nat.Coprime (Ideal.absNorm v.asIdeal) n := (Nat.Prime.coprime_iff_not_dvd hv).2 h
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hp : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ∈ v.asIdeal := Ideal.absNorm_mem _
  have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
    have e := congrArg (Int.cast : ℤ → 𝓞 K) hab
    push_cast at e
    rw [← e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hn)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem inv_absNorm_notMem_inv (hK : finrank ℚ K = 2) (hv : (Ideal.absNorm v.asIdeal).Prime) :
    ((Ideal.absNorm v.asIdeal : K))⁻¹ ∉ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  set p := Ideal.absNorm v.asIdeal with hpdef
  intro hmem
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hv.ne_zero
  have hle : v.asIdeal ≤ Ideal.span {(p : 𝓞 K)} := by
    intro y hy
    have h1 := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)).1 hmem
      (algebraMap (𝓞 K) K y) (FractionalIdeal.mem_coeIdeal_of_mem _ hy)
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [Ideal.mem_span_singleton']
    refine ⟨z, IsFractionRing.injective (𝓞 K) K ?_⟩
    rw [map_mul, hz, map_natCast]
    field_simp
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, hK]
    simp
  rw [hnorm] at hdvd
  have := Nat.le_of_dvd hv.pos hdvd
  have h2 := hv.two_le
  nlinarith

end Prime

section Degree

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

include hK in

theorem degree_eq_absNorm {E E' : CMCurve K} (v : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm v.asIdeal).Prime) (φ : Isogeny E.curve E'.curve)
    (hφ : (homConstSet E.curve E'.curve : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    φ.degree = Ideal.absNorm v.asIdeal := by
  classical
  set p := Ideal.absNorm v.asIdeal with hpdef
  set c := invConst φ with hcdef
  have hc : c ≠ 0 := invConst_ne_zero φ
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hv.ne_zero
  have hφu : (homConstSet E.curve E'.curve : Set ℂ) =
      (c * ·) '' idealLattice σ₀ ↑(primeUnit v)⁻¹ := by
    rw [primeUnit_inv_val]; exact hφ
  have hsym := homConstSet_symm σ₀ hK hc hφu
  rw [primeUnit_val] at hsym

  have hpmem : (p : ℂ) ∈ idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    have hx : ((p : K)) ∈ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
      have := FractionalIdeal.mem_coeIdeal_of_mem (S := (𝓞 K)⁰) (P := K) (Ideal.absNorm_mem v.asIdeal)
      simpa using this
    simpa using map_mem_idealLattice σ₀ hx
  have hν : c⁻¹ * p ∈ homConstSet E'.curve E.curve := by
    have h' : c⁻¹ * (p : ℂ) ∈ (homConstSet E'.curve E.curve : Set ℂ) := by
      rw [hsym]; exact ⟨p, hpmem, rfl⟩
    exact h'
  obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hν
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hQ
    exact mul_ne_zero (inv_ne_zero hc) hp0 hQ.symm
  set ν := isogOfHom Q hQ0 with hνdef
  have hνc : invConst ν = c⁻¹ * p := by rw [← homConst_toHom, isogOfHom_toHom, hQ]

  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hv.ne_zero
  have hcomp : ν.comp φ = mulIsogeny E.curve p hpz := by
    have h1 : endConst E.curve (ν.comp φ).toHom = endConst E.curve (mulIsogeny E.curve p hpz).toHom := by
      rw [endConst_apply, endConst_apply, homConst_toHom, homConst_toHom, invConst_comp, hνc,
        invConst_mulIsogeny]
      field_simp
      push_cast
      ring
    have h2 := congrArg Subtype.val (endConst_injective h1)
    exact Subtype.ext h2
  have hdeg1 : ν.degree * φ.degree = p ^ 2 := by
    rw [← Isogeny.degree_comp, hcomp, degree_mulIsogeny]
    simp

  have hdvd : p ∣ φ.degree := by
    have hd : invConst (dualOver φ) ∈ (homConstSet E'.curve E.curve : Set ℂ) :=
      invConst_mem_homConstSet _
    rw [hsym] at hd
    obtain ⟨z, hz, hz'⟩ := hd
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ₀).1 hz
    have e := invConst_dualOver_mul φ
    rw [← hcdef, ← hz'] at e
    simp only at e
    have hx' : σ₀ x = σ₀ (φ.degree : K) := by
      rw [map_natCast, ← e]
      field_simp
    have hxK : x = φ.degree := σ₀.injective hx'
    rw [hxK] at hx
    obtain ⟨y, hy, hy'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    have : y = (φ.degree : 𝓞 K) := IsFractionRing.injective (𝓞 K) K (by rw [hy', map_natCast])
    rw [this] at hy
    exact absNorm_dvd_of_natCast_mem v hv hy
  obtain ⟨k, hk, hkdeg⟩ := (Nat.dvd_prime_pow hv).1 (Dvd.intro_left _ hdeg1)
  interval_cases k
  · rw [hkdeg, pow_zero] at hdvd
    exact absurd (Nat.le_of_dvd one_pos hdvd) (by have := hv.two_le; omega)
  · rw [hkdeg, pow_one]
  · exfalso
    have hν1 : ν.degree = 1 := by
      rw [hkdeg] at hdeg1
      have hp2 : 0 < p ^ 2 := pow_pos hv.pos 2
      nlinarith
    have e := invConst_dualOver_mul ν
    rw [hν1, hνc, Nat.cast_one] at e
    have hd : invConst (dualOver ν) ∈ (homConstSet E.curve E'.curve : Set ℂ) :=
      invConst_mem_homConstSet _
    rw [hφ] at hd
    obtain ⟨z, hz, hz'⟩ := hd
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ₀).1 hz
    rw [← hz'] at e
    simp only at e
    have e2 : σ₀ x * p = 1 := by
      rw [← e]
      field_simp
    have hx' : σ₀ x = σ₀ ((p : K))⁻¹ := by
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left e2
    rw [σ₀.injective hx'] at hx
    exact inv_absNorm_notMem_inv v hK hv hx

include hK in

theorem exists_isogeny_homConstSet_eq {E E' : CMCurve K} (v : HeightOneSpectrum (𝓞 K))
    (h : (ellMulAction σ₀ hK).smul
      (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) E.toEll = E'.toEll) :
    ∃ φ : Isogeny E.curve E'.curve, (homConstSet E.curve E'.curve : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  classical
  rw [← classGroup_mk_primeUnit] at h
  obtain ⟨c, hc, hset⟩ := homConstSet_of_smul σ₀ hK h
  rw [primeUnit_inv_val] at hset
  have h1 : (1 : ℂ) ∈ idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    simpa using map_mem_idealLattice σ₀ (FractionalIdeal.one_mem_inv_coe_ideal v.ne_bot)
  have hcmem : c ∈ homConstSet E.curve E'.curve := by
    have h' : c ∈ (homConstSet E.curve E'.curve : Set ℂ) := by
      rw [hset]; exact ⟨1, h1, mul_one c⟩
    exact h'
  obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hcmem
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hQ
    exact hc hQ.symm
  refine ⟨isogOfHom Q hQ0, ?_⟩
  rw [← homConst_toHom, isogOfHom_toHom, hQ]
  exact hset

end Degree

end

end Elliptic
end GroundTheory.Global
end

section
namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian

universe u

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (F : Type u) [Field F] [Algebra 𝒪 F] [IsFractionRing 𝒪 F] {W W' : WeierstrassCurve 𝒪}
  [W.IsElliptic] [W'.IsElliptic]

theorem invConst_reduceIsogeny_eq_zero (φ : Isogeny (W.baseChange F) (W'.baseChange F)) {c : 𝒪}
    (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    invConst (reduceIsogeny F W W' φ) = 0 := by
  obtain ⟨c', h1, h2⟩ := exists_invConst_reduceIsogeny F W W' φ
  have e : c' = c := IsFractionRing.injective 𝒪 F (h1.trans hφ.symm)
  rw [← h2, e]
  exact (residue_eq_zero_iff c).2 hc

theorem isogenyPullback_reduceIsogeny_eq_zero (φ : Isogeny (W.baseChange F) (W'.baseChange F))
    {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    isogenyPullback (reduceIsogeny F W W' φ) (invariantDifferential (W'.map (residue 𝒪))) = 0 := by
  rw [isogenyPullback_eq_invConst_smul, invConst_reduceIsogeny_eq_zero F φ hc hφ, zero_smul]

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField 𝒪) p] [PerfectRing (ResidueField 𝒪) p]

theorem reduceIsogeny_eq_comp_frobeniusIsogeny (φ : Isogeny (W.baseChange F) (W'.baseChange F))
    (hdeg : φ.degree = p) {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    ∃ ψ : Isogeny (frobeniusTwist (W.map (residue 𝒪)) p) (W'.map (residue 𝒪)),
      reduceIsogeny F W W' φ = ψ.comp (frobeniusIsogeny (W.map (residue 𝒪)) p) ∧
      ψ.degree = 1 ∧ Function.Bijective ψ.comap ∧
      (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
      ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero :=
  exists_isomorphism_of_degree_eq p _ (isogenyPullback_reduceIsogeny_eq_zero F φ hc hφ)
    (by rw [degree_reduceIsogeny, hdeg])

theorem residue_j_eq_pow (φ : Isogeny (W.baseChange F) (W'.baseChange F)) (hdeg : φ.degree = p)
    {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    residue 𝒪 W'.j = residue 𝒪 W.j ^ p := by
  rw [← j_map_residue, ← j_map_residue]
  exact j_eq_pow_of_isogenyPullback_eq_zero p _ (isogenyPullback_reduceIsogeny_eq_zero F φ hc hφ)
    (by rw [degree_reduceIsogeny, hdeg])

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global

open NumberField IsDedekindDomain IsLocalRing Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

noncomputable section

def functionFieldCongr {F : Type*} [Field F] {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.FunctionField ≃+* V'.toAffine.FunctionField := by
  subst h
  exact RingEquiv.refl _

@[simp]
theorem functionFieldCongr_self {F : Type*} [Field F] {V : WeierstrassCurve F} (h : V = V)
    (x : V.toAffine.FunctionField) : functionFieldCongr h x = x :=
  rfl

variable {L : Type*} [Field L] [NumberField L]

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global

open NumberField IsDedekindDomain IsLocalRing WeierstrassCurve.Affine

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem under_eq_of_liesOver {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.LiesOver v.asIdeal) : w.under (𝓞 K) = v :=
  HeightOneSpectrum.ext h.over.symm

theorem exists_finite_forall_liesOver {p : HeightOneSpectrum (𝓞 L) → Prop}
    (hp : ∀ᶠ w in Filter.cofinite, p w) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v ∉ T, ∀ w : HeightOneSpectrum (𝓞 L),
      w.asIdeal.LiesOver v.asIdeal → p w := by
  refine ⟨(fun w => w.under (𝓞 K)) '' {w | ¬ p w}, (Filter.eventually_cofinite.mp hp).image _,
    fun v hv w hw => by_contra fun hn => hv ⟨w, hn, under_eq_of_liesOver hw⟩⟩

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Residue

variable {L : Type*} [Field L] [NumberField L] (𝔓 : HeightOneSpectrum (𝓞 L))

instance finite_residueField_localizationAt : Finite (ResidueField (localizationAt L 𝔓)) :=
  Finite.of_equiv _
    (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔓.asIdeal (localizationAt L 𝔓)).toEquiv

theorem algebraMap_mem_maximalIdeal_localizationAt_iff (a : 𝓞 L) :
    algebraMap (𝓞 L) (localizationAt L 𝔓) a ∈ maximalIdeal (localizationAt L 𝔓) ↔ a ∈ 𝔓.asIdeal :=
  IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ a

theorem charP_residueField_localizationAt {p : ℕ} (hp : p.Prime) (hmem : (p : 𝓞 L) ∈ 𝔓.asIdeal) :
    CharP (ResidueField (localizationAt L 𝔓)) p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  have h := (algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 p).2 hmem
  rw [map_natCast] at h
  rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), residue_eq_zero_iff]
  exact h

variable {K : Type*} [Field K] [Algebra K L]

theorem residue_smul_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    (a : 𝓞 L) :
    IsLocalRing.residue (localizationAt L 𝔓) (algebraMap (𝓞 L) _ (σ • a)) =
      IsLocalRing.residue (localizationAt L 𝔓) (algebraMap (𝓞 L) _ a) ^
        Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  rw [← sub_eq_zero, ← map_pow, ← map_sub, residue_eq_zero_iff, ← map_pow, ← map_sub,
    algebraMap_mem_maximalIdeal_localizationAt_iff]
  exact hσ a

omit [NumberField L] in

theorem smul_notMem_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    {s : 𝓞 L} (hs : s ∉ 𝔓.asIdeal) : σ • s ∉ 𝔓.asIdeal := by
  intro h
  apply hs
  have h' : s ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) ∈ 𝔓.asIdeal := by
    have := 𝔓.asIdeal.sub_mem h (hσ s)
    simpa using this
  exact 𝔓.isPrime.mem_of_pow_mem _ h'

theorem residue_apply_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    {x : L} (hx : x ∈ localizationAt L 𝔓) :
    ∃ h : σ x ∈ localizationAt L 𝔓, IsLocalRing.residue (localizationAt L 𝔓) ⟨σ x, h⟩ =
      IsLocalRing.residue (localizationAt L 𝔓) ⟨x, hx⟩ ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  set q := Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K))
  obtain ⟨a, s, hs, hxs⟩ := mem_localizationAt_iff.1 hx
  have hs0 : (algebraMap (𝓞 L) L s) ≠ 0 := by
    intro h0
    apply hs
    rw [(IsFractionRing.injective (𝓞 L) L) (h0.trans (map_zero _).symm)]
    exact 𝔓.asIdeal.zero_mem
  have hσs := smul_notMem_of_isArithFrobAt 𝔓 hσ hs
  have hσs0 : (algebraMap (𝓞 L) L (σ • s)) ≠ 0 := by
    intro h0
    apply hσs
    rw [(IsFractionRing.injective (𝓞 L) L) (h0.trans (map_zero _).symm)]
    exact 𝔓.asIdeal.zero_mem
  have hσx : σ x = algebraMap (𝓞 L) L (σ • a) * (algebraMap (𝓞 L) L (σ • s))⁻¹ := by
    rw [hxs, map_mul, map_inv₀]
    rfl
  have hmem : σ x ∈ localizationAt L 𝔓 := mem_localizationAt_iff.2 ⟨σ • a, σ • s, hσs, hσx⟩
  refine ⟨hmem, ?_⟩
  set R := localizationAt L 𝔓
  set A := algebraMap (𝓞 L) R
  have e1 : (⟨x, hx⟩ : R) * A s = A a := by
    apply Subtype.ext
    change x * algebraMap (𝓞 L) L s = algebraMap (𝓞 L) L a
    rw [hxs, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  have e2 : (⟨σ x, hmem⟩ : R) * A (σ • s) = A (σ • a) := by
    apply Subtype.ext
    change σ x * algebraMap (𝓞 L) L (σ • s) = algebraMap (𝓞 L) L (σ • a)
    rw [hσx, mul_assoc, inv_mul_cancel₀ hσs0, mul_one]
  have hres : IsLocalRing.residue R (A (σ • s)) ≠ 0 := by
    rw [Ne, residue_eq_zero_iff, algebraMap_mem_maximalIdeal_localizationAt_iff]
    exact hσs
  have r1 := congrArg (IsLocalRing.residue R) e1
  have r2 := congrArg (IsLocalRing.residue R) e2
  rw [map_mul] at r1 r2
  rw [residue_smul_of_isArithFrobAt 𝔓 hσ, residue_smul_of_isArithFrobAt 𝔓 hσ, ← r1, mul_pow] at r2
  exact mul_right_cancel₀ (by rwa [residue_smul_of_isArithFrobAt 𝔓 hσ] at hres) r2

end Residue

section DegreeOne

theorem intCast_surjective_ringOfIntegers_rat :
    Function.Surjective (Int.castRingHom (𝓞 ℚ)) := by
  intro z
  refine ⟨Rat.ringOfIntegersEquiv z, Rat.ringOfIntegersEquiv.injective ?_⟩
  simp

theorem absNorm_prime_of_ringOfIntegers_rat (𝔮 : Ideal (𝓞 ℚ)) (h0 : 𝔮 ≠ ⊥) [𝔮.IsMaximal] :
    (Ideal.absNorm 𝔮).Prime := by
  let _ : Field (𝓞 ℚ ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have hfin : Finite (𝓞 ℚ ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h0
  set p := ringChar (𝓞 ℚ ⧸ 𝔮)
  have hp : p.Prime := (CharP.char_is_prime_or_zero (𝓞 ℚ ⧸ 𝔮) p).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 ℚ ⧸ 𝔮) p)
  have : Fact p.Prime := ⟨hp⟩
  let f : ZMod p →+* 𝓞 ℚ ⧸ 𝔮 := ZMod.castHom (dvd_refl p) _
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨n, rfl⟩ := intCast_surjective_ringOfIntegers_rat z
    exact ⟨n, by simp [f]⟩
  have hbij : Function.Bijective f := ⟨f.injective, hsurj⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← Nat.card_congr (Equiv.ofBijective f hbij),
    Nat.card_zmod]
  exact hp

theorem absNorm_prime_of_mem_degreeOnePrimes {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ degreeOnePrimes ℚ K) :
    (Ideal.absNorm v.asIdeal).Prime := by
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under (𝓞 ℚ)) v.asIdeal
  have hv' : v.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := hv
  rw [hv', pow_one] at h
  rw [← h]
  have hne : v.asIdeal.under (𝓞 ℚ) ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)
  have : (v.asIdeal.under (𝓞 ℚ)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  exact absNorm_prime_of_ringOfIntegers_rat _ hne

end DegreeOne

section LatticeForm

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

include hK in

theorem exists_unit_of_homConstSet_eq (L L' : PeriodPair) (hL : latticeEnd L = cmRing σ₀)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hL' : L'.lattice = idealLattice σ₀ ↑𝔞⁻¹ * L.lattice)
    (φ : Isogeny (weierstrassCurve L) (weierstrassCurve L'))
    (hφ : (homConstSet (weierstrassCurve L) (weierstrassCurve L') : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    ∃ u : (𝓞 K)ˣ, invConst φ = σ₀ (algebraMap (𝓞 K) K u) ∧
      ∀ z : ℂ, homPt φ.toHom (toPoint L z) = toPoint L' (σ₀ (algebraMap (𝓞 K) K u) * z) := by
  classical
  set c := invConst φ with hcdef
  have hc : c ≠ 0 := invConst_ne_zero φ
  have hM : (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [← hφ, homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL']
  have hM' := eq_image_mul_inv hc hM
  have hP : (idealPeriodPair σ₀ hK 𝔞⁻¹).lattice = idealLattice σ₀ ↑𝔞⁻¹ :=
    lattice_idealPeriodPair σ₀ hK _
  have hPend : latticeEnd (idealPeriodPair σ₀ hK 𝔞⁻¹) = cmRing σ₀ := latticeEnd_idealPeriodPair σ₀ hK _
  have mult : ∀ d : ℂ, (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = (d * ·) '' idealLattice σ₀ ↑𝔞⁻¹ →
      d ∈ cmRing σ₀ := by
    intro d hd
    rw [← hPend]
    intro l hl
    rw [hP] at hl ⊢
    have h' : d * l ∈ (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) := by
      rw [hd]
      exact ⟨l, hl, rfl⟩
    exact h'
  obtain ⟨a, ha⟩ := (mem_cmRing σ₀).1 (mult c hM)
  obtain ⟨b, hb⟩ := (mem_cmRing σ₀).1 (mult c⁻¹ hM')
  have hinj : Function.Injective (σ₀.comp (algebraMap (𝓞 K) K)) :=
    σ₀.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hab : a * b = 1 := hinj (by
    simp only [RingHom.comp_apply, map_mul, map_one]
    rw [ha, hb, mul_inv_cancel₀ hc])
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm, fun z ↦ ?_⟩
  rw [← latticeToHom_homConst φ.toHom, homPt_latticeToHom]
  congr 1
  change homConst _ _ φ.toHom * z = _
  rw [homConst_toHom, ← hcdef, ← ha]

end LatticeForm

section Main

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]

omit [NumberField K] [IsTotallyComplex K] [NumberField L] in

theorem algebraMap_mem_of_liesOver {𝔭 : HeightOneSpectrum (𝓞 K)} {𝔓 : HeightOneSpectrum (𝓞 L)}
    [h : 𝔓.asIdeal.LiesOver 𝔭.asIdeal] {a : 𝓞 K} (ha : a ∈ 𝔭.asIdeal) :
    algebraMap (𝓞 K) (𝓞 L) a ∈ 𝔓.asIdeal := by
  rw [h.over] at ha
  exact ha

omit [NumberField K] [IsTotallyComplex K] [NumberField L] in

theorem isogBaseChange_eq_map {A A' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic]
    (φ : Isogeny A A') : isogBaseChange (F' := ℂ) φ = φ.map (algebraMap L ℂ) :=
  Isogeny.ext_xy
    (by rw [isogBaseChange_alt, ← ffMap_algebraMap_eq_bcEmb]; exact (Isogeny.map_x _ φ).symm)
    (by rw [isogBaseChange_y, ← ffMap_algebraMap_eq_bcEmb]; exact (Isogeny.map_y _ φ).symm)

omit [NumberField L] in
include hK in

theorem exists_isogBaseChange_eq_of_isogeny {A A' : WeierstrassCurve L} [A.IsElliptic]
    [A'.IsElliptic] (hA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K)) (φ : Isogeny A A')
    (ψ : Isogeny (A.baseChange ℂ) (A'.baseChange ℂ)) :
    ∃ φ' : Isogeny A A', isogBaseChange φ' = ψ := by
  classical
  suffices h : ∀ g : ℂ ≃ₐ[L] ℂ, ψ.conj g = ψ by
    obtain ⟨φ', hφ'⟩ := ψ.exists_map_eq_of_forall_conj_eq h
    exact ⟨φ', (isogBaseChange_eq_map φ').trans hφ'⟩
  intro g
  set D := dualOver (isogBaseChange (F' := ℂ) φ)
  obtain ⟨Λ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve (A.baseChange ℂ)
  have hΛ : latticeEnd Λ = cmRing (algebraMap K ℂ) := latticeEnd_eq_cmRing_of_ringEquiv
    (algebraMap K ℂ) hK Λ ((latticeEndEquiv Λ).trans ((vcEndEquiv C hC).symm.trans hA.some))
  have hmem : endConst (A.baseChange ℂ) (D.comp ψ).toHom ∈ cmRing (algebraMap K ℂ) := by
    rw [← hΛ, ← range_endConst hC]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := (mem_cmRing (algebraMap K ℂ)).1 hmem
  rw [endConst_apply, homConst_toHom, invConst_comp] at ha
  have hD := invConst_dualOver_mul (isogBaseChange (F' := ℂ) φ)
  rw [invConst_isogBaseChange, degree_isogBaseChange] at hD
  change invConst D * _ = _ at hD
  have hD0 : invConst D ≠ 0 := invConst_ne_zero D
  have hc0 : algebraMap L ℂ (invConst φ) ≠ 0 := by
    rw [← invConst_isogBaseChange]
    exact invConst_ne_zero _
  have hψ : invConst ψ = algebraMap L ℂ (algebraMap K L (algebraMap (𝓞 K) K a) * invConst φ /
      φ.degree) := by
    have hdeg0 : (φ.degree : ℂ) ≠ 0 := Nat.cast_ne_zero.2 φ.degree_pos.ne'
    rw [map_div₀, map_mul, map_natCast, ← IsScalarTower.algebraMap_apply, ha, ← hD]
    field_simp
  have hc : invConst (ψ.conj g) = invConst ψ := by
    rw [Isogeny.invConst_conj, hψ]
    exact g.commutes _
  have hQ : (ψ.conj g).toHom - ψ.toHom = 0 := by
    by_contra hne
    have h0 := invConst_ne_zero (isogOfHom _ hne)
    rw [← homConst_toHom, isogOfHom_toHom, map_sub, homConst_toHom, homConst_toHom, hc,
      sub_self] at h0
    exact h0 rfl
  have hQ' : (ψ.conj g).toHom = ψ.toHom := sub_eq_zero.1 hQ
  have h2 := congrArg Subtype.val hQ'
  exact Isogeny.ext' h2

include hK in

theorem exists_mem_maximalIdeal_invConst (𝔭 : HeightOneSpectrum (𝓞 K))
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hEW : Nonempty (isogEnd ((W.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny (W.baseChange L) (W'.baseChange L))
    (hφ : (homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    ∃ c ∈ maximalIdeal (localizationAt L 𝔓), algebraMap (localizationAt L 𝔓) L c = invConst φ := by
  classical
  set c := invConst φ with hcdef
  have hc0 : algebraMap L ℂ c ≠ 0 := by
    rw [hcdef, ← invConst_isogBaseChange]
    exact invConst_ne_zero _

  have step1 : ∀ β ∈ (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹,
      c * algebraMap K L β ∈ localizationAt L 𝔓 := by
    intro β hβ
    by_cases hβ0 : β = 0
    · rw [hβ0, map_zero, mul_zero]
      exact zero_mem _
    have hmem : algebraMap L ℂ c * algebraMap K ℂ β ∈
        homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) := by
      have h' : algebraMap L ℂ c * algebraMap K ℂ β ∈ (homConstSet ((W.baseChange L).baseChange ℂ)
          ((W'.baseChange L).baseChange ℂ) : Set ℂ) := by
        rw [hφ]
        exact ⟨_, map_mem_idealLattice _ hβ, rfl⟩
      exact h'
    obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hmem
    have hQ0 : Q ≠ 0 := by
      rintro rfl
      rw [map_zero] at hQ
      exact mul_ne_zero hc0 ((map_ne_zero _).2 hβ0) hQ.symm
    obtain ⟨ν, hν⟩ := exists_isogBaseChange_eq_of_isogeny hK hEW φ (isogOfHom Q hQ0)
    have e : algebraMap L ℂ (invConst ν) = algebraMap L ℂ (c * algebraMap K L β) := by
      rw [← invConst_isogBaseChange, hν, ← homConst_toHom, isogOfHom_toHom, hQ, map_mul,
        ← IsScalarTower.algebraMap_apply]
    have e' := (algebraMap L ℂ).injective e
    obtain ⟨d, hd, -⟩ := exists_invConst_reduceIsogeny L W W' ν
    rw [← e', ← hd]
    exact d.2

  have h1 : (1 : K) ∈ (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 𝔭.ne_bot)]
    exact FractionalIdeal.one_mem_one _
  have key := FractionalIdeal.mul_induction_on
    (C := fun z : K ↦ ∃ m ∈ maximalIdeal (localizationAt L 𝔓),
      algebraMap (localizationAt L 𝔓) L m = c * algebraMap K L z) h1
    (fun i hi j hj ↦ by
      obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
      refine ⟨⟨c * algebraMap K L i, step1 i hi⟩ * algebraMap (𝓞 L) (localizationAt L 𝔓)
        (algebraMap (𝓞 K) (𝓞 L) a), Ideal.mul_mem_left _ _
          ((algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 _).2
            (algebraMap_mem_of_liesOver ha)), ?_⟩
      change c * algebraMap K L i * algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L, map_mul,
        mul_assoc])
    (fun x y ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩ ↦
      ⟨m₁ + m₂, add_mem hm₁ hm₂, by rw [map_add, e₁, e₂, map_add, mul_add]⟩)
  obtain ⟨m, hm, e⟩ := key
  exact ⟨m, hm, by rw [e, map_one, mul_one]⟩

include hK in

theorem reduceIsogeny_eq_comp_frobeniusIsogeny_of_homConstSet (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (𝔓 : HeightOneSpectrum (𝓞 L))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hEW : Nonempty (isogEnd ((W.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (hEW' : Nonempty (isogEnd ((W'.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny (W.baseChange L) (W'.baseChange L))
    (hφ : (homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p] :
    p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
      (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
          (W'.map (IsLocalRing.residue _)),
        reduceIsogeny L W W' φ = ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
        ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
        ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
      IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  classical
  obtain ⟨c, hc, hcφ⟩ := exists_mem_maximalIdeal_invConst hK 𝔭 𝔓 hEW φ hφ
  have hdeg : φ.degree = Ideal.absNorm 𝔭.asIdeal := by
    have h := degree_eq_absNorm (algebraMap K ℂ) hK (E := ⟨_, hEW⟩) (E' := ⟨_, hEW'⟩) 𝔭 hv
      (isogBaseChange φ) (by rw [invConst_isogBaseChange]; exact hφ)
    rwa [degree_isogBaseChange] at h
  have hp : p = Ideal.absNorm 𝔭.asIdeal := by
    have hmem : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 L) ∈ 𝔓.asIdeal := by
      have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
      rwa [map_natCast] at this
    have h0 : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ResidueField (localizationAt L 𝔓)) = 0 := by
      have h := (algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 _).2 hmem
      rw [map_natCast] at h
      rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), residue_eq_zero_iff]
      exact h
    have hdvd := (CharP.cast_eq_zero_iff (ResidueField (localizationAt L 𝔓)) p _).1 h0
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out) hv).1 hdvd
  have hdeg' : φ.degree = p := hdeg.trans hp.symm
  obtain ⟨ψ, h1, h2, -, h4, h5⟩ := reduceIsogeny_eq_comp_frobeniusIsogeny L p φ hdeg' hc hcφ
  exact ⟨hp, hdeg', ⟨ψ, h1, h2, h4, h5⟩, residue_j_eq_pow L p φ hdeg' hc hcφ⟩

include hK in

theorem reduceIsogeny_congr_eq_comp_frobeniusIsogeny (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (𝔓 : HeightOneSpectrum (𝓞 L))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] {A A' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic]
    (hEA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K))
    (hEA' : Nonempty (isogEnd (A'.baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny A A')
    (hφ : (homConstSet (A.baseChange ℂ) (A'.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hW : W.map (algebraMap (localizationAt L 𝔓) L) = A)
    (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) = A')
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p] :
    p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
      (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
          (W'.map (IsLocalRing.residue _)),
        reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
          ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
        ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
        ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
      IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  subst hW hW'
  erw [Isogeny.congr_rfl]
  exact reduceIsogeny_eq_comp_frobeniusIsogeny_of_homConstSet hK 𝔭 hv 𝔓 hEA hEA' φ hφ p

end Main

section Global

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]

abbrev primeClass (𝔭 : HeightOneSpectrum (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩

omit [NumberField K] [IsTotallyComplex K] [NumberField L] in

theorem ELL.j_eq_algebraMap_j {A : WeierstrassCurve L} [A.IsElliptic] {x : ELL K}
    {h : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K)}
    (hx : (⟨A.baseChange ℂ, h⟩ : CMCurve K).toEll = x) : ELL.j x = algebraMap L ℂ A.j := by
  rw [← hx, ELL.j_toEll]
  exact WeierstrassCurve.map_j _ _

omit [NumberField L] in
include hK in

theorem exists_isogeny_primeClass_smul
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y)))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (x : ELL K) :
    ∃ φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)),
      (homConstSet ((E x).baseChange ℂ)
          ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) : Set ℂ) =
        (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ∧
      ((Ideal.absNorm 𝔭.asIdeal).Prime → φ.degree = Ideal.absNorm 𝔭.asIdeal) := by
  classical
  set y := (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x
  obtain ⟨h₀, hx⟩ := hE x
  obtain ⟨h₁, hy⟩ := hE y
  obtain ⟨ψ, hψ⟩ := exists_isogeny_homConstSet_eq (algebraMap K ℂ) hK
    (E := ⟨_, h₀⟩) (E' := ⟨_, h₁⟩) 𝔭 (by rw [hx, hy])
  obtain ⟨φ, hφ⟩ := exists_isogBaseChange_eq_of_isogeny hK h₀ (hiso x y).some ψ
  have hφ' : (homConstSet ((E x).baseChange ℂ) ((E y).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← invConst_isogBaseChange, hφ]
    exact hψ
  refine ⟨φ, hφ', fun hv ↦ ?_⟩
  have h := degree_eq_absNorm (algebraMap K ℂ) hK (E := ⟨_, h₀⟩) (E' := ⟨_, h₁⟩) 𝔭 hv
    (isogBaseChange φ) (by rw [invConst_isogBaseChange]; exact hφ')
  rwa [degree_isogBaseChange] at h

include hK in

theorem frobenius_at_primes_of_degree_one (hL : ∀ x : ELL K, ELL.j x ∈ L)
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y))) :
    ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧ ∀ 𝔭 ∉ S, 𝔭 ∈ degreeOnePrimes ℚ K →
      ∀ (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal],
        (∃ (W : ELL K → WeierstrassCurve (localizationAt L 𝔓)) (_ : ∀ x, (W x).IsElliptic),
          (∀ x, (W x).map (algebraMap (localizationAt L 𝔓) L) = E x) ∧
          Pairwise fun x y ↦ IsLocalRing.residue _ (W x).j ≠ IsLocalRing.residue _ (W y).j) ∧
        (∀ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal →
          galClassOf hK L hL σ = primeClass 𝔭 ∧
          ∀ x : ELL K, σ ⟨ELL.j x, hL x⟩ =
            ⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x), hL _⟩) ∧
        ∀ (x : ELL K)
          (φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))),
          (homConstSet ((E x).baseChange ℂ)
              ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) :
                Set ℂ) =
            (algebraMap L ℂ (invConst φ) * ·) ''
              idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ →
          ∀ (W W' : WeierstrassCurve (localizationAt L 𝔓)) [W.IsElliptic] [W'.IsElliptic]
            (hW : W.map (algebraMap (localizationAt L 𝔓) L) = E x)
            (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) =
              E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))
            (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p],
            p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
              (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
                  (W'.map (IsLocalRing.residue _)),
                reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
                  ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
                ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
                ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
              IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  classical
  have : Finite (ELL K) := finite_ell hK
  have hj : ∀ x, ELL.j x = algebraMap L ℂ (E x).j := fun x ↦ by
    obtain ⟨h, hx⟩ := hE x
    exact ELL.j_eq_algebraMap_j hx
  have hEj : Pairwise fun x y ↦ (E x).j ≠ (E y).j := fun x y hxy e ↦
    hxy (ELL.j_injective (by rw [hj, hj, e]))
  obtain ⟨T, hT, hTgood⟩ :=
    exists_finite_forall_liesOver (K := K) (eventually_goodReduction E hEj)
  refine ⟨T, hT, fun 𝔭 h𝔭T h𝔭1 𝔓 _ ↦ ?_⟩
  have hv := absNorm_prime_of_mem_degreeOnePrimes h𝔭1
  obtain ⟨W, hWell, hWmap, hWj, hWres⟩ := hTgood 𝔭 h𝔭T 𝔓 inferInstance
  have partB : ∀ (x : ELL K)
      (φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))),
      (homConstSet ((E x).baseChange ℂ)
          ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) : Set ℂ) =
        (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ →
      ∀ (W W' : WeierstrassCurve (localizationAt L 𝔓)) [W.IsElliptic] [W'.IsElliptic]
        (hW : W.map (algebraMap (localizationAt L 𝔓) L) = E x)
        (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) =
          E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))
        (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p],
        p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
          (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
              (W'.map (IsLocalRing.residue _)),
            reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
              ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
            ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
            ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
          IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
    intro x φ hφ W W' _ _ hW hW' q _ _
    obtain ⟨h₁, -⟩ := hE x
    obtain ⟨h₂, -⟩ := hE ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)
    exact reduceIsogeny_congr_eq_comp_frobeniusIsogeny hK 𝔭 hv 𝔓 h₁ h₂ φ hφ hW hW' q
  refine ⟨⟨W, hWell, hWmap, hWres⟩, fun σ hσ ↦ ?_, partB⟩

  set p := Ideal.absNorm 𝔭.asIdeal with hpdef
  have : Fact p.Prime := ⟨hv⟩
  have : CharP (ResidueField (localizationAt L 𝔓)) p := by
    refine charP_residueField_localizationAt 𝔓 hv ?_
    have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
    rwa [map_natCast] at this
  set x₀ : ELL K := classToEll (algebraMap K ℂ) hK 1
  set y := (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀
  set z := (ellMulAction (algebraMap K ℂ) hK).smul (galClassOf hK L hL σ) x₀
  obtain ⟨φ, hφ, -⟩ := exists_isogeny_primeClass_smul hK E hE hiso 𝔭 x₀
  obtain ⟨-, -, -, hjy⟩ := partB x₀ φ hφ (W x₀) (W y) (hWmap x₀) (hWmap y) p
  have hjmem : (E x₀).j ∈ localizationAt L 𝔓 := by
    rw [← hWj x₀]
    exact (W x₀).j.2
  obtain ⟨hσmem, hσres⟩ := residue_apply_of_isArithFrobAt 𝔓 hσ hjmem
  have hq : Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) = p := by
    rw [← Ideal.LiesOver.over (P := 𝔓.asIdeal) (p := 𝔭.asIdeal), hpdef, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
  have hσj : σ (E x₀).j = (E z).j := by
    have h := galClassOf_apply_j hK L hL σ x₀
    have e1 : (⟨ELL.j x₀, hL x₀⟩ : L) = (E x₀).j := Subtype.ext (hj x₀)
    rw [e1] at h
    apply Subtype.ext
    rw [h, hj z]
    rfl
  have key : IsLocalRing.residue _ (W z).j = IsLocalRing.residue _ (W y).j := by
    have ez : (W z).j = ⟨σ (E x₀).j, hσmem⟩ := Subtype.ext (by
      show ((W z).j : L) = σ (E x₀).j
      rw [hσj, ← hWj z]
      rfl)
    have ex : (W x₀).j = ⟨(E x₀).j, hjmem⟩ := Subtype.ext (by
      show ((W x₀).j : L) = (E x₀).j
      rw [← hWj x₀]
      rfl)
    rw [ez, hσres, hq, hjy, ex]
  have hzy : z = y := by
    by_contra hne
    exact hWres hne key
  have hcls : galClassOf hK L hL σ = primeClass 𝔭 := by
    obtain ⟨a, -, huniq⟩ := existsUnique_smul_eq (algebraMap K ℂ) hK x₀ y
    exact (huniq _ hzy).trans (huniq _ rfl).symm
  refine ⟨hcls, fun x ↦ Subtype.ext ?_⟩
  rw [galClassOf_apply_j, hcls]

end Global

end

end Elliptic
end GroundTheory.Global
end
