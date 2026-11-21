import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDegreePolynomialMapEqCharpolyRatioStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDimStatement

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.charPolyRat : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f) : ℚ) := by
  intro K _ A f
  obtain ⟨F, hF, hev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl 2 ![𝟙 A, f]
  set N := 2 * A.dim with hN
  have hsupp : ∀ d ∈ F.support, d 0 + d 1 = N := by
    intro d hd
    by_contra h
    refine (MvPolynomial.mem_support_iff.mp hd) (hF.coeff_eq_zero ?_)
    rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  let P : Polynomial ℚ := ∑ d ∈ F.support,
    Polynomial.C (MvPolynomial.coeff d F * (-1) ^ d 1) * Polynomial.X ^ d 0
  have hPeval : ∀ q : ℚ, P.eval q = MvPolynomial.eval ![q, -1] F := by
    intro q
    rw [MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [Fin.prod_univ_two]
    ring
  have hcoef : P.coeff N = MvPolynomial.coeff (Finsupp.single 0 N) F := by
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp
    · intro d hd hne
      rw [if_neg]
      intro h0
      apply hne
      have := hsupp d hd
      ext i
      fin_cases i <;> simp <;> omega
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hdeg : P.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro d hd
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := hsupp d hd; omega)
  have h10 : MvPolynomial.eval ![1, 0] F = MvPolynomial.coeff (Finsupp.single 0 N) F := by
    rw [MvPolynomial.eval_eq', Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp [Fin.prod_univ_two]
    · intro d hd hne
      have := hsupp d hd
      have h1 : d 1 ≠ 0 := by
        intro h1
        apply hne
        ext i
        fin_cases i <;> simp <;> omega
      simp [Fin.prod_univ_two, h1]
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hone : MvPolynomial.eval ![1, 0] F = 1 := by
    have h := hev ![1, 0]
    have e1 : (fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![1, 0] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    have h2 := (GlobalTheory.MulIsogeny.mul_isogeny K A 1 one_ne_zero).2
    simp only [one_smul, Int.natAbs_one, one_pow] at h2
    simp [Fin.sum_univ_two, h2]
  have hnat : P.natDegree = N := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg
    rw [hcoef, ← h10, hone]
    exact one_ne_zero
  refine ⟨P, ?_, hnat, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hnat, hcoef, ← h10, hone]
  · intro n
    rw [hPeval]
    have h := hev ![n, -1]
    have e1 : (fun i => (((![n, -1] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![(n : ℚ), -1] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    congr 2
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, neg_smul, one_smul]
    rw [sub_eq_add_neg]
    congr 1
    exact zsmul_one (R := End A) n
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_rat_charPoly_abelianVariety : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f) : ℚ) := by
  first | (exact @GlobalTheory.charPolyRat) | (exact GlobalTheory.charPolyRat) | (intros; apply GlobalTheory.charPolyRat  <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
open Polynomial

namespace GlobalTheory.AV.AbVar

theorem int_of_charpoly_rat_of_monic_annihilator : ∀ (k V : Type) [Field k] [Algebra ℚ k] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (P : Polynomial ℚ) (Q : Polynomial ℤ), Q.Monic → Polynomial.aeval φ Q = 0 → P.map (algebraMap ℚ k) = φ.charpoly → ∃ P₀ : Polynomial ℤ, P₀.map (algebraMap ℤ ℚ) = P := by
  intro k V _ _ _ _ _ φ P Q hQ hφ hP
  have hinj : Function.Injective (algebraMap ℚ k) := (algebraMap ℚ k).injective
  have hPm : P.Monic := Polynomial.monic_of_injective hinj (by rw [hP]; exact LinearMap.charpoly_monic φ)
  set Qq : ℚ[X] := Q.map (algebraMap ℤ ℚ) with hQq
  have hmap : Qq.map (algebraMap ℚ k) = Q.map (algebraMap ℤ k) := by
    rw [hQq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hG : aeval φ (Q.map (algebraMap ℤ k)) = 0 := by
    rw [aeval_map_algebraMap]; exact hφ
  have hd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank φ _ hG
  rw [← hP, ← hmap, ← Polynomial.map_pow, Polynomial.map_dvd_map' (algebraMap ℚ k)] at hd
  have hd' : P ∣ (Q ^ Module.finrank k V).map (algebraMap ℤ ℚ) := by
    rw [Polynomial.map_pow]; exact hd
  obtain ⟨P₀, hP₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ (hQ.pow _) hd'
  refine ⟨P₀, ?_⟩
  rw [hPm.leadingCoeff, Polynomial.C_1, _root_.mul_one] at hP₀
  exact hP₀

end GlobalTheory.AV.AbVar
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_charpoly_of_monic_integral_annihilator : ∀ (k V : Type) [Field k] [Algebra ℚ k] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (P : Polynomial ℚ) (Q : Polynomial ℤ), Q.Monic → Polynomial.aeval φ Q = 0 → P.map (algebraMap ℚ k) = φ.charpoly → ∃ P₀ : Polynomial ℤ, P₀.map (algebraMap ℤ ℚ) = P := by
  atlas_forward_decl GlobalTheory.AV.AbVar.int_of_charpoly_rat_of_monic_annihilator
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_prime_natCast_ne_zero_of_field (K : Type) [Field K] : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
  by_cases h2 : (2 : K) = 0
  · refine ⟨3, Nat.prime_three, ?_⟩
    intro h3
    have : (1 : K) = 0 := by
      have e : (1 : K) = (3 : ℕ) - (2 : K) := by push_cast; ring
      rw [e, h3, h2, sub_zero]
    exact one_ne_zero this
  · exact ⟨2, Nat.prime_two, by exact_mod_cast h2⟩

noncomputable def vendRing {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (A : AbVar K) : End A →+* Module.End ℚ_[l] (Vl l A) :=
  (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp (tend l A)

theorem vendRing_apply {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (A : AbVar K) (f : End A) : vendRing l A f = vmap l f := rfl

theorem exists_isCharpoly {K : Type} [Field K] (A : AbVar K) (f : End A) : ∃ P, IsCharpoly f P := by
  obtain ⟨P, hPm, hPd, hPe⟩ := GlobalTheory.T.exists_monic_rat_charPoly_abelianVariety K A f
  obtain ⟨l, hl, hlK⟩ := exists_prime_natCast_ne_zero_of_field K
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : Module.Finite ℚ_[l] (Vl l A) := (tl_free_finrank K l hlK A).2.2.2.1
  have hcp := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate K l hlK A f P hPm hPd hPe
  haveI : Module.Finite ℤ (End A) := (GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim K A A).1
  obtain ⟨Q, hQm, hQ⟩ := (Algebra.IsIntegral.isIntegral f : IsIntegral ℤ f)
  have hQV : Polynomial.aeval (vmap l (A := A) (B := A) f) Q = 0 := by
    have h := congrArg (vendRing l A) hQ
    rw [Polynomial.hom_eval₂, map_zero,
      Subsingleton.elim ((vendRing l A).comp (algebraMap ℤ (End A))) (algebraMap ℤ _)] at h
    rw [Polynomial.aeval_def, ← vendRing_apply]
    exact h
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.integral_charpoly_of_monic_integral_annihilator ℚ_[l] (Vl l A) (vmap l (A := A) (B := A) f) P Q hQm hQV hcp
  have hinj : Function.Injective (algebraMap ℤ ℚ) := (algebraMap ℤ ℚ).injective_int
  refine ⟨P₀, ?_, ?_, ?_⟩
  · have h := hPm
    rw [← hP₀] at h
    rw [Polynomial.Monic, Polynomial.leadingCoeff_map_of_injective hinj] at h
    exact hinj (by simpa using h)
  · rw [← Polynomial.natDegree_map_eq_of_injective hinj, hP₀, hPd]
  · intro n
    have h := hPe n
    rw [← hP₀, Polynomial.eval_map, show (n : ℚ) = algebraMap ℤ ℚ n by simp,
      Polynomial.eval₂_hom] at h
    rw [eq_intCast] at h
    exact_mod_cast h

theorem isCharpoly_charpoly_unique (K : Type) [Field K] (A : AbVar K) (f : End A) :
    IsCharpoly f (charpoly f) ∧ ∀ P, IsCharpoly f P → P = charpoly f := by
  have hex := exists_isCharpoly A f
  have hc : IsCharpoly f (charpoly f) := by
    classical
    rw [charpoly, dif_pos hex]
    exact hex.choose_spec
  refine ⟨hc, fun P hP => Polynomial.funext fun n => ?_⟩
  rw [hP.2.2 n, hc.2.2 n]

theorem charpoly_spec : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A),
    IsCharpoly f (charpoly f) ∧ ∀ P, IsCharpoly f P → P = charpoly f :=
  fun K _ A f => isCharpoly_charpoly_unique K A f

end GlobalTheory.AV.AbVar
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietyEndCharpoly_spec : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), IsCharpoly f (charpoly f) ∧ ∀ P, IsCharpoly f P → P = charpoly f := by
  first | (exact @GlobalTheory.AV.AbVar.charpoly_spec) | (exact GlobalTheory.AV.AbVar.charpoly_spec) | (intros; apply GlobalTheory.AV.AbVar.charpoly_spec  <;> assumption)
end
