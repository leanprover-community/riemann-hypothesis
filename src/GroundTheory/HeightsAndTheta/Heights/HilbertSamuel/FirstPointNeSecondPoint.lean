import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FderivFderivLogRho
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace P1

abbrev Fld : Type := FractionRing (Polynomial ℤ)

instance : CharZero Fld :=
  charZero_of_injective_algebraMap (IsFractionRing.injective (Polynomial ℤ) Fld)

instance (priority := 10000) fldAlgInt : Algebra ℤ Fld := Ring.toIntAlgebra Fld

abbrev J2 : Type := Ix (Fin 2)

def p0 : J2 := ⟨(), 0⟩

def p1 : J2 := ⟨(), 1⟩


theorem firstPoint_ne_secondPoint : p0 ≠ p1 := by
  decide

theorem sum_twoPoint {M : Type*} [AddCommMonoid M] (g : J2 → M) : ∑ q, g q = g p0 + g p1 := by
  rw [Fintype.sum_sigma]
  simp [Fin.sum_univ_two, p0, p1]

def val (q : J2) : Polynomial ℤ := if q.2 = 0 then 1 else Polynomial.X

def x : J2 → Fld := fun q ↦ algebraMap (Polynomial ℤ) Fld (val q)

def dehom : MvPolynomial J2 ℤ →+* Polynomial ℤ := eval₂Hom (Int.castRingHom _) val

theorem aeval_alt (f : MvPolynomial J2 ℤ) : aeval x f = algebraMap (Polynomial ℤ) Fld (dehom f) := by
  have : (aeval x : MvPolynomial J2 ℤ →ₐ[ℤ] Fld).toRingHom =
      (algebraMap (Polynomial ℤ) Fld).comp dehom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [dehom]
    · intro q; simp [dehom, x]
  exact congrArg (fun φ : MvPolynomial J2 ℤ →+* Fld ↦ φ f) this

def homog (p : Polynomial ℤ) (d : ℕ) : MvPolynomial J2 ℤ :=
  ∑ i ∈ Finset.range (d + 1), monomial (Finsupp.single p1 i + Finsupp.single p0 (d - i)) (p.coeff i)

theorem monomial_eq (i j : ℕ) (c : ℤ) :
    monomial (Finsupp.single p1 i + Finsupp.single p0 j) c = C c * (X p1 ^ i * X p0 ^ j) := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, C_mul_monomial, one_mul, mul_one]

theorem dehom_monomial (i j : ℕ) (c : ℤ) :
    dehom (monomial (Finsupp.single p1 i + Finsupp.single p0 j) c) = Polynomial.C c * Polynomial.X ^ i := by
  rw [monomial_eq, map_mul, map_mul, map_pow, map_pow]
  simp only [dehom, coe_eval₂Hom, eval₂_C, eval₂_X, val, p0, p1]
  simp

theorem dehom_homog (p : Polynomial ℤ) {d : ℕ} (hp : p.natDegree ≤ d) : dehom (homog p d) = p := by
  rw [homog, map_sum]
  simp_rw [dehom_monomial]
  conv_rhs => rw [p.as_sum_range' (d + 1) (by omega)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial]


theorem homog_add (p q : Polynomial ℤ) (d : ℕ) : homog (p + q) d = homog p d + homog q d := by
  simp [homog, Polynomial.coeff_add, map_add, Finset.sum_add_distrib]

theorem homog_zero (d : ℕ) : homog 0 d = 0 := by simp [homog]








abbrev fs : ConeMetric ℂ J2 := fsMetric J2


theorem isSmoothHerm_fs {κ : Type} [Fintype κ] : IsSmoothHerm (HermLine.ofCone (fsMetric (Ix κ))) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FSLevi.nsq (J := Ix κ)) := by
    unfold FSLevi.nsq
    exact ContDiff.sum fun p _ ↦ ((FSLevi.reP p).contDiff.pow 2).add ((FSLevi.imaginary p).contDiff.pow 2)
  have he : (HermLine.ofCone (fsMetric (Ix κ))).h = fun z ↦ Real.sqrt (FSLevi.nsq z) := by
    funext z
    simp [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq, FSLevi.nsq, FSLevi.reP_apply,
      FSLevi.imaginaryPart_apply, FSLevi.norm_sq_eq]
  unfold IsSmoothHerm
  rw [he]
  refine hN.contDiffOn.sqrt fun z hz ↦ (FSLevi.nsq_pos ?_).ne'
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 ↦ hi (congrFun h0 _)

theorem isConjInvariantH_fs {κ : Type} [Fintype κ] :
    IsConjInvariantH (HermLine.ofCone (fsMetric (Ix κ))) := by
  intro z
  simp [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq]

theorem isSemipositiveRel_fs {κ : Type} [Fintype κ] (P₀ P : Ideal (MRing (GlobalTheory κ))) :
    IsSemipositiveRel P₀ P (HermLine.ofCone (fsMetric (Ix κ))) := by
  refine ⟨isSmoothHerm_fs, fun z hz w _ ↦ ?_⟩
  have hz0 : z ≠ 0 := by
    obtain ⟨i, hi⟩ := hz.1 ()
    exact fun h0 ↦ hi (congrFun h0 _)
  exact FSLevi.leviForm_nonneg hz0 w


end P1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
