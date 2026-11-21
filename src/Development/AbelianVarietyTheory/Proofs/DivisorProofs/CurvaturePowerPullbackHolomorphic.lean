import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem pull_aeval_sym : ∀ (n n' : ℕ) (L : V n' →L[ℂ] V n) (P : MvPolynomial (Fin n × Fin n) ℂ), pull L ((aeval sym P : Ev n) : Alt n) = ((aeval sym (aeval (fun x : Fin n × Fin n => ∑ c, ∑ d, C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) * (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ)) P) : Ev n') : Alt n') := by
  intro n n' L P
  rw [MvPolynomial.comp_aeval_apply]
  have key : (pull L).comp ((Subalgebra.center ℂ (Alt n)).val.comp (aeval sym)) = (Subalgebra.center ℂ (Alt n')).val.comp
      (aeval fun x : Fin n × Fin n => aeval sym (∑ c, ∑ d,
        C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) * (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ))) := by
    refine MvPolynomial.algHom_ext fun x => ?_
    simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, Subalgebra.coe_val, sym, (pull_dz L _).1,
      (pull_dz L _).2, Finset.sum_mul_sum, AlgHom.commutes, smul_mul_smul_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Algebra.smul_def, map_mul]
  exact congrArg (fun f => f P) key

end GlobalTheory.ChernCalc
end

section
noncomputable section

open Matrix MvPolynomial ComplexConjugate
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory.CurvatureSesquilinearExpansion

theorem eq_sum_coordVec {n : ℕ} (v : V n) : v = ∑ a, v.ofLp a • coordVec a := by
  ext j
  simp [Pi.single_apply]

theorem sesq_expand {n : ℕ} (F : V n → V n → ℂ)
    (h1 : ∀ x y z, F (x + y) z = F x z + F y z) (h2 : ∀ (c : ℂ) x z, F (c • x) z = c * F x z)
    (h3 : ∀ x y z, F x (y + z) = F x y + F x z)
    (h4 : ∀ (c : ℂ) x z, F x (c • z) = conj c * F x z) (ξ η : V n) :
    F ξ η = ∑ a, ∑ b, ξ.ofLp a * conj (η.ofLp b) * F (coordVec a) (coordVec b) := by
  have s1 (z : V n) (f : Fin n → V n) : F (∑ a, f a) z = ∑ a, F (f a) z :=
    map_sum (AddMonoidHom.mk' (fun x => F x z) fun x y => h1 x y z) f Finset.univ
  have s2 (x : V n) (f : Fin n → V n) : F x (∑ a, f a) = ∑ a, F x (f a) :=
    map_sum (AddMonoidHom.mk' (fun z => F x z) fun y z => h3 x y z) f Finset.univ
  conv_lhs => rw [eq_sum_coordVec ξ, eq_sum_coordVec η, s1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [s2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h2, h4, mul_assoc]

theorem curv_expand {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {z : V n}
    (h : MContDiffAt 2 G z) (hu : IsUnit (G z).det) (ξ η : V n) (i j : r) :
    curv G z ξ η i j =
      ∑ a, ∑ b, ξ.ofLp a * conj (η.ofLp b) * curv G z (coordVec a) (coordVec b) i j := by
  have m1 (x y w : V n) : mddbar G z (x + y) w = mddbar G z x w + mddbar G z y w := by
    ext a b; simp
  have m2 (c : ℂ) (x w : V n) : mddbar G z (c • x) w = c • mddbar G z x w := by
    ext a b; simp
  have m3 (x y w : V n) : mddbar G z x (y + w) = mddbar G z x y + mddbar G z x w := by
    ext a b; simp
  have m4 (c : ℂ) (x w : V n) : mddbar G z x (c • w) = conj c • mddbar G z x w := by
    ext a b; simp
  refine sesq_expand (fun ξ η => curv G z ξ η i j) ?_ ?_ ?_ ?_ ξ η
  · intro x y w
    simp only [curv_eq h hu, mdel_add_vec, m1, transpose_add, Matrix.mul_add, Matrix.sub_apply,
      Matrix.add_apply]
    ring
  · intro c x w
    simp only [curv_eq h hu, mdel_smul_vec, m2, transpose_smul, Matrix.mul_smul, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  · intro x y w
    simp only [curv_eq h hu, mdbar_add_vec, m3, transpose_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.sub_apply, Matrix.add_apply]
    ring
  · intro c x w
    simp only [curv_eq h hu, mdbar_smul_vec, m4, transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem curvPoly_pullback : (let d1 : {n n' : ℕ} → (ReciprocityTheory.L2DbarEstimates.V n' →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) → MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ := @(fun {n n' : ℕ} (L : ReciprocityTheory.L2DbarEstimates.V n' →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) ↦ MvPolynomial.aeval fun (x : Fin n × Fin n) ↦ ∑ c : Fin n', ∑ d : Fin n', (MvPolynomial.C : (fun (x : Fin n) ↦ ℂ) (Prod.fst x) → MvPolynomial (Fin n' × Fin n') ((fun (x : Fin n) ↦ ℂ) (Prod.fst x))) (WithLp.ofLp ((L : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n) (GlobalTheory.GoodMetric.coordVec c)) (Prod.fst x) * (starRingEnd ℂ : ℂ → ℂ) (WithLp.ofLp ((L : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n) (GlobalTheory.GoodMetric.coordVec d)) (Prod.snd x))) * MvPolynomial.X (c, d)); ∀ {n n' : ℕ} {r : Type} [inst : Fintype r] [inst_1 : DecidableEq r] {G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {φ : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n} {w : ReciprocityTheory.L2DbarEstimates.V n'}, ContDiffAt ℂ (2 : WithTop ℕ∞) φ w → GlobalTheory.HermFrame.MContDiffAt ((⊤ : ℕ∞) : WithTop ℕ∞) G (φ w) → IsUnit (Matrix.det (G (φ w))) → GlobalTheory.GoodMetric.curvPoly (fun (x : ReciprocityTheory.L2DbarEstimates.V n') ↦ G (φ x)) w = (AlgHom.mapMatrix (d1 (fderiv ℂ φ w)) : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ) → Matrix r r (MvPolynomial (Fin n' × Fin n') ℂ)) (GlobalTheory.GoodMetric.curvPoly G (φ w))) := by
  intro d1 n n' r _ _ G φ w hφ hG hu
  have h2 : MContDiffAt 2 G (φ w) := hG.of_le (by norm_cast)
  refine Matrix.ext fun i j => ?_
  simp only [d1, curvPoly, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    aeval_X, aeval_C, algebraMap_eq, curv_comp_holo h2 hu hφ, Finset.mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [curv_expand h2 hu (fderiv ℂ φ w (coordVec c))]
  simp only [map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.CurvatureSesquilinearExpansion
end
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc.HoloPull

noncomputable def subst {n n' : ℕ} (L : V n' →L[ℂ] V n) :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ :=
  aeval fun x : Fin n × Fin n => ∑ c, ∑ d, C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) *
    (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ)

theorem sesq_expand {n : ℕ} {r : Type} {F : V n → V n → Matrix r r ℂ} (h : IsSesq F) (ξ η : V n) (i j : r) :
    F ξ η i j = ∑ a, ∑ b, ξ a * (starRingEnd ℂ) (η b) * F (coordVec a) (coordVec b) i j := by
  have e (v : V n) : v = ∑ a, v a • coordVec a := by
    ext b; simp [Pi.single_apply]
  have h1 (s : Finset (Fin n)) (c : Fin n → ℂ) (y : V n) :
      F (∑ a ∈ s, c a • coordVec a) y = ∑ a ∈ s, c a • F (coordVec a) y := by
    induction s using Finset.induction_on with
    | empty => simpa using h.smul_left 0 0 y
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_left, h.smul_left, ih]
  have h2 (s : Finset (Fin n)) (c : Fin n → ℂ) (x : V n) :
      F x (∑ a ∈ s, c a • coordVec a) = ∑ a ∈ s, (starRingEnd ℂ) (c a) • F x (coordVec a) := by
    induction s using Finset.induction_on with
    | empty => simpa using h.smul_right 0 x 0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, h.smul_right, ih]
  conv_lhs => rw [e ξ, e η, h1]
  simp only [h2, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

variable {n n' : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n' → V n} {w : V n'}

theorem curvPoly_comp (hφ : ContDiffAt ℂ 2 φ w) (hG : MContDiffAt ∞ G (φ w)) (hu : IsUnit (G (φ w)).det) :
    curvPoly (fun x => G (φ x)) w = (subst (fderiv ℂ φ w)).mapMatrix (curvPoly G (φ w)) := by
  first
  | exact @_root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback
  | exact _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback
  | (apply _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> assumption)
  | (intros; apply _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback ..)

theorem curvEv_eq (G : V n → Matrix r r ℂ) (v : V n) :
    curvEv G v = (aeval sym : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n).mapMatrix (curvPoly G v) := rfl

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix r r R) :
    Matrix.charpolyRev (M.map f) = (Matrix.charpolyRev M).map f := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext1 i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

end GlobalTheory.ChernCalc.HoloPull

namespace GlobalTheory.ChernCalc

open HoloPull in

theorem curv_pow_chern_comp_holo : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → (∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') = pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n)) ∧ ∀ k, (powAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (powAt G (φ w) k) ∧ (chernAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (chernAt G (φ w) k) := by
  intro n n' r _ _ G φ w hφ hG hu
  have key : ∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det →
      ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') =
        pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n) := by
    intro k l i j G' hG' hu'
    simp only [curvEv_eq, curvPoly_comp hφ hG hu, curvPoly_comp hφ hG' hu', ← map_pow, ← map_mul]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply]
    exact (pull_aeval_sym _ _ _ _).symm
  refine ⟨key, fun k => ⟨?_, ?_⟩⟩
  · have := fun i => key k 0 i i G hG hu
    simp only [pow_zero, mul_one] at this
    simp only [powAt, Matrix.trace, Matrix.diag_apply, AddSubmonoidClass.coe_finsetSum, map_sum, this]
  · have e : chernPoly (fun x => G (φ x)) w k = subst (fderiv ℂ φ w) (chernPoly G (φ w) k) := by
      rw [chernPoly, chernPoly, curvPoly_comp hφ hG hu, ← map_neg]
      exact (congrArg (fun p => Polynomial.coeff p k)
        (charpolyRev_map (subst (fderiv ℂ φ w)).toRingHom _)).trans (Polynomial.coeff_map _ _)
    rw [chernAt, chernAt, e, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, pull_aeval_sym]
    rfl

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_power_pullback_holomorphic : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → (∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') = pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n)) ∧ ∀ k, (powAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (powAt G (φ w) k) ∧ (chernAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (chernAt G (φ w) k) := by
  atlas_forward_decl GlobalTheory.ChernCalc.curv_pow_chern_comp_holo
end
