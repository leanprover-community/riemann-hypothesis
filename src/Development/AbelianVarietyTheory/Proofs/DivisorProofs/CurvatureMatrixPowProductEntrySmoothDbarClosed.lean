import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarOperatorLocalCalculusComplexFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem smooth_coeff_closure : ∀ (n : ℕ) (v : V n), (∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v)) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v)) ∧ (∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v)) ∧ (∀ α β : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x * β x) S) v)) := by
  intro n v
  have hc : ∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v) :=
    fun γ S => contDiffAt_const
  have hs : ∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v) := by
    intro J s α h S
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    exact ContDiffAt.sum fun j hj => h j hj S
  have hg : ∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v) := by
    intro g α h1 h2 S
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact h1.mul (h2 S)
  refine ⟨hc, hs, hg, ?_⟩
  intro α β ha hb U
  have key : ∀ x, α x * β x = ∑ S, (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T) := by
    intro x
    conv_lhs => rw [← (bas n).sum_repr (α x), ← (bas n).sum_repr (β x)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [smul_mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [mul_smul_comm]
  simp only [key]
  refine hs _ Finset.univ (fun S x => (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T)) (fun S _ => ?_) U
  refine hg _ _ (ha S) ?_
  refine hs _ Finset.univ (fun T x => (bas n).repr (β x) T • (bas n S * bas n T)) (fun T _ => ?_)
  exact hg _ (fun _ => bas n S * bas n T) (hb T) (hc _)

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_coefficient_forms_closed_under_operations : ∀ (n : ℕ) (v : V n), (∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v)) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v)) ∧ (∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v)) ∧ (∀ α β : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x * β x) S) v)) := by
  atlas_forward_decl GlobalTheory.ChernCalc.smooth_coeff_closure
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.CurvSmooth

theorem curvEv_entry_smooth : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, (∀ x, (curvEv G x i j : Alt n) = ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j • (dz a * dzb b)) ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((curvEv G x i j : Alt n)) S) v) := by
  intro n r _ _ G v hG hu i j
  have e : ∀ x, (curvEv G x i j : Alt n) = ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j • (dz a * dzb b) := by
    intro x
    simp [curvEv, curvPoly, Matrix.map_apply, map_sum, sym, Algebra.smul_def]
  refine ⟨e, fun S => ?_⟩
  have hc : ∀ a b, ContDiffAt ℝ ∞ (fun x => curv G x (coordVec a) (coordVec b) i j) v := fun a b =>
    MContDiffAt.curv (j := ∞) hG hu (le_of_eq rfl) _ _ i j
  have hf : (fun x => (bas n).repr ((curvEv G x i j : Alt n)) S) =
      fun x => ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j * (bas n).repr (dz a * dzb b) S := by
    funext x
    rw [e x]
    simp [map_sum, Finsupp.finset_sum_apply]
  rw [hf]
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (hc a b).mul contDiffAt_const

end GlobalTheory.CurvSmooth
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvatureMatrixEvenForms_entries_smooth_coefficients : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, (∀ x, (curvEv G x i j : Alt n) = ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j • (dz a * dzb b)) ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((curvEv G x i j : Alt n)) S) v) := by
  atlas_forward_decl GlobalTheory.CurvSmooth.curvEv_entry_smooth
end

section
section
set_option autoImplicit false

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

noncomputable section

namespace GlobalTheory.ChernCalc.CurvClosed

theorem dbar_dbar_comm {n : ℕ} {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (v w : V n) :
    dbar (fun x => dbar u x w) z v = dbar (fun x => dbar u x v) z w := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have key (a b : V n) : dbar (fun x => dbar u x b) z a = (1 / 2 : ℂ) • (dbar (fun x => fderiv ℝ u x b) z a +
      Complex.I • dbar (fun x => fderiv ℝ u x (Complex.I • b)) z a) := by
    rw [show (fun x => dbar u x b) = fun x => (1 / 2 : ℂ) • (fderiv ℝ u x b + Complex.I • fderiv ℝ u x (Complex.I • b))
      from rfl, dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul Complex.I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul Complex.I), dbar_const_smul _ (h1 _)]
    rfl
  rw [key, key]
  simp only [dbar_apply, fderiv_fderiv_apply hu, smul_eq_mul]
  rw [hs.eq w v, hs.eq w (Complex.I • v), hs.eq (Complex.I • w) v, hs.eq (Complex.I • w) (Complex.I • v)]
  ring

theorem sum_symm {n : ℕ} {s : Fin n → Fin n → Fin n → ℂ} (hs : ∀ a c b, s a c b = s a b c) :
    ∑ c, ∑ p : Fin n × Fin n, s p.1 c p.2 • (dzb c * (-(dz p.1 * dzb p.2)) : Alt n) = 0 := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  have h := congrArg (dz a * ·) (PullClosed.sum_symm_dzb (hs a))
  simp only [Finset.mul_sum, mul_smul_comm, mul_zero] at h
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_) h
  rw [mul_neg, ← mul_assoc, ← mul_assoc, ← neg_mul, dz, dzb,
    ← eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)]

theorem curvEv_apply {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (x : V n) (i j : r) :
    (curvEv G x i j : Alt n) = ∑ p : Fin n × Fin n,
      dbar (fun y => conn G y (coordVec p.1) i j) x (coordVec p.2) • (-(dz p.1 * dzb p.2)) := by
  simp only [curvEv, curvPoly, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, ← Algebra.smul_def, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym,
    Fintype.sum_prod_type, curv, Matrix.neg_apply, mdbar_apply, neg_smul, smul_neg, NegMemClass.coe_neg]

theorem dbarAt_curvEv : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n),
    MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => (curvEv G x i j : Alt n)) v = 0 := by
  intro n r _ _ G v hG hu i j
  have hθ (a : Fin n) : ContDiffAt ℝ 2 (fun x => conn G x (coordVec a) i j) v :=
    hG.conn hu (j := 2) (WithTop.coe_le_coe.2 (le_top : (2 + 1 : ℕ∞) ≤ ⊤)) (coordVec a) i j
  rw [funext fun x => curvEv_apply G x i j,
    PullClosed.dbarAt_sum_smul (ι := Fin n × Fin n)
      (f := fun p x => dbar (fun y => conn G y (coordVec p.1) i j) x (coordVec p.2)) _
      fun p => differentiableAt_dbar_apply (hθ p.1) _]
  exact sum_symm
    (s := fun a c b => dbar (fun x => dbar (fun y => conn G y (coordVec a) i j) x (coordVec b)) v (coordVec c))
    fun a c b => dbar_dbar_comm (hθ a) _ _

end GlobalTheory.ChernCalc.CurvClosed
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_curvatureMatrixEvenForms_eq_zero : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => (curvEv G x i j : Alt n)) v = 0 := by
  atlas_forward_decl GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.PowCurv

def Good (n : ℕ) (v : V n) (f : V n → Ev n) : Prop :=
  (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((f x : Alt n)) S) v) ∧ dbarAt (fun x => (f x : Alt n)) v = 0

variable {n : ℕ} {v : V n}

theorem diff_of_smooth {α : V n → Alt n} (h : ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) (S) :
    DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v := by
  have h1 := h S
  exact h1.differentiableAt (by simp)

theorem good_const (c : Ev n) : Good n v (fun _ => c) := by
  refine ⟨fun S => (GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).1 (c : Alt n) S, ?_⟩
  exact (GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.2.2.1 (c : Alt n)

theorem good_sum {J : Type} (s : Finset J) (f : J → V n → Ev n) (h : ∀ j ∈ s, Good n v (f j)) :
    Good n v (fun x => ∑ j ∈ s, f j x) := by
  have hfun : ∀ x, ((∑ j ∈ s, f j x : Ev n) : Alt n) = ∑ j ∈ s, (f j x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).2.1 J s (fun j x => (f j x : Alt n)) (fun j hj => (h j hj).1), ?_⟩
  rw [(GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.1 J s (fun j x => (f j x : Alt n))
    (fun j hj S => diff_of_smooth (α := fun x => (f j x : Alt n)) (h j hj).1 S)]
  exact Finset.sum_eq_zero fun j hj => (h j hj).2

theorem good_mul (f g : V n → Ev n) (hf : Good n v f) (hg : Good n v g) : Good n v (fun x => f x * g x) := by
  have hfun : ∀ x, ((f x * g x : Ev n) : Alt n) = (f x : Alt n) * (g x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).2.2.2 (fun x => (f x : Alt n)) (fun x => (g x : Alt n)) hf.1 hg.1, ?_⟩
  rw [(GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.2.2.2 f (fun x => (g x : Alt n))
    (diff_of_smooth (α := fun x => (f x : Alt n)) hf.1) (diff_of_smooth (α := fun x => (g x : Alt n)) hg.1)]
  rw [hf.2, hg.2]
  simp

variable {r : Type} [Fintype r] [DecidableEq r]

theorem goodM_mul (M N : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j))
    (hN : ∀ i j, Good n v (fun x => N x i j)) (i j : r) : Good n v (fun x => (M x * N x) i j) := by
  have hfun : (fun x => (M x * N x) i j) = fun x => ∑ k ∈ Finset.univ, M x i k * N x k j := by
    funext x
    rw [Matrix.mul_apply]
  rw [hfun]
  exact good_sum Finset.univ (fun k x => M x i k * N x k j) fun k _ => good_mul _ _ (hM i k) (hN k j)

theorem goodM_pow (M : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j)) (k : ℕ) (i j : r) :
    Good n v (fun x => (M x ^ k) i j) := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero]
    exact good_const _
  | succ k ih =>
    simp only [pow_succ]
    exact goodM_mul (fun x => M x ^ k) M (fun a b => ih a b) hM i j

theorem goodM_curv (G : V n → Matrix r r ℂ) (hG : MContDiffAt ∞ G v) (hd : IsUnit (G v).det) (i j : r) :
    Good n v (fun x => curvEv G x i j) := ⟨((GlobalTheory.T.curvatureMatrixEvenForms_entries_smooth_coefficients n r G v hG hd) i j).2, GlobalTheory.T.dbar_curvatureMatrixEvenForms_eq_zero n r G v hG hd i j⟩

end GlobalTheory.PowCurv

open GlobalTheory.PowCurv in

theorem GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ (k l : ℕ) (i j : r), (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) S) v) ∧ dbarAt (fun x => ((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) v = 0 := by
  intro n r _ _ G G' v hG hd hG' hd' k l i j
  exact goodM_mul (fun x => curvEv G x ^ k) (fun x => curvEv G' x ^ l)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G hG hd c d) k a b)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G' hG' hd' c d) l a b) i j
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ (k l : ℕ) (i j : r), (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) S) v) ∧ dbarAt (fun x => ((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) v = 0 := by
  atlas_forward_decl GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar
end
