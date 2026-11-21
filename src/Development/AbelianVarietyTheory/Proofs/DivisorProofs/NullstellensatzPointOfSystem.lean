import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralConeRingOfForallValuationSubring
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioMemValuationSubringAtGenericPoint

section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring | exact GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring | (intros; apply GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring <;> assumption)
end

section
section
open MvPolynomial

namespace GlobalTheory

theorem coeff_eval₂_C_mul_X {F K : Type} [Field F] [Field K] (φ : F →+* K) {r : ℕ} (w : Fin r → K)
    (p : MvPolynomial (Fin r) F) (d : ℕ) :
    (MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) p).coeff d
      = MvPolynomial.eval₂ φ w (homogeneousComponent d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hprod : (u.prod fun i k => (Polynomial.C (w i) * Polynomial.X : Polynomial K) ^ k)
        = Polynomial.C (u.prod fun i k => w i ^ k) * Polynomial.X ^ (Finsupp.degree u) := by
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
        Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
    have hcomp : homogeneousComponent d (monomial u a)
        = if Finsupp.degree u = d then monomial u a else 0 := by
      ext v
      rw [coeff_homogeneousComponent]
      by_cases hd : Finsupp.degree u = d
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
    rw [eval₂_monomial, hprod, hcomp, ← mul_assoc, RingHom.comp_apply, ← map_mul,
      Polynomial.coeff_C_mul_X_pow]
    by_cases h : Finsupp.degree u = d
    · subst h
      simp [eval₂_monomial]
    · have h' : d ≠ Finsupp.degree u := fun e => h e.symm
      simp [h, h']
  | add p q hp hq =>
    simp only [eval₂_add, Polynomial.coeff_add, map_add, hp, hq]

theorem homogeneous_components_of_integral_equation (F K : Type) [Field F] [Field K] (φ : F →+* K)
    (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F)
    (h : (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0) :
    ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧
      τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  refine ⟨fun k => homogeneousComponent (e * (m - k)) (b k),
    fun k => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hc := congrArg (fun P : Polynomial K => P.coeff (e * m)) h
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
  have hpow : ∀ n : ℕ, (Polynomial.C τ * Polynomial.X ^ e) ^ n
      = Polynomial.C (τ ^ n) * Polynomial.X ^ (e * n) := by
    intro n
    rw [mul_pow, ← pow_mul, map_pow]
  have hterm : ∀ k : Fin m, (MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ)).coeff (e * m)
      = MvPolynomial.eval₂ φ w (homogeneousComponent (e * (m - k)) (b k)) * τ ^ (k : ℕ) := by
    intro k
    have hle : e * (k : ℕ) ≤ e * m := Nat.mul_le_mul_left e k.is_lt.le
    rw [hpow, ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hle, Polynomial.coeff_mul_C,
      ← Nat.mul_sub, coeff_eval₂_C_mul_X]
  rw [hpow, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
  simpa only [hterm] using hc

end GlobalTheory
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_components_of_cone_integral_equation : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 → ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  atlas_forward_decl GlobalTheory.homogeneous_components_of_integral_equation
end

section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratio_mem_valuationSubring_at_generic_point : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∀ η : S.Y, IsGenericPoint η Set.univ → ∀ V : ValuationSubring (S.Y.residueField η), (∀ c, S.baseHom (resPt η) c ∈ V) → ∃ i, S.val (resPt η) (S.comb (u i)) ≠ 0 ∧ S.powVal (resPt η) th / S.val (resPt η) (S.comb (u i)) ^ e ∈ V := by
  first | exact @GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring | exact GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring | (intros; apply GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring <;> assumption)
end

section
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry TopologicalSpace CategoryTheory GlobalTheory.Points GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory.Adelic.GenericRel

theorem eval₂_mul_of_isHomogeneous {σ R A : Type} [CommSemiring R] [CommSemiring A] (φ : R →+* A)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (c : A) (v : σ → A) :
    eval₂ φ (fun i => c * v i) p = c ^ d * eval₂ φ v p := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

variable {F : Type} [Field F] (S : LinSys F)

noncomputable def relFn (c : S.L.ι) {r e : ℕ} (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ)
    (a : Fin m → MvPolynomial (Fin r) F) : Γ(S.Y, S.L.U c) :=
  zfun th c ^ m + ∑ k, eval₂ ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤)))
    (fun i => (S.comb (u i)).f c) (a k) * zfun th c ^ (k : ℕ)

theorem valR_relFn {K : Type} [Field K] (x : Sp K ⟶ S.Y) (c : S.L.ι) (hx : ptOf x ∈ S.L.U c) {r e : ℕ}
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) :
    valR x (S.L.U c) (relFn S c u th m a) = valR x (S.L.U c) (zfun th c) ^ m + ∑ k, eval₂ (S.baseHom x)
      (fun i => valR x (S.L.U c) ((S.comb (u i)).f c)) (a k) * valR x (S.L.U c) (zfun th c) ^ (k : ℕ) := by
  have h := (le_iff_ptOf_mem x _).2 hx
  have hc : (valMap x _ h).hom.comp ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤))) = S.baseHom x := by
    ext b
    exact ((valR_eq x _ h _).symm.trans (valR_res x le_top h _)).trans (S.valR_algebraMap x b)
  simp only [relFn, valR_eq x _ h, map_add, map_sum, map_mul, map_pow, eval₂_comp_left, hc]
  rfl

theorem relation_of_generic (F : Type) [Field F] (S : LinSys F) (hY : AlgebraicGeometry.IsIntegral S.Y)
    (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y) (hη : IsGenericPoint η Set.univ)
    (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) (ha : ∀ k, (a k).IsHomogeneous (e * (m - k)))
    (h0 : S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
      (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0)
    (K : Type) [Field K] [Algebra F K] (x : S.Pt K) :
    S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) *
      S.powVal x.1 th ^ (k : ℕ) = 0 := by
  have hxU : ptOf x.1 ∈ S.L.U (S.chartAt (ptOf x.1)) := S.mem_chartAt _
  have hηU : ptOf (resPt η) ∈ S.L.U (S.chartAt (ptOf x.1)) := by
    rw [ptOf_resPt]
    exact (hη.mem_open_set_iff (S.L.U _).isOpen).2 ⟨_, trivial, hxU⟩
  obtain ⟨c0, hc0, hv, hp⟩ := S.exists_frame_change (resPt η) _ hηU
  have hzero : valR (resPt η) _ (relFn S (S.chartAt (ptOf x.1)) u th m a) = 0 := by
    rw [valR_relFn S _ _ hηU, hp (e : ℤ) th]
    simp only [hv, zpow_natCast, eval₂_mul_of_isHomogeneous _ (ha _)]
    calc _ = c0 ^ (e * m) * (S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
          (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ)) := by
          rw [mul_add, Finset.mul_sum, mul_pow, ← pow_mul]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_pow, ← pow_mul, show e * m = e * (m - k) + e * k by
            rw [← mul_add, Nat.sub_add_cancel k.2.le], pow_add]
          ring
      _ = 0 := by rw [h0, mul_zero]
  have hb : S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hm : η ∈ S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) :=
      (hη.mem_open_set_iff (S.Y.basicOpen _).isOpen).2 ⟨y, trivial, hy⟩
    rw [← ptOf_resPt η] at hm
    exact ((valR_ne_zero_iff (resPt η) hηU _).2 hm hzero).elim
  have hf : relFn S (S.chartAt (ptOf x.1)) u th m a = 0 := by
    haveI := hY
    exact (basicOpen_eq_bot_iff _).1 hb
  have key := valR_relFn S x.1 _ hxU u th m a
  rw [hf, valR_zero x.1 _ ((le_iff_ptOf_mem _ _).2 hxU)] at key
  have e2 : ∀ i, valR x.1 _ ((S.comb (u i)).f (S.chartAt (ptOf x.1))) =
      ∑ j, algebraMap F K (u i j) * S.coords x.1 j := fun i =>
    (S.val_comb x.1 (u i)).trans (by rw [LinSys.baseHom_ptOver])
  simp only [e2, LinSys.baseHom_ptOver] at key
  simp only [aeval_def]
  exact key.symm

end GlobalTheory.Adelic.GenericRel
end

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSystem_relation_of_generic_point : ∀ (F : Type) [Field F] (S : LinSys F), AlgebraicGeometry.IsIntegral S.Y → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y), IsGenericPoint η Set.univ → ∀ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) → S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η)) (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0 → ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  atlas_forward_decl GlobalTheory.Adelic.GenericRel.relation_of_generic
end

section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SecIntegral

theorem exists_integral_relation : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∃ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  intro F _ S hS r e u th hcov
  have hI : AlgebraicGeometry.IsIntegral S.Y := hS.isIntegral
  have hη : IsGenericPoint (genericPoint S.Y) Set.univ := by
    simpa using genericPoint_spec S.Y
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring F (S.Y.residueField (genericPoint S.Y)) (S.baseHom (resPt (genericPoint S.Y))) r e
    (fun i => S.val (resPt (genericPoint S.Y)) (S.comb (u i))) (S.powVal (resPt (genericPoint S.Y)) th)
    (GlobalTheory.T.exists_ratio_mem_valuationSubring_at_generic_point F S hS r e u th hcov _ hη)
  obtain ⟨a, ha, h0⟩ := GlobalTheory.T.homogeneous_components_of_cone_integral_equation _ _ _ r e m _ _ b hb
  exact ⟨m, a, ha, GlobalTheory.T.linearSystem_relation_of_generic_point F S hI r e u th _ hη m a ha h0⟩

end GlobalTheory.SecIntegral
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry CategoryTheory

open GlobalTheory.CompHt

namespace GlobalTheory.ConeOnto

theorem exists_rat_pt {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Sp K) [LocallyOfFiniteType f]
    {Z : Set X} (hZ : IsLocallyClosed Z) {x : X} (hx : x ∈ Z) :
    ∃ a : Sp K ⟶ X, a ≫ f = 𝟙 _ ∧ ∀ w, a w ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hZ
  replace hc : IsClosed {c} := hc
  exact ⟨pointOfClosedPoint f c hc, pointOfClosedPoint_comp _ _ _, fun w => by rw [pointOfClosedPoint_apply]; exact hcZ⟩


end GlobalTheory.ConeOnto
end
end
