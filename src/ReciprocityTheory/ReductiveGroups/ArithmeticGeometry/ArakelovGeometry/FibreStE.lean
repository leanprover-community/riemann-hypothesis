import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def deh {ι S : Type*} [Field S] (v : ι → S) (i₀ : ι) : MvPolynomial ι ℤ →+* S :=
  eval₂Hom (Int.castRingHom S) fun i => v i / v i₀

def homog {ι : Type*} [DecidableEq ι] (i₀ : ι) (N : ℕ) (G : MvPolynomial ι ℤ) :
    MvPolynomial ι ℤ :=
  ∑ m ∈ G.support, monomial (m + Finsupp.single i₀ (N - m.degree)) (G.coeff m)

theorem homog_isHomogeneous {ι : Type*} [DecidableEq ι] (i₀ : ι) {N : ℕ} (G : MvPolynomial ι ℤ)
    (hN : G.totalDegree ≤ N) : (homog i₀ N G).IsHomogeneous N := by
  apply IsHomogeneous.sum
  intro m hm
  apply isHomogeneous_monomial
  have : m.degree ≤ N := le_trans (le_totalDegree hm) hN
  have h := Finsupp.degree_single (R := ℕ) i₀ (N - m.degree)
  simp only [map_add, h]
  omega

theorem eval₂_homog {ι S : Type*} [Fintype ι] [DecidableEq ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {N : ℕ} (G : MvPolynomial ι ℤ) (hN : G.totalDegree ≤ N) :
    eval₂ (Int.castRingHom S) v (homog i₀ N G) = v i₀ ^ N * deh v i₀ G := by
  rw [homog, eval₂_sum, deh, coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m.degree ≤ N := le_trans (le_totalDegree hm) hN
  rw [eval₂_monomial, Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
    Finsupp.prod_single_index (by simp)]
  have h1 : (m.prod fun i k => v i ^ k) = ∏ i, v i ^ m i :=
    Finsupp.prod_fintype _ _ (by simp)
  have h2 : ∏ i, (v i / v i₀) ^ m i = (∏ i, v i ^ m i) / v i₀ ^ m.degree := by
    rw [Finset.prod_congr rfl fun i _ => div_pow (v i) (v i₀) (m i), Finset.prod_div_distrib,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
  rw [h1, h2]
  have h3 : v i₀ ^ N = v i₀ ^ (N - m.degree) * v i₀ ^ m.degree := by
    rw [← pow_add]; congr 1; omega
  rw [h3]
  field_simp

theorem aeval_smul_of_isHomogeneous {ι S : Type*} [Fintype ι] [CommRing S]
    {f : MvPolynomial ι ℤ} {d : ℕ} (hf : f.IsHomogeneous d) (c : S) (v : ι → S) :
    aeval (fun i => c * v i) f = c ^ d * aeval v f := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hf (mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem aeval_eq_pow_mul_deh {ι S : Type*} [Fintype ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {n : ℕ} {f : MvPolynomial ι ℤ} (hf : f.IsHomogeneous n) :
    aeval v f = v i₀ ^ n * deh v i₀ f := by
  have h : v = fun i => v i₀ * (v i / v i₀) := by
    funext i; rw [mul_div_cancel₀ _ hv]
  conv_lhs => rw [h]
  rw [aeval_smul_of_isHomogeneous hf]
  rfl

theorem deh_X {ι S : Type*} [Field S] (v : ι → S) (i₀ i : ι) : deh v i₀ (X i) = v i / v i₀ := by
  simp [deh]



theorem deh_eq_zero_of_deh_eq_zero {ι : Type*} [Fintype ι] {Ω : Type*} [Field Ω]
    (x : ι → Ω) (z : ι → ℂ) (i₀ : ι) (hx : x i₀ ≠ 0) (hz : z i₀ ≠ 0)
    (hP : ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0)
    {G : MvPolynomial ι ℤ} (hG : deh x i₀ G = 0) : deh z i₀ G = 0 := by
  classical
  have hH := homog_isHomogeneous i₀ G le_rfl
  have h1 : aeval x (homog i₀ G.totalDegree G) = 0 := by
    rw [aeval_def, algebraMap_int_eq, eval₂_homog x i₀ hx G le_rfl, hG, mul_zero]
  have h2 := hP _ (mem_coordIdeal_of_isHomogeneous ℤ x hH h1)
  rw [eval_map, eval₂_homog z i₀ hz G le_rfl] at h2
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hz)


end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem deh_apply {ι S : Type*} [Field S] (v : ι → S) (i₀ : ι) (F : MvPolynomial ι ℤ) :
    deh v i₀ F = eval₂ (Int.castRingHom S) (fun i => v i / v i₀) F := rfl

theorem eval₂_eq_zero_of_monic {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : R →+* T) (hker : ∀ m, φ m = 0 → ψ m = 0) {P : Polynomial R}
    (hP : P.Monic) {θ : S} {ρ : T}
    (hmin : ∀ H : Polynomial R, H.natDegree < P.natDegree → H.eval₂ φ θ = 0 →
      ∀ j, φ (H.coeff j) = 0)
    (hθ : P.eval₂ φ θ = 0) (hρ : P.eval₂ ψ ρ = 0) (hP1 : P ≠ 1) {H : Polynomial R}
    (hH : H.eval₂ φ θ = 0) : H.eval₂ ψ ρ = 0 := by
  have hdec := Polynomial.modByMonic_add_div H P
  have h1 : (H %ₘ P).eval₂ φ θ = 0 := by
    have := congrArg (Polynomial.eval₂ φ θ) hdec
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hθ, zero_mul, add_zero, hH] at this
    exact this
  have h2 := hmin _ (Polynomial.natDegree_modByMonic_lt H hP hP1) h1
  have h3 : (H %ₘ P).eval₂ ψ ρ = 0 := by
    rw [← Polynomial.eval_map]
    have : (H %ₘ P).map ψ = 0 := by
      ext j; rw [Polynomial.coeff_map, hker _ (h2 j), Polynomial.coeff_zero]
    rw [this, Polynomial.eval_zero]
  rw [← hdec, Polynomial.eval₂_add, Polynomial.eval₂_mul, hρ, zero_mul, add_zero, h3]

variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ}

structure Gen (x : ι → Ω) (e : Fin (D + 1) → ι) where
  Θ : MvPolynomial ι ℤ
  P : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  monic : P.Monic
  root : P.eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ) = 0
  min : ∀ H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ), H.natDegree < P.natDegree →
    H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ) = 0 → ∀ j, deh (x ∘ e) 0 (H.coeff j) = 0
  dd : MvPolynomial (Fin (D + 1)) ℤ
  dd_ne : deh (x ∘ e) 0 dd ≠ 0
  Q : ι → Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  hQ : ∀ i, deh (x ∘ e) 0 dd * deh x (e 0) (X i) = (Q i).eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ)
  cc : MvPolynomial (Fin (D + 1)) ℤ
  cc_ne : deh (x ∘ e) 0 cc ≠ 0
  U : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  V : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  hUV : (U * P + V * Polynomial.derivative P - Polynomial.C cc).map (deh (x ∘ e) 0) = 0

variable {x : ι → Ω} {e : Fin (D + 1) → ι}

def Gen.HG [DecidableEq ι] (G : Gen x e) (F : MvPolynomial ι ℤ) :
    Polynomial (MvPolynomial (Fin (D + 1)) ℤ) :=
  MvPolynomial.eval₂ (Int.castRingHom _) (fun o : Option ι => o.elim (Polynomial.C G.dd) G.Q)
    (homog none F.totalDegree (rename some F))

def Gen.evQ (G : Gen x e) {S : Type*} [Field S] (ψ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S) :
    ι → S :=
  fun i => (G.Q i).eval₂ ψ t / ψ G.dd

theorem Gen.HG_eval [DecidableEq ι] (G : Gen x e) {S : Type*} [Field S]
    (ψ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S) (hd : ψ G.dd ≠ 0) (F : MvPolynomial ι ℤ) :
    (G.HG F).eval₂ ψ t =
      ψ G.dd ^ F.totalDegree * MvPolynomial.eval₂ (Int.castRingHom S) (G.evQ ψ t) F := by
  have h1 : (G.HG F).eval₂ ψ t = MvPolynomial.eval₂ (Int.castRingHom S)
      (fun o : Option ι => (o.elim (Polynomial.C G.dd) G.Q).eval₂ ψ t)
      (homog none F.totalDegree (rename some F)) := by
    rw [Gen.HG, ← Polynomial.coe_eval₂RingHom, MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  have hv : (fun o : Option ι => (o.elim (Polynomial.C G.dd) G.Q).eval₂ ψ t) none ≠ 0 := by
    simpa using hd
  rw [h1, eval₂_homog _ none hv _ (totalDegree_rename_le _ _)]
  simp only [Option.elim, Polynomial.eval₂_C]
  congr 1
  rw [deh_apply, eval₂_rename]
  congr 1
  funext i
  simp [Gen.evQ, Polynomial.eval₂_C]

theorem Gen.dehomogenized_generator_eval (G : Gen x e) :
    G.evQ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = fun i => x i / x (e 0) := by
  funext i
  rw [Gen.evQ, ← G.hQ i, mul_div_cancel_left₀ _ G.dd_ne, deh_X]

theorem Gen.P_ne_one (G : Gen x e) : G.P ≠ 1 := by
  intro h1
  have := G.root
  rw [h1, Polynomial.eval₂_one] at this
  exact one_ne_zero this

theorem Gen.transfer [DecidableEq ι] (G : Gen x e) (w : Fin (D + 1) → ℂ)
    (hker : ∀ m, deh (x ∘ e) 0 m = 0 → deh w 0 m = 0) (hdw : deh w 0 G.dd ≠ 0)
    {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) {F : MvPolynomial ι ℤ}
    {H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)}
    (h : deh x (e 0) F = H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) (G.evQ (deh w 0) ρ) F = H.eval₂ (deh w 0) ρ := by
  have key := eval₂_eq_zero_of_monic (deh (x ∘ e) 0) (deh w 0) hker G.monic G.min G.root hρ
    G.P_ne_one (H := G.HG F - Polynomial.C (G.dd ^ F.totalDegree) * H) (by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, G.HG_eval _ _ G.dd_ne,
        G.dehomogenized_generator_eval, ← deh_apply, h, map_pow, sub_self])
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, G.HG_eval _ _ hdw, map_pow,
    ← mul_sub, mul_eq_zero] at key
  exact sub_eq_zero.mp (key.resolve_left (pow_ne_zero _ hdw))

def Gen.zOf (G : Gen x e) (w : Fin (D + 1) → ℂ) (ρ : ℂ) : ι → ℂ :=
  fun i => w 0 * G.evQ (deh w 0) ρ i

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem coneMap_eq_zero_of_mem_pts {J : Type} [Fintype J] {P : Ideal (MvPolynomial J ℤ)}
    (hP : IsHomogIdeal ℤ P) {z : J → ℂ} (hz : z ∈ pts P) {f : MvPolynomial J ℤ} (hf : f ∈ P) :
    coneMap ℤ z f = 0 := by
  ext d
  rw [coeff_coneMap, Polynomial.coeff_zero]
  have h := hz.2 _ (hP f hf d)
  rw [eval_map] at h
  rw [aeval_def, show algebraMap ℤ ℂ = Int.castRingHom ℂ from Subsingleton.elim _ _]
  exact h

theorem coneMap_rename {J J' : Type} {R : Type*} [CommRing R] [Algebra ℤ R] (x : J → R) (e : J' → J)
    (g : MvPolynomial J' ℤ) : coneMap ℤ x (rename e g) = coneMap ℤ (x ∘ e) g := by
  simp only [coneMap, aeval_rename]
  rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}

structure Gen.Good (G : Gen x e) (w : Fin (D + 1) → ℂ) : Prop where
  w0 : w 0 ≠ 0
  ker : ∀ m, deh (x ∘ e) 0 m = 0 → deh w 0 m = 0
  dd : deh w 0 G.dd ≠ 0
  cc : deh w 0 G.cc ≠ 0

theorem deh_eval₂_rename {S : Type*} [Field S] (v : ι → S) (e : Fin (D + 1) → ι)
    (Θ : MvPolynomial ι ℤ) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)) :
    deh v (e 0) (H.eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom Θ) =
      H.eval₂ (deh (v ∘ e) 0) (deh v (e 0) Θ) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [deh_apply]
  · intro i
    simp [deh_apply]

variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}

private theorem eval₂_deh_eq_zero_of_good_of_root (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0)
    (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ))
    (hH : H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0) : H.eval₂ (deh w 0) ρ = 0 := by
  have hP1 : G.P ≠ 1 := by
    intro h
    have h' := G.root
    rw [h, Polynomial.eval₂_one] at h'
    exact one_ne_zero h'
  have hsplit : H %ₘ G.P + G.P * (H /ₘ G.P) = H := by
    first
    | exact Polynomial.modByMonic_add_div H G.P
    | exact Polynomial.modByMonic_add_div H G.monic
  have hdeg : (H %ₘ G.P).natDegree < G.P.natDegree := by
    first
    | exact Polynomial.natDegree_modByMonic_lt H G.monic hP1
    | exact Polynomial.natDegree_modByMonic_lt H G.monic hP1
  have hrx : (H %ₘ G.P).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
    have h2 := congrArg (fun p => p.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) hsplit
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, G.root, zero_mul, add_zero, hH] at h2
    exact h2
  have hc := G.min _ hdeg hrx
  have hrw : (H %ₘ G.P).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, hw.ker _ (hc j), Polynomial.coeff_zero]
  have hr : (H %ₘ G.P).eval₂ (deh w 0) ρ = 0 := by
    rw [← Polynomial.eval_map, hrw, Polynomial.eval_zero]
  have h3 := congrArg (fun p => p.eval₂ (deh w 0) ρ) hsplit
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hr, hρ, zero_mul, add_zero] at h3
  exact h3.symm

theorem Gen.zOf_e (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) (k : Fin (D + 1)) :
    G.zOf w ρ (e k) = w k := by
  have hH := eval₂_deh_eq_zero_of_good_of_root G hw hρ (G.Q (e k) - Polynomial.C (G.dd * X k)) (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, ← G.hQ (e k), map_mul, sub_eq_zero, deh_X, deh_X]
    rfl)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, map_mul, deh_X, sub_eq_zero] at hH
  have h0 := hw.w0
  have h1 := hw.dd
  simp only [Gen.zOf, Gen.evQ]
  rw [hH]
  first
  | (field_simp; done)
  | (field_simp; ring)

theorem Gen.deh_zOf (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0)
    (F : MvPolynomial ι ℤ) :
    deh (G.zOf w ρ) (e 0) F = MvPolynomial.eval₂ (Int.castRingHom ℂ) (G.evQ (deh w 0) ρ) F := by
  have h0 := hw.w0
  rw [deh_apply, G.zOf_e hw hρ 0]
  congr 1
  funext i
  simp only [Gen.zOf]
  first
  | (field_simp; done)
  | (field_simp; ring)

private theorem map_eval₂_X_mul_C_eq {K : Type*} [Field K] (φ : MvPolynomial (Fin (D + 1)) ℤ →+* K) (t : K)
    (f : MvPolynomial ι ℤ) :
    (MvPolynomial.eval₂ (Int.castRingHom (Polynomial (Polynomial (MvPolynomial (Fin (D + 1)) ℤ))))
        (fun i => Polynomial.X * Polynomial.C (G.Q i)) f).map (Polynomial.eval₂RingHom φ t) =
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial K))
        (fun i => Polynomial.X * Polynomial.C ((G.Q i).eval₂ φ t)) f := by
  have hk := MvPolynomial.eval₂_comp_left (Polynomial.mapRingHom (Polynomial.eval₂RingHom φ t))
    (Int.castRingHom _) (fun i => Polynomial.X * Polynomial.C (G.Q i)) f
  first
  | rw [Polynomial.coe_mapRingHom] at hk
  | skip
  rw [hk]
  congr 1
  · exact RingHom.ext_int _ _
  · funext i
    simp [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, Polynomial.coe_eval₂RingHom]

theorem Gen.zOf_mem (hx0 : x (e 0) ≠ 0) (hw : G.Good w) {ρ : ℂ}
    (hρ : G.P.eval₂ (deh w 0) ρ = 0) : G.zOf w ρ ∈ pts (coordIdeal ℤ x) := by
  show G.zOf w ρ ≠ 0 ∧ ∀ f ∈ coordIdeal ℤ x,
    MvPolynomial.eval (G.zOf w ρ) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0
  refine ⟨fun h => hw.w0 ?_, fun f hf => ?_⟩
  · rw [← G.zOf_e hw hρ 0, h, Pi.zero_apply]
  have hcone := RingHom.mem_ker.mp (show f ∈ RingHom.ker (coneMap ℤ x) from hf)
  have hrel : MvPolynomial.eval₂ (Int.castRingHom (Polynomial Ω))
      (fun i => Polynomial.X * Polynomial.C ((G.Q i).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ))) f =
      ((coneMap ℤ x) f).comp (Polynomial.C (deh (x ∘ e) 0 G.dd * (x (e 0))⁻¹) * Polynomial.X) := by
    have hk := MvPolynomial.eval₂_comp_left
      (Polynomial.compRingHom (Polynomial.C (deh (x ∘ e) 0 G.dd * (x (e 0))⁻¹) * Polynomial.X))
      (algebraMap ℤ (Polynomial Ω)) (fun i => Polynomial.C (x i) * Polynomial.X) f
    rw [coneMap, MvPolynomial.aeval_def, ← Polynomial.coe_compRingHom_apply, hk]
    congr 1
    · exact RingHom.ext_int _ _
    · funext i
      simp only [Function.comp_apply, Polynomial.coe_compRingHom_apply, Polynomial.mul_comp,
        Polynomial.C_comp, Polynomial.X_comp, ← G.hQ i, deh_X, div_eq_mul_inv, map_mul]
      ring
  have h2 := map_eval₂_X_mul_C_eq G (deh (x ∘ e) 0) (deh x (e 0) G.Θ) f
  rw [hrel, hcone, Polynomial.zero_comp] at h2
  have h3 : (MvPolynomial.eval₂ (Int.castRingHom (Polynomial (Polynomial (MvPolynomial (Fin (D + 1)) ℤ))))
        (fun i => Polynomial.X * Polynomial.C (G.Q i)) f).map (Polynomial.eval₂RingHom (deh w 0) ρ) = 0 := by
    ext d
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_eval₂RingHom]
    apply eval₂_deh_eq_zero_of_good_of_root G hw hρ
    have h4 := Polynomial.ext_iff.mp h2 d
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_eval₂RingHom] at h4
    exact h4
  rw [map_eval₂_X_mul_C_eq G (deh w 0) ρ f] at h3
  rw [MvPolynomial.eval_map]
  have h4 := congrArg (Polynomial.eval (w 0 / deh w 0 G.dd)) h3
  rw [Polynomial.eval_zero, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left] at h4
  have e1 : (Polynomial.evalRingHom (w 0 / deh w 0 G.dd)).comp (Int.castRingHom (Polynomial ℂ)) =
      Int.castRingHom ℂ := RingHom.ext_int _ _
  have e2 : (⇑(Polynomial.evalRingHom (w 0 / deh w 0 G.dd)) ∘
      fun i => Polynomial.X * Polynomial.C ((G.Q i).eval₂ (deh w 0) ρ)) = G.zOf w ρ := by
    funext i
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Gen.zOf, Gen.evQ]
    ring
  rw [e1, e2] at h4
  exact h4

private theorem sum_coeff_homogenize_eq_pow_mul_eval₂ {S : Type*} [Field S] (F : MvPolynomial ι ℤ) (v a : ι → S) (d : S)
    (hv : ∀ i, v i = a i / d) (hd : d ≠ 0) (N : ℕ) (hN : F.totalDegree ≤ N) :
    ∑ m ∈ F.support, ((MvPolynomial.coeff m F : ℤ) : S) * d ^ (N - ∑ i ∈ m.support, m i) *
      ∏ i ∈ m.support, a i ^ m i = d ^ N * MvPolynomial.eval₂ (Int.castRingHom S) v F := by
  rw [MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hs : ∑ i ∈ m.support, m i ≤ N := (MvPolynomial.le_totalDegree hm).trans hN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  simp only [hv, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, eq_intCast,
    Nat.add_sub_cancel_left, pow_add]
  first
  | (field_simp; done)
  | (field_simp; ring)
  | ring

private theorem map_homogenized_sub_dd_pow_X_eq {S : Type*} [Field S] (φ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S)
    (hd : φ G.dd ≠ 0) :
    Polynomial.eval₂ φ t ((∑ m ∈ G.Θ.support, Polynomial.C (MvPolynomial.C (MvPolynomial.coeff m G.Θ) *
        G.dd ^ (G.Θ.totalDegree - ∑ i ∈ m.support, m i)) * ∏ i ∈ m.support, G.Q i ^ m i) -
      Polynomial.C (G.dd ^ G.Θ.totalDegree) * Polynomial.X) =
      φ G.dd ^ G.Θ.totalDegree * (MvPolynomial.eval₂ (Int.castRingHom S) (G.evQ φ t) G.Θ - t) := by
  have hC : ∀ c : ℤ, φ (MvPolynomial.C c) = (c : S) := fun c => eq_intCast (φ.comp MvPolynomial.C) c
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_finset_prod, Polynomial.eval₂_pow, map_mul, map_pow, hC]
  rw [mul_sub, ← sum_coeff_homogenize_eq_pow_mul_eval₂ G.Θ (G.evQ φ t) (fun i => (G.Q i).eval₂ φ t) (φ G.dd) (fun i => rfl) hd
    G.Θ.totalDegree le_rfl]

theorem Gen.deh_zOf_Θ (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) :
    deh (G.zOf w ρ) (e 0) G.Θ = ρ := by
  have hx := map_homogenized_sub_dd_pow_X_eq G (deh (x ∘ e) 0) (deh x (e 0) G.Θ) G.dd_ne
  have hQx : MvPolynomial.eval₂ (Int.castRingHom Ω) (G.evQ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) G.Θ =
      deh x (e 0) G.Θ := by
    conv_rhs => rw [deh_apply]
    congr 1
    funext i
    simp only [Gen.evQ]
    rw [← G.hQ i, deh_X]
    first
    | exact mul_div_cancel_left₀ _ G.dd_ne
    | field_simp [G.dd_ne]
  rw [hQx, sub_self, mul_zero] at hx
  have hw' := eval₂_deh_eq_zero_of_good_of_root G hw hρ _ hx
  rw [map_homogenized_sub_dd_pow_X_eq G (deh w 0) ρ hw.dd] at hw'
  have h2 := (mul_eq_zero.mp hw').resolve_left (pow_ne_zero _ hw.dd)
  rw [G.deh_zOf hw hρ]
  exact sub_eq_zero.mp h2

private theorem deh_eq_zero_of_mem_pts_of_deh_eq_zero (hx0 : x (e 0) ≠ 0) (F : MvPolynomial ι ℤ) (hF : deh x (e 0) F = 0)
    {z : ι → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) (hz0 : z (e 0) ≠ 0) : deh z (e 0) F = 0 := by
  have hz' : z ≠ 0 ∧ ∀ f ∈ coordIdeal ℤ x,
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := hz
  have hmem : (∑ m ∈ F.support, MvPolynomial.C (MvPolynomial.coeff m F) *
      X (e 0) ^ (F.totalDegree - ∑ i ∈ m.support, m i) * ∏ i ∈ m.support, X i ^ m i) ∈ coordIdeal ℤ x := by
    show _ ∈ RingHom.ker (coneMap ℤ x)
    rw [RingHom.mem_ker, coneMap, map_sum]
    have h1 : ∀ m ∈ F.support, (aeval fun i => Polynomial.C (x i) * Polynomial.X)
        (MvPolynomial.C (MvPolynomial.coeff m F) * X (e 0) ^ (F.totalDegree - ∑ i ∈ m.support, m i) *
          ∏ i ∈ m.support, X i ^ m i) =
        Polynomial.C (((MvPolynomial.coeff m F : ℤ) : Ω) * x (e 0) ^ (F.totalDegree - ∑ i ∈ m.support, m i) *
          ∏ i ∈ m.support, x i ^ m i) * Polynomial.X ^ F.totalDegree := by
      intro m hm
      have hs : ∑ i ∈ m.support, m i ≤ F.totalDegree := MvPolynomial.le_totalDegree hm
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
      rw [hk, Nat.add_sub_cancel_left]
      simp only [map_mul, map_pow, map_prod, MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, algebraMap_int_eq, eq_intCast, map_intCast]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← map_sum Polynomial.C,
      sum_coeff_homogenize_eq_pow_mul_eval₂ F (fun i => x i / x (e 0)) x (x (e 0)) (fun i => rfl) hx0 _ le_rfl, ← deh_apply, hF,
      mul_zero, map_zero, zero_mul]
  have h2 := hz'.2 _ hmem
  rw [MvPolynomial.eval_map] at h2
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_prod, Int.coe_castRingHom] at h2
  rw [sum_coeff_homogenize_eq_pow_mul_eval₂ F (fun i => z i / z (e 0)) z (z (e 0)) (fun i => rfl) hz0 _ le_rfl, ← deh_apply] at h2
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hz0)

private theorem deh_rename' {S : Type*} [Field S] (v : ι → S) (F : MvPolynomial (Fin (D + 1)) ℤ) :
    deh v (e 0) (rename e F) = deh (v ∘ e) 0 F := by
  rw [deh_apply, deh_apply, MvPolynomial.eval₂_rename]
  rfl

theorem Gen.of_mem (hx0 : x (e 0) ≠ 0) (hw : G.Good w) {z : ι → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) (hze : ∀ k, z (e k) = w k) :
    G.P.eval₂ (deh w 0) (deh z (e 0) G.Θ) = 0 ∧ G.zOf w (deh z (e 0) G.Θ) = z := by
  have hz0 : z (e 0) ≠ 0 := by
    rw [hze 0]
    exact hw.w0
  have hze' : z ∘ e = w := funext hze
  constructor
  · have h := deh_eq_zero_of_mem_pts_of_deh_eq_zero hx0
      (G.P.eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom G.Θ)
      (by rw [deh_eval₂_rename]; exact G.root) hz hz0
    rw [deh_eval₂_rename, hze'] at h
    exact h
  · funext i
    have h := deh_eq_zero_of_mem_pts_of_deh_eq_zero hx0
      ((G.Q i).eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom G.Θ -
        rename e G.dd * X i)
      (by rw [map_sub, deh_eval₂_rename, map_mul, deh_rename', ← G.hQ i, sub_self]) hz hz0
    rw [map_sub, deh_eval₂_rename, map_mul, deh_rename', hze', deh_X, sub_eq_zero] at h
    have h0 := hw.w0
    have h1 := hw.dd
    simp only [Gen.zOf, Gen.evQ]
    rw [h, hze 0]
    first
    | (field_simp; done)
    | (field_simp; ring)

theorem Gen.sep (hw : G.Good w) : (G.P.map (deh w 0)).Separable := by
  have h0 : (G.U * G.P + G.V * Polynomial.derivative G.P - Polynomial.C G.cc).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    apply hw.ker
    rw [← Polynomial.coeff_map, G.hUV, Polynomial.coeff_zero]
  have h1 : G.U.map (deh w 0) * G.P.map (deh w 0) +
      G.V.map (deh w 0) * Polynomial.derivative (G.P.map (deh w 0)) =
      Polynomial.C (deh w 0 G.cc) := by
    rw [Polynomial.derivative_map, ← sub_eq_zero, ← h0]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  rw [Polynomial.separable_def]
  refine ⟨Polynomial.C (deh w 0 G.cc)⁻¹ * G.U.map (deh w 0),
    Polynomial.C (deh w 0 G.cc)⁻¹ * G.V.map (deh w 0), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul, inv_mul_cancel₀ hw.cc, Polynomial.C_1]

theorem Gen.mem_roots {ρ : ℂ} :
    ρ ∈ (G.P.map (deh w 0)).roots ↔ G.P.eval₂ (deh w 0) ρ = 0 := by
  rw [Polynomial.mem_roots (G.monic.map _).ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map]

theorem Gen.card_roots : (G.P.map (deh w 0)).roots.card = G.P.natDegree := by
  have hd : (G.P.map (deh w 0)).natDegree = G.P.natDegree := by
    first
    | exact G.monic.natDegree_map _
    | exact Polynomial.natDegree_map_of_monic G.monic _
  rw [← hd]
  first
  | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  | exact IsAlgClosed.card_roots_eq_natDegree
  | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  | simp

abbrev fib (x : ι → Ω) (e : Fin (D + 1) → ι) (w : Fin (D + 1) → ℂ) : Set (ι → ℂ) :=
  {z | z ∈ pts (coordIdeal ℤ x) ∧ ∀ k, z (e k) = w k}

theorem Gen.fib_eq (hx0 : x (e 0) ≠ 0) (hw : G.Good w) :
    fib x e w = G.zOf w '' {ρ | ρ ∈ (G.P.map (deh w 0)).roots} := by
  ext z
  constructor
  · rintro ⟨hz, hze⟩
    obtain ⟨h1, h2⟩ := G.of_mem hx0 hw hz hze
    exact ⟨_, G.mem_roots.2 h1, h2⟩
  · rintro ⟨ρ, hρ, rfl⟩
    have hρ' := G.mem_roots.1 hρ
    exact ⟨G.zOf_mem hx0 hw hρ', G.zOf_e hw hρ'⟩

theorem Gen.injOn (hw : G.Good w) :
    Set.InjOn (G.zOf w) {ρ | ρ ∈ (G.P.map (deh w 0)).roots} := by
  intro ρ₁ h₁ ρ₂ h₂ h
  calc ρ₁ = deh (G.zOf w ρ₁) (e 0) G.Θ := (G.deh_zOf_Θ hw (G.mem_roots.1 h₁)).symm
    _ = deh (G.zOf w ρ₂) (e 0) G.Θ := by rw [h]
    _ = ρ₂ := G.deh_zOf_Θ hw (G.mem_roots.1 h₂)

theorem Gen.roots_set (w : Fin (D + 1) → ℂ) :
    {ρ | ρ ∈ (G.P.map (deh w 0)).roots} = ((G.P.map (deh w 0)).roots.toFinset : Set ℂ) := by
  ext ρ
  simp

theorem Gen.fib_finite (hx0 : x (e 0) ≠ 0) (hw : G.Good w) : (fib x e w).Finite := by
  rw [G.fib_eq hx0 hw, G.roots_set]
  exact (Finset.finite_toSet _).image _

theorem Gen.fib_ncard (hx0 : x (e 0) ≠ 0) (hw : G.Good w) :
    (fib x e w).ncard = G.P.natDegree := by
  rw [G.fib_eq hx0 hw, Set.ncard_image_of_injOn (G.injOn hw), G.roots_set, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (G.sep hw)), G.card_roots]

theorem Gen.finsum_fib (hx0 : x (e 0) ≠ 0) (hw : G.Good w) (f : (ι → ℂ) → ℂ) :
    ∑ᶠ z ∈ fib x e w, f z = ((G.P.map (deh w 0)).roots.map fun ρ => f (G.zOf w ρ)).sum := by
  rw [G.fib_eq hx0 hw, finsum_mem_image (G.injOn hw), G.roots_set, finsum_mem_coe_finset,
    Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots (G.sep hw))]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem exists_implicit_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : E × ℂ → ℂ) (u : E × ℂ) (hf : ContDiffAt ℂ 1 f u) {c : ℂ} (hc : c ≠ 0)
    (hd : HasDerivAt (fun t => f (u.1, t)) c u.2) :
    ∃ (U : Set E) (τ : E → ℂ), IsOpen U ∧ u.1 ∈ U ∧ DifferentiableOn ℂ τ U ∧ τ u.1 = u.2 ∧
      ∀ w ∈ U, f (w, τ w) = f u := by
  have hfd : HasFDerivAt f (fderiv ℂ f u) u := (hf.differentiableAt one_ne_zero).hasFDerivAt
  have hi : HasFDerivAt (fun t : ℂ => (u.1, t)) (ContinuousLinearMap.inr ℂ E ℂ) u.2 := by
    first
    | exact hasFDerivAt_prodMk_right u.1 u.2
    | exact hasFDerivAt_prod_mk_right u.1 u.2
    | exact (hasFDerivAt_const u.1 u.2).prodMk (hasFDerivAt_id u.2)
    | exact (hasFDerivAt_const u.1 u.2).prod (hasFDerivAt_id u.2)
  have hcomp : HasFDerivAt (fun t : ℂ => f (u.1, t))
      ((fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ)) u.2 := by
    have hfd' : HasFDerivAt f (fderiv ℂ f u) (u.1, u.2) := hfd
    exact hfd'.comp u.2 hi
  have heq : (fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c := hcomp.unique hd.hasFDerivAt
  have hinv : ((fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
    rw [heq]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc), ?_⟩
    first
    | (ext; simp)
    | (ext x; simp [mul_comm])
  have ev := IsContDiffImplicitAt.apply_implicitFunction hf one_ne_zero hinv
  have cd := IsContDiffImplicitAt.contDiffAt_implicitFunction hf one_ne_zero hinv
  have ev2 := IsContDiffImplicitAt.eventually_implicitFunction_apply_eq hf one_ne_zero hinv
  have hval : hf.implicitFunction one_ne_zero hinv u.1 = u.2 := (ev2.self_of_nhds).1 rfl
  have ecd : ∀ᶠ y in 𝓝 u.1, ContDiffAt ℂ 1 (hf.implicitFunction one_ne_zero hinv) y := by
    first
    | exact cd.eventually (by simp)
    | exact cd.eventually (by decide)
    | exact cd.eventually ENat.one_ne_top
  obtain ⟨U, hUsub, hUo, hUmem⟩ := eventually_nhds_iff.mp (ev.and ecd)
  exact ⟨U, hf.implicitFunction one_ne_zero hinv, hUo, hUmem,
    fun y hy => ((hUsub y hy).2.differentiableAt one_ne_zero).differentiableWithinAt, hval,
    fun y hy => (hUsub y hy).1⟩

theorem contDiffAt_eval₂ {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (e₀ : E) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (G : MvPolynomial ι ℤ) : ContDiffAt ℂ 1 (fun e => eval₂ (Int.castRingHom ℂ) (g e) G) e₀ := by
  induction G using MvPolynomial.induction_on
  next r =>
    simp only [eval₂_C]
    exact contDiffAt_const
  next p q hp hq =>
    simp only [eval₂_add]
    exact hp.add hq
  next p i hp =>
    simp only [eval₂_mul, eval₂_X]
    exact hp.mul (hg i)

theorem contDiffAt_deh {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (h0 : g e₀ i₀ ≠ 0) (G : MvPolynomial ι ℤ) : ContDiffAt ℂ 1 (fun e => deh (g e) i₀ G) e₀ := by
  simp only [deh_apply]
  exact contDiffAt_eval₂ (fun e i => g e i / g e i₀) e₀ (fun i => (hg i).div (hg i₀) h0) G

theorem contDiffAt_eval₂_deh {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (t : E → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (ht : ContDiffAt ℂ 1 t e₀) (h0 : g e₀ i₀ ≠ 0) (H : Polynomial (MvPolynomial ι ℤ)) :
    ContDiffAt ℂ 1 (fun e => H.eval₂ (deh (g e) i₀) (t e)) e₀ := by
  refine Polynomial.induction_on' H (fun p q hp hq => ?_) (fun n a => ?_)
  · simp only [Polynomial.eval₂_add]
    exact hp.add hq
  · simp only [Polynomial.eval₂_monomial]
    exact (contDiffAt_deh g e₀ i₀ hg h0 a).mul (ht.pow n)

theorem differentiableAt_eval₂_deh {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (t : E → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (ht : DifferentiableAt ℂ t e₀) (h0 : g e₀ i₀ ≠ 0) (H : Polynomial (MvPolynomial ι ℤ)) :
    DifferentiableAt ℂ (fun e => H.eval₂ (deh (g e) i₀) (t e)) e₀ := by
  refine Polynomial.induction_on' H (fun p q hp hq => ?_) (fun n a => ?_)
  · simp only [Polynomial.eval₂_add]
    exact hp.add hq
  · simp only [Polynomial.eval₂_monomial]
    exact ((contDiffAt_deh g e₀ i₀ hg h0 a).differentiableAt one_ne_zero).mul (ht.pow n)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω}
  {e : Fin (D + 1) → ι} (G : Gen x e)

theorem Gen.exists_section (hx0 : x (e 0) ≠ 0) {W : Set (Fin (D + 1) → ℂ)} (hWo : IsOpen W)
    (hgood : ∀ w ∈ W, G.Good w) {w : Fin (D + 1) → ℂ} (hw : w ∈ W) {z : ι → ℂ}
    (hz : z ∈ fib x e w) :
    ∃ (U : Set (Fin (D + 1) → ℂ)) (γ : (Fin (D + 1) → ℂ) → ι → ℂ),
      IsOpen U ∧ w ∈ U ∧ DifferentiableOn ℂ γ U ∧ γ w = z ∧ ∀ w' ∈ U, γ w' ∈ fib x e w' := by
  have hgw := hgood w hw
  obtain ⟨hroot, hzeq⟩ := G.of_mem hx0 hgw hz.1 hz.2
  generalize hρ : deh z (e 0) G.Θ = ρ at hroot hzeq
  have hp1 : ∀ i, ContDiffAt ℂ 1 (fun p : (Fin (D + 1) → ℂ) × ℂ => p.1 i) (w, ρ) := by
    intro i
    first
    | fun_prop
    | exact ((contDiff_apply ℂ ℂ i).comp contDiff_fst).contDiffAt
    | exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D + 1) => ℂ) i).comp
        (ContinuousLinearMap.fst ℂ (Fin (D + 1) → ℂ) ℂ)).contDiff.contDiffAt
  have hcd : ContDiffAt ℂ 1 (fun p : (Fin (D + 1) → ℂ) × ℂ => G.P.eval₂ (deh p.1 0) p.2) (w, ρ) :=
    contDiffAt_eval₂_deh (fun p : (Fin (D + 1) → ℂ) × ℂ => p.1) (fun p => p.2) (w, ρ) 0 hp1
      contDiffAt_snd hgw.w0 G.P
  have hd0 := (G.P.map (deh w 0)).hasDerivAt ρ
  simp only [Polynomial.eval_map] at hd0
  have hsep := G.sep hgw
  rw [Polynomial.separable_def] at hsep
  obtain ⟨a, b, hab⟩ := hsep
  have hev := congrArg (Polynomial.eval ρ) hab
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_map, hroot, mul_zero, zero_add] at hev
  have hc : Polynomial.eval ρ (Polynomial.derivative (G.P.map (deh w 0))) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hev
    exact zero_ne_one hev
  obtain ⟨U', τ, hU'o, hwU', hτd, hτw, hτf⟩ :=
    exists_implicit_section (fun p : (Fin (D + 1) → ℂ) × ℂ => G.P.eval₂ (deh p.1 0) p.2) (w, ρ) hcd hc hd0
  have hτw' : τ w = ρ := hτw
  have hproj : ∀ (v : Fin (D + 1) → ℂ) j, ContDiffAt ℂ 1 (fun u : Fin (D + 1) → ℂ => u j) v := by
    intro v j
    first
    | fun_prop
    | exact (contDiff_apply ℂ ℂ j).contDiffAt
    | exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D + 1) => ℂ) j).contDiff.contDiffAt
  refine ⟨U' ∩ W, fun w' => G.zOf w' (τ w'), hU'o.inter hWo, ⟨hwU', hw⟩, ?_, ?_, ?_⟩
  · intro w' hw'
    have hg' := hgood w' hw'.2
    have hτa : DifferentiableAt ℂ τ w' := hτd.differentiableAt (hU'o.mem_nhds hw'.1)
    apply DifferentiableAt.differentiableWithinAt
    rw [differentiableAt_pi]
    intro i
    have hA := differentiableAt_eval₂_deh (fun u => u) τ w' 0 (hproj w') hτa hg'.w0 (G.Q i)
    have hB := (contDiffAt_deh (fun u => u) w' 0 (hproj w') hg'.w0 G.dd).differentiableAt one_ne_zero
    have hC := hA.mul (hB.inv hg'.dd)
    simp only [Gen.zOf, Gen.evQ, div_eq_mul_inv]
    exact ((hproj w' 0).differentiableAt one_ne_zero).mul hC
  · show G.zOf w (τ w) = z
    rw [hτw']
    exact hzeq
  · intro w' hw'
    have hg' := hgood w' hw'.2
    have hr : G.P.eval₂ (deh w' 0) (τ w') = 0 := (hτf w' hw'.1).trans hroot
    exact ⟨G.zOf_mem hx0 hg' hr, G.zOf_e hg' hr⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def psumQ (δ k : ℕ) : MvPolynomial (Fin δ) ℤ :=
  (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose

theorem aeval_psumQ (δ k : ℕ) :
    aeval (fun i : Fin δ => esymm (Fin δ) ℤ (i + 1)) (psumQ δ k) = psum (Fin δ) ℤ k := by
  have h := (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose_spec
  have h2 := congrArg Subtype.val h
  first
  | (rw [esymmAlgHom_apply] at h2; exact h2)
  | exact h2
  | simpa [psumQ, esymmAlgHom_apply] using h2

theorem sum_pow_eq_aeval_psumQ {S : Type*} [CommRing S] {δ : ℕ} (f : Fin δ → S) (k : ℕ) :
    ∑ i, f i ^ k =
      aeval (fun i : Fin δ => (Finset.univ.val.map f).esymm (i + 1)) (psumQ δ k) := by
  have h := congrArg (aeval f) (aeval_psumQ δ k)
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h
  simp only [MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
  rw [h]
  simp [MvPolynomial.psum]

theorem multiset_sum_pow_eq {S : Type*} [CommRing S] (s : Multiset S) {n : ℕ}
    (hn : Multiset.card s = n) (k : ℕ) :
    (s.map (· ^ k)).sum = aeval (fun i : Fin n => s.esymm (i + 1)) (psumQ n k) := by
  obtain ⟨l, rfl⟩ : ∃ l : List S, (l : Multiset S) = s := ⟨_, (Quotient.exists_rep s).choose_spec⟩
  rw [Multiset.coe_card] at hn
  subst hn
  have hs : (Finset.univ.val.map l.get : Multiset S) = (l : Multiset S) := by
    first
    | rw [Fin.univ_val_map, List.ofFn_get]
    | simp [Fin.univ_val_map, List.ofFn_get]
  have key := sum_pow_eq_aeval_psumQ l.get k
  rw [hs] at key
  rw [← key, Finset.sum_eq_multiset_sum, ← hs, Multiset.map_map] <;> rfl

def psumC {R : Type*} [CommRing R] (p : Polynomial R) (n k : ℕ) : R :=
  aeval (fun i : Fin n => (-1) ^ (i.val + 1) * p.coeff (n - (i.val + 1))) (psumQ n k)

theorem map_psumC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : Polynomial R)
    (n k : ℕ) : φ (psumC p n k) = psumC (p.map φ) n k := by
  unfold psumC
  induction psumQ n k using MvPolynomial.induction_on
  next a => simp
  next P1 P2 h1 h2 => simp only [map_add, h1, h2]
  next P1 i h1 => simp [h1, Polynomial.coeff_map]

theorem sum_roots_pow {K : Type*} [Field K] (p : Polynomial K) (hm : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) (k : ℕ) :
    (p.roots.map (· ^ k)).sum = psumC p p.natDegree k := by
  rw [multiset_sum_pow_eq p.roots hroots k, psumC]
  refine congrArg (fun F => aeval F (psumQ _ k)) (funext fun i => ?_)
  have hi : (i : ℕ) + 1 ≤ p.natDegree := i.isLt
  rw [Polynomial.coeff_eq_esymm_roots_of_card hroots (Nat.sub_le _ _), hm.leadingCoeff,
    Nat.sub_sub_self hi, one_mul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}

def Gen.S (G : Gen x e) (j : ℕ) : MvPolynomial (Fin (D + 1)) ℤ :=
  psumC G.P G.P.natDegree j

def Gen.TrP (G : Gen x e) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)) :
    MvPolynomial (Fin (D + 1)) ℤ :=
  ∑ j ∈ Finset.range (H.natDegree + 1), H.coeff j * G.S j

variable [DecidableEq ι] (G : Gen x e)

theorem Gen.deh_S {w : Fin (D + 1) → ℂ} (j : ℕ) :
    deh w 0 (G.S j) = ((G.P.map (deh w 0)).roots.map (· ^ j)).sum := by
  have hm : (G.P.map (deh w 0)).Monic := G.monic.map _
  have hd : (G.P.map (deh w 0)).natDegree = G.P.natDegree := G.monic.natDegree_map _
  have hc : Multiset.card (G.P.map (deh w 0)).roots = (G.P.map (deh w 0)).natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
    | exact (IsAlgClosed.splits _).card_roots
    | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  rw [sum_roots_pow _ hm hc j, hd, Gen.S, map_psumC]

private theorem eval₂_deh_eq_zero_of_mem_roots {w : Fin (D + 1) → ℂ} (hw : G.Good w)
    (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ))
    (hH : H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) : H.eval₂ (deh w 0) ρ = 0 := by
  have hP1 : G.P ≠ 1 := by
    intro h1
    have h2 := G.root
    rw [h1, Polynomial.eval₂_one] at h2
    exact one_ne_zero h2
  have hdecomp : H %ₘ G.P + G.P * (H /ₘ G.P) = H := by
    first
    | exact Polynomial.modByMonic_add_div H G.monic
    | exact Polynomial.modByMonic_add_div H G.P
    | exact Polynomial.modByMonic_add_div H G.P G.monic
  have hr : (H %ₘ G.P).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
    have h1 := congrArg (Polynomial.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) hdecomp
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, G.root, zero_mul, add_zero, hH] at h1
    exact h1
  have hcoef := G.min (H %ₘ G.P) (Polynomial.natDegree_modByMonic_lt H G.monic hP1) hr
  have hrw : (H %ₘ G.P).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact hw.ker _ (hcoef j)
  have hPρ : G.P.eval₂ (deh w 0) ρ = 0 := by
    have h3 := (Polynomial.mem_roots (G.monic.map _).ne_zero).mp hρ
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at h3
  have h2 := congrArg (Polynomial.eval₂ (deh w 0) ρ) hdecomp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hPρ, zero_mul, add_zero] at h2
  rw [← h2, ← Polynomial.eval_map, hrw, Polynomial.eval_zero]

private theorem deh_dd_mul_deh_zOf_X_eq_eval₂_Q {w : Fin (D + 1) → ℂ} (hw : G.Good w) (i : ι) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) :
    deh w 0 G.dd * deh (G.zOf w ρ) (e 0) (X i) = (G.Q i).eval₂ (deh w 0) ρ := by
  have hx : ∀ j, deh x (e 0) (X j) = x j / x (e 0) := fun j => by simp [deh]
  have hz : ∀ j, deh (G.zOf w ρ) (e 0) (X j) = G.zOf w ρ j / G.zOf w ρ (e 0) :=
    fun j => by simp [deh]
  have hzj : ∀ j, G.zOf w ρ j = w 0 * ((G.Q j).eval₂ (deh w 0) ρ / deh w 0 G.dd) := fun j => rfl
  have hd := hw.dd
  have h0 := hw.w0
  rw [hz, hzj, hzj]
  by_cases hxe : x (e 0) = 0
  · have hq : ∀ j, (G.Q j).eval₂ (deh w 0) ρ = 0 := by
      intro j
      refine eval₂_deh_eq_zero_of_mem_roots G hw (G.Q j) ?_ hρ
      rw [← G.hQ j, hx, hxe, div_zero, mul_zero]
    simp [hq]
  · have hxs : (G.Q (e 0) - Polynomial.C G.dd).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, ← G.hQ (e 0), hx, div_self hxe, mul_one,
        sub_self]
    have h1 := eval₂_deh_eq_zero_of_mem_roots G hw _ hxs hρ
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, sub_eq_zero] at h1
    rw [h1]
    field_simp
    first | done | ring

private theorem exists_pow_mul_eq_eval₂_theta {w : Fin (D + 1) → ℂ} (hw : G.Good w) (f : MvPolynomial ι ℤ) :
    ∃ (N : ℕ) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)),
      deh (x ∘ e) 0 G.dd ^ N * deh x (e 0) f = H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) ∧
      ∀ ρ ∈ (G.P.map (deh w 0)).roots,
        deh w 0 G.dd ^ N * deh (G.zOf w ρ) (e 0) f = H.eval₂ (deh w 0) ρ := by
  induction f using MvPolynomial.induction_on
  next a =>
    refine ⟨0, Polynomial.C (MvPolynomial.C a), ?_, fun ρ _ => ?_⟩ <;>
      (rw [pow_zero, one_mul, Polynomial.eval₂_C]; simp [deh])
  next f1 f2 h1 h2 =>
    obtain ⟨N1, H1, hx1, hw1⟩ := h1
    obtain ⟨N2, H2, hx2, hw2⟩ := h2
    refine ⟨N1 + N2, Polynomial.C (G.dd ^ N2) * H1 + Polynomial.C (G.dd ^ N1) * H2, ?_,
      fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hx1, ← hx2, map_add, map_pow, map_pow]
      ring
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hw1 ρ hρ, ← hw2 ρ hρ, map_add, map_pow, map_pow]
      ring
  next f1 i h1 =>
    obtain ⟨N, H, hx1, hw1⟩ := h1
    refine ⟨N + 1, H * G.Q i, ?_, fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_mul, ← hx1, ← G.hQ i, map_mul]
      ring
    · rw [Polynomial.eval₂_mul, ← hw1 ρ hρ, ← deh_dd_mul_deh_zOf_X_eq_eval₂_Q G hw i hρ, map_mul]
      ring

theorem Gen.trace_w {w : Fin (D + 1) → ℂ} (hw : G.Good w) (Tr : Ω → Ω)
    (hTr : ∀ H, Tr (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) = deh (x ∘ e) 0 (G.TrP H))
    (hsc : ∀ (m : MvPolynomial (Fin (D + 1)) ℤ) (F : MvPolynomial ι ℤ),
      Tr (deh (x ∘ e) 0 m * deh x (e 0) F) = deh (x ∘ e) 0 m * Tr (deh x (e 0) F))
    {f : MvPolynomial ι ℤ} {g : MvPolynomial (Fin (D + 1)) ℤ}
    (h : deh (x ∘ e) 0 g = Tr (deh x (e 0) f)) :
    deh w 0 g = ((G.P.map (deh w 0)).roots.map fun ρ => deh (G.zOf w ρ) (e 0) f).sum := by
  obtain ⟨N, H, hx, hwr⟩ := exists_pow_mul_eq_eval₂_theta G hw f
  have hker : deh (x ∘ e) 0 (G.dd ^ N * g - G.TrP H) = 0 := by
    rw [map_sub, map_mul, h, ← hTr H, ← hx, ← hsc, map_pow, sub_self]
  have hwk := hw.ker _ hker
  rw [map_sub, map_mul, map_pow, sub_eq_zero] at hwk
  have hTrw : deh w 0 (G.TrP H) =
      ((G.P.map (deh w 0)).roots.map fun ρ => H.eval₂ (deh w 0) ρ).sum := by
    rw [Gen.TrP, map_sum]
    simp only [map_mul, G.deh_S, Polynomial.eval₂_eq_sum_range]
    generalize (G.P.map (deh w 0)).roots = s
    refine Multiset.induction_on s ?_ ?_
    · simp
    · intro a s ih
      simp [Multiset.map_cons, Multiset.sum_cons, mul_add, Finset.sum_add_distrib, ih]
  have hdN : deh w 0 G.dd ^ N ≠ 0 := pow_ne_zero _ hw.dd
  apply mul_left_cancel₀ hdN
  rw [hwk, hTrw, ← Multiset.sum_map_mul_left]
  congr 1
  exact Multiset.map_congr rfl fun ρ hρ => (hwr ρ hρ).symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open Polynomial IntermediateField

private lemma exists_int_primitive_element_pair {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero E] [Finite (IntermediateField F E)] (α β : E) :
    ∃ n : ℤ, α ∈ F⟮α + (n : E) * β⟯ ∧ β ∈ F⟮α + (n : E) * β⟯ := by
  obtain ⟨a, b, hab, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => F⟮α + (n : E) * β⟯)
  have ha : α + (a : E) * β ∈ F⟮α + (b : E) * β⟯ := by
    rw [← heq]; exact IntermediateField.mem_adjoin_simple_self F _
  have hb : α + (b : E) * β ∈ F⟮α + (b : E) * β⟯ := IntermediateField.mem_adjoin_simple_self F _
  have hne : (a : E) - b ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hab
  have hβ : β ∈ F⟮α + (b : E) * β⟯ := by
    have hsub := sub_mem ha hb
    have h1 : (α + (a : E) * β) - (α + (b : E) * β) = ((a : E) - b) * β := by ring
    rw [h1] at hsub
    have hc : (a : E) - b ∈ F⟮α + (b : E) * β⟯ := sub_mem (intCast_mem _ a) (intCast_mem _ b)
    have := mul_mem (inv_mem hc) hsub
    rwa [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at this
  refine ⟨b, ?_, hβ⟩
  have := sub_mem hb (mul_mem (intCast_mem _ b) hβ)
  simpa using this

theorem exists_int_primitive {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F]
    [CharZero E] [FiniteDimensional F E] {ι : Type*} [Fintype ι] (v : ι → E)
    (hv : adjoin F (Set.range v) = ⊤) : ∃ c : ι → ℤ, F⟮∑ i, (c i : E) * v i⟯ = ⊤ := by
  classical
  haveI hfinite : Finite (IntermediateField F E) := by
    first
    | exact inferInstance
    | exact Field.finite_intermediateField_of_exists_primitive_element F E
        (Field.exists_primitive_element F E)
    | exact Field.finite_intermediateField_of_exists_primitive_element
        (Field.exists_primitive_element F E)
    | exact (Field.exists_primitive_element_iff_finite_intermediateField F E).mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
    | exact Field.exists_primitive_element_iff_finite_intermediateField.mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
  have key : ∀ s : Finset ι, ∃ c : ι → ℤ, ∀ i ∈ s, v i ∈ F⟮∑ j, (c j : E) * v j⟯ := by
    intro s
    refine Finset.induction_on s ⟨0, by simp⟩ ?_
    intro j s _ ih
    obtain ⟨c, hc⟩ := ih
    obtain ⟨n, hα, hβ⟩ := exists_int_primitive_element_pair (F := F) (∑ i, (c i : E) * v i) (v j)
    refine ⟨c + Pi.single j n, ?_⟩
    have h2 : ∑ i, (((Pi.single j n : ι → ℤ) i : ℤ) : E) * v i = (n : E) * v j := by
      rw [Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
      simp
    have hsum : ∑ i, (((c + Pi.single j n : ι → ℤ) i : ℤ) : E) * v i =
        ∑ i, (c i : E) * v i + (n : E) * v j := by
      simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, h2]
    rw [hsum]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hβ
    · exact (IntermediateField.adjoin_simple_le_iff.mpr hα) (hc i hi)
  obtain ⟨c, hc⟩ := key Finset.univ
  refine ⟨c, top_le_iff.mp ?_⟩
  rw [← hv, IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact hc i (Finset.mem_univ i)

theorem trace_pow_eq_psumC {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero K]
    [FiniteDimensional K E] {θ : E} (hθ : K⟮θ⟯ = ⊤) (j : ℕ) :
    Algebra.trace K E (θ ^ j) = psumC (minpoly K θ) (minpoly K θ).natDegree j := by
  classical
  have hint : IsIntegral K θ := IsIntegral.of_finite K θ
  have hmon := minpoly.monic hint
  have hsep : (minpoly K θ).Separable := Algebra.IsSeparable.isSeparable K θ
  have hc : Multiset.card ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
    | exact (IsAlgClosed.splits _).card_roots
    | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  have hnd : ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.Nodup :=
    Polynomial.nodup_roots hsep.map
  have hadj : Algebra.adjoin K {θ} = ⊤ := by
    first
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
          (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hint.isAlgebraic), hθ,
        IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) := by
    intro σ τ h
    exact AlgHom.ext_of_adjoin_eq_top hadj (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h)
  have hfin : Module.finrank K E = (minpoly K θ).natDegree := by
    rw [← IntermediateField.finrank_top', ← hθ, IntermediateField.adjoin.finrank hint]
  have himg : Finset.univ.image (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmon.map _).ne_zero]
      first
      | rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
      | simp [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]
    · rw [Multiset.toFinset_card_of_nodup hnd, hc, hmon.natDegree_map,
        Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hfin]
      exact (AlgHom.card K E (AlgebraicClosure K)).ge
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_psumC, ← hmon.natDegree_map (algebraMap K (AlgebraicClosure K)),
    ← sum_roots_pow _ (hmon.map _) hc j]
  first
  | rw [trace_eq_sum_embeddings (AlgebraicClosure K)]
  | rw [trace_eq_sum_embeddings]
  | rw [Algebra.trace_eq_sum_embeddings (AlgebraicClosure K)]
  simp only [map_pow]
  have hsum := Finset.sum_image (s := Finset.univ)
    (g := fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) (f := fun y => y ^ j)
    (fun σ _ τ _ h => hinj h)
  rw [himg] at hsum
  rw [← hsum, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

theorem exists_clear {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {ι : Type*} [Fintype ι] (q : ι → K[X]) :
    ∃ (b : A) (Q : ι → A[X]), b ≠ 0 ∧
      ∀ i, (Q i).map (algebraMap A K) = C (algebraMap A K b) * q i := by
  classical
  choose b hb using fun i =>
    IsLocalization.integerNormalization_map_to_map (M := nonZeroDivisors A) (q i)
  refine ⟨∏ i, (b i : A), fun i => C (∏ j ∈ Finset.univ.erase i, (b j : A)) *
    IsLocalization.integerNormalization (nonZeroDivisors A) (q i), ?_, fun i => ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => nonZeroDivisors.coe_ne_zero (b i)
  · rw [Polynomial.map_mul, hb i, Polynomial.map_C, ← algebraMap_smul K (b i : A) (q i),
      Polynomial.smul_eq_C_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [map_mul, Polynomial.C_mul, mul_assoc]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem coord_ne_zero {ι : Type*} (y : ι → Ω) (h : coordIdeal ℤ y = ⊥) (k : ι) : y k ≠ 0 := by
  intro hk
  have hmem : (MvPolynomial.X k : MvPolynomial ι ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker, coneMap]
    simp [hk]
  rw [h, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero k hmem

theorem div_mem_fnField (x : κ → Ω) (i j : κ) : x i / x j ∈ fnField x := by
  exact IntermediateField.subset_adjoin ℚ {t | ∃ i j, t = x i / x j} ⟨i, j, rfl⟩

theorem deh_mem_fnField {ι : Type*} (y : ι → Ω) (i₀ : ι) (m : MvPolynomial ι ℤ) :
    deh y i₀ m ∈ fnField y := by
  rw [deh_apply]
  induction m using MvPolynomial.induction_on
  · rw [MvPolynomial.eval₂_C]
    simpa using intCast_mem (fnField y) _
  · rw [MvPolynomial.eval₂_add]
    exact add_mem ‹_› ‹_›
  · rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact mul_mem ‹_› (div_mem_fnField y _ i₀)

def dehK (y : Fin (D + 1) → Ω) : MvPolynomial (Fin (D + 1)) ℤ →+* fnField y :=
  (deh y 0).codRestrict (fnField y).toSubfield.toSubring fun m => deh_mem_fnField y 0 m

@[simp] theorem coe_dehK (y : Fin (D + 1) → Ω) (m : MvPolynomial (Fin (D + 1)) ℤ) :
    ((dehK y m : fnField y) : Ω) = deh y 0 m := rfl

def chartGen (y : Fin (D + 1) → Ω) (k : {k : Fin (D + 1) // k ≠ 0}) : fnField y :=
  ⟨y k / y 0, div_mem_fnField y k 0⟩

def chartRing (y : Fin (D + 1) → Ω) : Subalgebra ℤ (fnField y) :=
  Algebra.adjoin ℤ (Set.range (chartGen y))

theorem aeval_chartGen (y : Fin (D + 1) → Ω) (g : MvPolynomial {k : Fin (D + 1) // k ≠ 0} ℤ) :
    ((MvPolynomial.aeval (chartGen y) g : fnField y) : Ω) =
      deh y 0 (MvPolynomial.rename Subtype.val g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [deh_apply]
  | add p q hp hq => simp only [map_add, AddMemClass.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.rename_X, MulMemClass.coe_mul, hp]
    congr 1
    simp [deh_apply, chartGen]

theorem chartGen_indep (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    AlgebraicIndependent ℤ (chartGen y) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro g hg
  have hy0 := coord_ne_zero y hfree 0
  set G := MvPolynomial.rename Subtype.val g
  have h1 : deh y 0 G = 0 := by
    rw [← aeval_chartGen]
    change (((MvPolynomial.aeval (chartGen y) g : fnField y)) : Ω) = 0
    rw [hg]; rfl
  have hH := homog_isHomogeneous (0 : Fin (D + 1)) G le_rfl
  have h2 : MvPolynomial.aeval y (homog 0 G.totalDegree G) = 0 := by
    rw [MvPolynomial.aeval_def, algebraMap_int_eq, eval₂_homog y 0 hy0 G le_rfl, h1, mul_zero]
  have h3 := mem_coordIdeal_of_isHomogeneous ℤ y hH h2
  rw [hfree, Ideal.mem_bot] at h3
  apply MvPolynomial.funext
  intro u
  let v : Fin (D + 1) → ℚ := fun k => if h : k = 0 then 1 else (u ⟨k, h⟩ : ℚ)
  have h4 := eval₂_homog v 0 (by simp [v]) G le_rfl
  rw [h3, MvPolynomial.eval₂_zero] at h4
  have h5 : deh v 0 G = ((MvPolynomial.eval u g : ℤ) : ℚ) := by
    rw [deh_apply, MvPolynomial.eval₂_rename, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
    congr 1
    funext k
    simp [v, k.2]
  rw [h5] at h4
  have h6 : ((MvPolynomial.eval u g : ℤ) : ℚ) = 0 := by
    have := h4.symm
    rwa [mul_eq_zero, or_iff_right (pow_ne_zero _ (by simp [v]))] at this
  simpa using h6

theorem chartRing_closed (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsIntegrallyClosed (chartRing y) := by
  have hind := chartGen_indep y hfree
  haveI : UniqueFactorizationMonoid (chartRing y) :=
    MulEquiv.uniqueFactorizationMonoid hind.aevalEquiv.toRingEquiv.toMulEquiv inferInstance
  haveI : IsDomain (chartRing y) := Subalgebra.isDomain _
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

theorem chartRing_frac (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsFractionRing (chartRing y) (fnField y) := by
  have hl : y 0 ≠ 0 := coord_ne_zero y hfree 0
  refine IsFractionRing.of_field _ _ fun z => ?_
  have hinj : Function.Injective (algebraMap (chartRing y) Ω) := by
    intro a b hab
    exact Subtype.val_injective (Subtype.val_injective hab)
  let F : Subfield Ω := (IsFractionRing.lift (K := FractionRing (chartRing y)) hinj).fieldRange
  have hgen : ∀ i, y i / y 0 ∈ F := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [div_self hl]; exact F.one_mem
    · refine ⟨algebraMap (chartRing y) (FractionRing (chartRing y))
        ⟨chartGen y ⟨i, hi⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩, ?_⟩
      rw [IsFractionRing.lift_algebraMap hinj]
      rfl
  have hle : (fnField y).toSubfield ≤ F := by
    unfold fnField
    refine IntermediateField.adjoin_le_subfield ℚ _ ?_ ?_
    · rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem F q
    · rintro _ ⟨i, j, rfl⟩
      have : y i / y j = (y i / y 0) / (y j / y 0) := by
        rw [div_div_div_cancel_right₀ hl]
      change y i / y j ∈ F
      rw [this]
      exact F.div_mem (hgen i) (hgen j)
  obtain ⟨w, hw⟩ := hle z.2
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := chartRing y) w
  refine ⟨a, b, Subtype.val_injective ?_⟩
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap] at hw
  rw [← hw]
  exact (map_div₀ (fnField y).val _ _).symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField

variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}

theorem coord_div_isIntegral (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) (i : ι) :
    IsIntegral (chartRing (x ∘ e)) (x i / x (e 0)) := by
  set y := x ∘ e with hy
  change IsIntegral _ (x i / y 0)
  have hl : y 0 ≠ 0 := coord_ne_zero y h.free 0
  have hinj : Function.Injective (coneMap ℤ y) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have : f ∈ coordIdeal ℤ y := by rw [coordIdeal, RingHom.mem_ker]; exact hf
    rwa [h.free, Ideal.mem_bot] at this
  let eqv : MvPolynomial (Fin (D + 1)) ℤ ≃ₐ[ℤ] coneRing ℤ y := AlgEquiv.ofInjective (coneMap ℤ y) hinj
  let w : Fin (D + 1) → chartRing y := fun k =>
    if hk : k = 0 then 1 else ⟨chartGen y ⟨k, hk⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩
  have hw : ∀ k, algebraMap (chartRing y) Ω (w k) = y k * (y 0)⁻¹ := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [w, mul_inv_cancel₀ hl]
    · simp only [w, dif_neg hk]
      change y k / y 0 = _
      exact div_eq_mul_inv _ _
  let ψ : Polynomial Ω →+* Ω := Polynomial.evalRingHom (y 0)⁻¹
  have hev : ∀ f : MvPolynomial (Fin (D + 1)) ℤ,
      ψ (coneMap ℤ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [coneMap, ψ]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]; simp [coneMap, ψ]
  let φ : coneRing ℤ y →+* chartRing y :=
    (MvPolynomial.aeval w).toRingHom.comp eqv.symm.toAlgHom.toRingHom
  have hrel : (algebraMap (chartRing y) Ω).comp φ = ψ.comp (algebraMap (coneRing ℤ y) _) := by
    ext r
    obtain ⟨f, rfl⟩ := eqv.surjective r
    have h1 : ((eqv f : coneRing ℤ y) : Polynomial Ω) = coneMap ℤ y f := rfl
    change algebraMap _ Ω (MvPolynomial.aeval w (eqv.symm (eqv f))) =
      ψ ((eqv f : coneRing ℤ y) : Polynomial Ω)
    rw [eqv.symm_apply_apply, h1, hev, ← MvPolynomial.aeval_algebraMap_apply,
      show (⇑(algebraMap (chartRing y) Ω) ∘ w) = fun k => y k * (y 0)⁻¹ from funext hw]
  have := IsIntegral.map_of_comp_eq φ ψ hrel (h.integral i)
  simpa [ψ, div_eq_mul_inv] using this

abbrev Lx (x : ι → Ω) (e : Fin (D + 1) → ι) : IntermediateField (fnField (x ∘ e)) Ω :=
  extendScalars (fnField_comp_le x e)

theorem Lx_eq (x : ι → Ω) (e : Fin (D + 1) → ι) (hx0 : x (e 0) ≠ 0) :
    Lx x e = adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  apply le_antisymm
  · intro t ht
    have key : fnField x ≤
        (adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))).restrictScalars ℚ := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro s ⟨i, j, rfl⟩
      have hi : x i / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨i, rfl⟩
      have hj : x j / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨j, rfl⟩
      have hq := div_mem hi hj
      have e2 : x i / x (e 0) / (x j / x (e 0)) = x i / x j := by
        by_cases hj0 : x j = 0
        · simp [hj0]
        · field_simp
      rw [e2] at hq
      exact hq
    exact key ht
  · rw [IntermediateField.adjoin_le_iff]
    rintro t ⟨i, rfl⟩
    exact div_mem_fnField x i (e 0)

theorem Lx_finite (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (Lx x e) := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero (x ∘ e) h.free 0
  have hint : ∀ t ∈ Set.range (fun i => x i / x (e 0)), IsIntegral (fnField (x ∘ e)) t := by
    rintro t ⟨i, rfl⟩
    exact (coord_div_isIntegral x e h i).tower_top
  rw [Lx_eq x e hx0]
  exact IntermediateField.finiteDimensional_adjoin hint

def gL (x : ι → Ω) (e : Fin (D + 1) → ι) (i : ι) : Lx x e :=
  ⟨x i / x (e 0), div_mem_fnField x i (e 0)⟩

theorem adjoin_gL (x : ι → Ω) (e : Fin (D + 1) → ι) (hx0 : x (e 0) ≠ 0) :
    adjoin (fnField (x ∘ e)) (Set.range (gL x e)) = ⊤ := by
  apply IntermediateField.map_injective (Lx x e).val
  have htop : (⊤ : IntermediateField (fnField (x ∘ e)) (Lx x e)).map (Lx x e).val = Lx x e := by
    ext z
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨w, -, rfl⟩
      exact w.2
    · intro hz
      exact ⟨⟨z, hz⟩, IntermediateField.mem_top, rfl⟩
  rw [IntermediateField.adjoin_map, ← Set.range_comp, htop]
  exact (Lx_eq x e hx0).symm

theorem exists_primitive (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    ∃ c : ι → ℤ, (fnField (x ∘ e))⟮∑ i, (c i : Lx x e) * gL x e i⟯ = ⊤ := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero (x ∘ e) h.free 0
  have := Lx_finite x e h
  exact exists_int_primitive (gL x e) (adjoin_gL x e hx0)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField

variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}

theorem fnTrace_coe (x : ι → Ω) (e : Fin (D + 1) → ι) (s : Lx x e) :
    fnTrace x e (s : Ω) =
      ((Algebra.trace (fnField (x ∘ e)) (Lx x e) s : fnField (x ∘ e)) : Ω) := by
  have hs : (s : Ω) ∈ fnField x := (IntermediateField.mem_extendScalars _).mp s.2
  unfold fnTrace
  rw [dif_pos hs]

theorem exists_gen (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    ∃ G : Gen x e, G.P.natDegree = projDeg x e ∧
      (∀ H, fnTrace x e (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) =
        deh (x ∘ e) 0 (G.TrP H)) ∧
      (∀ m F, fnTrace x e (deh (x ∘ e) 0 m * deh x (e 0) F) =
        deh (x ∘ e) 0 m * fnTrace x e (deh x (e 0) F)) := by
  classical
  set y := x ∘ e with hy
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero y h.free 0
  have hfin := Lx_finite x e h
  obtain ⟨c, hc⟩ := exists_primitive x e h
  set θL : Lx x e := ∑ i, (c i : Lx x e) * gL x e i with hθLdef
  let Θ : MvPolynomial ι ℤ := ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i
  have hθ : deh x (e 0) Θ = (θL : Ω) := by
    simp [Θ, θL, gL, deh_X]
  obtain ⟨θ, hθdef⟩ : ∃ θ : Ω, θ = deh x (e 0) Θ := ⟨_, rfl⟩
  have hθθ : θ = (θL : Ω) := hθdef.trans hθ

  have hfrac := chartRing_frac y h.free
  have hclosed := chartRing_closed y h.free
  have hθA : IsIntegral (chartRing y) θ := by
    have : (θL : Ω) = ∑ i, (c i : Ω) * (x i / x (e 0)) := by simp [θL, gL]
    rw [hθθ, this]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (coord_div_isIntegral x e h i)
    simpa using isIntegral_algebraMap (R := chartRing y) (A := Ω) (x := ((c i : ℤ) : chartRing y))
  have hθK : IsIntegral (fnField y) θ := hθA.tower_top
  have hPK : minpoly (fnField y) θ = (minpoly (chartRing y) θ).map (algebraMap (chartRing y) (fnField y)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (fnField y) hθA
  have hθL : minpoly (fnField y) θ = minpoly (fnField y) θL := by
    rw [hθθ]
    exact minpoly.algebraMap_eq (algebraMap (Lx x e) Ω).injective θL
  have hδ : (minpoly (fnField y) θL).natDegree = projDeg x e := by
    rw [projDeg, relfinrank_eq_finrank_of_le (fnField_comp_le x e), ← IntermediateField.finrank_top',
      ← hc, IntermediateField.adjoin.finrank (.of_finite _ _)]

  have hind := chartGen_indep y h.free
  let r : chartRing y →+* MvPolynomial (Fin (D + 1)) ℤ :=
    (MvPolynomial.rename Subtype.val).toRingHom.comp hind.aevalEquiv.symm.toRingHom
  have hr : ∀ a : chartRing y, deh y 0 (r a) = algebraMap (chartRing y) Ω a := by
    intro a
    obtain ⟨g, rfl⟩ := hind.aevalEquiv.surjective a
    have h1 : r (hind.aevalEquiv g) = MvPolynomial.rename Subtype.val g := by
      show MvPolynomial.rename Subtype.val (hind.aevalEquiv.symm (hind.aevalEquiv g)) = _
      rw [AlgEquiv.symm_apply_apply]
    have h2 : ((hind.aevalEquiv g : Algebra.adjoin ℤ (Set.range (chartGen y))) : fnField y) =
        MvPolynomial.aeval (chartGen y) g := hind.algebraMap_aevalEquiv g
    rw [h1, ← aeval_chartGen, ← h2]
    rfl
  have hrc : (deh y 0).comp r = algebraMap (chartRing y) Ω := RingHom.ext hr
  have hrK : (dehK y).comp r = algebraMap (chartRing y) (fnField y) := by
    ext a
    rw [RingHom.comp_apply, coe_dehK, hr, IsScalarTower.algebraMap_apply (chartRing y) (fnField y) Ω]
    rfl
  have hev : ∀ (p : (chartRing y)[X]) (t : Ω),
      (p.map r).eval₂ (deh y 0) t = aeval t (p.map (algebraMap (chartRing y) (fnField y))) := by
    intro p t
    rw [eval₂_map, hrc, IsScalarTower.algebraMap_eq (chartRing y) (fnField y) Ω, ← eval₂_map,
      aeval_def]
  have hdehK : (algebraMap (fnField y) Ω).comp (dehK y) = deh y 0 := RingHom.ext fun _ => rfl
  set Pa := minpoly (chartRing y) θ with hPa
  have hPa_deg : (Pa.map r).natDegree = (minpoly (fnField y) θL).natDegree := by
    rw [(minpoly.monic hθA).natDegree_map, ← hθL, hPK, (minpoly.monic hθA).natDegree_map]

  have hq : ∀ i, ∃ q : (fnField y)[X], aeval θL q = gL x e i := by
    intro i
    have htop : Algebra.adjoin (fnField y) {θL} = ⊤ := by
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.of_finite _ θL).isAlgebraic, hc,
        top_toSubalgebra]
    have hm : gL x e i ∈ Algebra.adjoin (fnField y) {θL} := htop ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨q, hq⟩ := hm
    exact ⟨q, hq⟩
  choose q hq using hq
  have hqΩ : ∀ i, aeval θ (q i) = x i / x (e 0) := by
    intro i
    have : (θL : Ω) = algebraMap (Lx x e) Ω θL := rfl
    rw [hθθ, this, aeval_algebraMap_apply, hq i]
    rfl
  obtain ⟨b, Qa, hb0, hQa⟩ := exists_clear (A := chartRing y) (K := fnField y) q
  have hsep : (minpoly (fnField y) θ).Separable := (minpoly.irreducible hθK).separable
  obtain ⟨u, v, huv⟩ := hsep
  obtain ⟨b', UV, hb'0, hUV⟩ := exists_clear (A := chartRing y) (K := fnField y) ![u, v]
  have hinjA : Function.Injective (algebraMap (chartRing y) Ω) := by
    rw [IsScalarTower.algebraMap_eq (chartRing y) (fnField y) Ω]
    exact (algebraMap (fnField y) Ω).injective.comp (IsFractionRing.injective _ _)
  have hne : ∀ a : chartRing y, a ≠ 0 → deh y 0 (r a) ≠ 0 := fun a ha => by
    rw [hr]; exact (map_ne_zero_iff _ hinjA).mpr ha
  let G : Gen x e :=
    { Θ := Θ
      P := Pa.map r
      monic := (minpoly.monic hθA).map r
      root := by rw [← hθdef, hev, ← hPK]; exact minpoly.aeval _ _
      min := by
        intro H hH h0 j
        have hm : H.map (dehK y) = 0 := by
          by_contra hne'
          have h1 : aeval θ (H.map (dehK y)) = 0 := by
            rw [aeval_def, eval₂_map, hdehK, hθdef]; exact h0
          have h2 := natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (fnField y) θ hne' h1)
          have h3 := natDegree_map_le (f := dehK y) (p := H)
          rw [hθL] at h2
          rw [hPa_deg] at hH
          omega
        have := congrArg (fun p => p.coeff j) hm
        simp only [coeff_map, coeff_zero] at this
        rw [← coe_dehK, this]
        simp
      dd := r b
      dd_ne := hne b hb0
      Q := fun i => (Qa i).map r
      hQ := by
        intro i
        rw [← hθdef, hev, hQa i, map_mul, aeval_C, hqΩ i, deh_X, hr,
          IsScalarTower.algebraMap_apply (chartRing y) (fnField y) Ω]
      cc := r b'
      cc_ne := hne b' hb'0
      U := (UV 0).map r
      V := (UV 1).map r
      hUV := by
        have e1 : (UV 0).map r * Pa.map r + (UV 1).map r * derivative (Pa.map r) - C (r b') =
            (UV 0 * Pa + UV 1 * derivative Pa - C b').map r := by
          rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
            Polynomial.derivative_map, Polynomial.map_C]
        have e2 : (UV 0 * Pa + UV 1 * derivative Pa - C b').map
            (algebraMap (chartRing y) (fnField y)) = 0 := by
          rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
            ← Polynomial.derivative_map, Polynomial.map_C, hUV 0, hUV 1, ← hPK]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linear_combination (C (algebraMap (chartRing y) (fnField y) b')) * huv
        rw [e1, Polynomial.map_map, hrc, IsScalarTower.algebraMap_eq (chartRing y) (fnField y) Ω, ← Polynomial.map_map,
          e2, Polynomial.map_zero] }
  refine ⟨G, ?_, ?_, ?_⟩
  · show (Pa.map r).natDegree = _
    rw [hPa_deg, hδ]
  · intro H
    have hS : ∀ j, (dehK y (G.S j) : fnField y) =
        psumC (minpoly (fnField y) θL) (minpoly (fnField y) θL).natDegree j := by
      intro j
      show dehK y (psumC (Pa.map r) (Pa.map r).natDegree j) = _
      rw [map_psumC, Polynomial.map_map, hrK, ← hPK, hθL, hPa_deg]
    set s : Lx x e := ∑ j ∈ Finset.range (H.natDegree + 1), dehK y (H.coeff j) • θL ^ j with hsdef
    have hs : (s : Ω) = H.eval₂ (deh y 0) (deh x (e 0) G.Θ) := by
      show _ = H.eval₂ (deh y 0) (deh x (e 0) Θ)
      rw [eval₂_eq_sum_range, hθ, hsdef]
      simp [Algebra.smul_def]
    rw [← hs, fnTrace_coe, map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul, trace_pow_eq_psumC hc]
    rw [Gen.TrP, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← coe_dehK y (G.S j), hS j]
    rfl
  · intro m F
    let t : Lx x e := ⟨deh x (e 0) F, deh_mem_fnField x (e 0) F⟩
    have h1 : deh y 0 m * deh x (e 0) F = ((dehK y m • t : Lx x e) : Ω) := by
      rw [Algebra.smul_def]; rfl
    rw [h1, fnTrace_coe, show deh x (e 0) F = (t : Ω) from rfl, fnTrace_coe, LinearMap.map_smul,
      smul_eq_mul]
    push_cast
    rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
