import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEqMulCanonicalThetaOfSignMultiplier

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.KeyNormalForm

section Normal

open Complex Matrix GlobalTheory.SiegelNormalForm

theorem exists_coordinates {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hspan : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Ef : LinearMap.BilinForm ℤ Λ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) :
    ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
      τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      ∀ z w, hermForm Hm (φ z) (φ w) = hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) z w := by
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  have halt : Ef.IsAlt := fun l => by
    have h1 := congrArg Complex.im (form_conj hH (l : Fin g → ℂ) l)
    have h2 := hE l l
    simp only [Complex.star_def, Complex.conj_im] at h1
    have : (Ef l l : ℝ) = 0 := by linarith
    exact_mod_cast this
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg
    (GlobalTheory.bijective_neg_bilinForm hbij) hrank
  set e : Fin g → Λ := fun i => bs (Sum.inl i) with he
  set f : Fin g → Λ := fun i => bs (Sum.inr i) with hf
  have hee : ∀ i j, ((e i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (e j : Fin g → ℂ)).im = 0 := fun i j => by
    have := hbs.left_left i j
    simp only [LinearMap.neg_apply, neg_eq_zero] at this
    rw [← hE, this]; simp
  have hff : ∀ i j, ((f i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (f j : Fin g → ℂ)).im = 0 := fun i j => by
    have := hbs.right_right i j
    simp only [LinearMap.neg_apply, neg_eq_zero] at this
    rw [← hE, this]; simp
  have hef : ∀ i j, ((e i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (f j : Fin g → ℂ)).im =
      if i = j then -1 else 0 := fun i j => by
    have := hbs.left_right i j
    simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
    rw [← hE, this]; split_ifs <;> simp
  let P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k i => (e i : Fin g → ℂ) k
  have hP : ∀ i, P *ᵥ Pi.single i 1 = e i := fun i => by
    ext k; simp [P]
  let Y : Matrix (Fin g) (Fin g) ℝ := (Pᵀ * Hm * P.map star).map Complex.re
  have hYe : ∀ i j, (Pᵀ * Hm * P.map star) i j =
      (e i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (e j : Fin g → ℂ) := fun i j => by
    rw [← form_single (Pᵀ * Hm * P.map star), ← form_pull, hP, hP]
  have hY : Pᵀ * Hm * P.map star = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · rw [hYe, hee]; simp
  have hPu : IsUnit P := isUnit_of_lagrangian P Hm (fun j => f j) hpos Y hY
    (fun i j => by rw [hP, hef])
  have hPi : Function.Injective P.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hPu
  have hPs : Function.Surjective P.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 hPu
  let φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofBijective P.mulVecLin ⟨hPi, hPs⟩
  have hφ : ∀ z, φ z = P *ᵥ z := fun z => rfl
  let τ : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => φ.symm (f j) k
  have hτ : ∀ j, P *ᵥ (τ *ᵥ Pi.single j 1) = f j := fun j => by
    rw [← hφ, ← LinearEquiv.eq_symm_apply]
    ext k; simp [τ]
  have hform : ∀ z w, (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (P *ᵥ w) = z ⬝ᵥ Y.map (↑) *ᵥ star w :=
    fun z w => by rw [form_pull, hY]
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (form_conj hH (e i : Fin g → ℂ) (e j))
    simp only [Complex.star_def, Complex.conj_re] at this
    simp only [Y, Matrix.transpose_apply, Matrix.map_apply, hYe, this]
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : P *ᵥ (fun i => (a i : ℂ)) ≠ 0 := by
      intro h0
      have := hPi (h0.trans (Matrix.mulVec_zero P).symm)
      exact ha (funext fun i => by simpa using congrFun this i)
    have := hpos _ hne
    rw [hform] at this
    simpa [Matrix.mulVec, dotProduct] using this
  obtain ⟨hτs, hτp, hYτ⟩ := siegel_of_relations Y hYp τ
    (fun i j => by rw [← hform, hP, hτ, hef]) (fun i j => by rw [← hform, hτ, hτ, hff])
  have hcomb : ∀ m n : Fin g → ℤ, φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) =
      ((∑ i, m i • e i + ∑ i, n i • f i : Λ) : Fin g → ℂ) := fun m n => by
    have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [h1 m, h1 n, hφ]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hP, hτ]
    simp
  refine ⟨φ, τ, hτs, hτp, fun z => ⟨fun hz => ?_, ?_⟩, fun z w => ?_⟩
  · refine ⟨fun i => bs.repr ⟨_, hz⟩ (Sum.inl i), fun i => bs.repr ⟨_, hz⟩ (Sum.inr i),
      φ.injective ?_⟩
    rw [hcomb]
    have := bs.sum_repr ⟨_, hz⟩
    rw [Fintype.sum_sum_type] at this
    rw [this]
  · rintro ⟨m, n, rfl⟩
    rw [hcomb]
    exact Subtype.coe_prop _
  · rw [Matrix.inv_eq_left_inv hYτ]
    exact hform z w

end Normal

section Change

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  (φ : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (Q : (Fin g → ℂ) → ℂ) (hQ : Differentiable ℂ Q)

def change : HolUnif A L g where
  ex z := u.ex (φ z)
  ex_add z w := by rw [map_add, u.ex_add]
  ex_onto := u.ex_onto.comp φ.surjective
  Λ := u.Λ.comap (φ.toLinearEquiv.toLinearMap.restrictScalars ℤ)
  ker z := u.ker _
  discrete := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (β := u.Λ)
      (f := fun l => ⟨φ l, l.2⟩) ((φ.continuous.comp continuous_subtype_val).subtype_mk _) ?_
    intro a b h
    exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  full := by
    have h : ((u.Λ.comap (φ.toLinearEquiv.toLinearMap.restrictScalars ℤ) : Submodule ℤ _) : Set (Fin g → ℂ)) =
        (φ.symm.toLinearEquiv.toLinearMap.restrictScalars ℝ) '' u.Λ := by
      ext z
      exact ⟨fun hz => ⟨φ z, hz, φ.symm_apply_apply z⟩, by
        rintro ⟨w, hw, rfl⟩
        change φ (φ.symm w) ∈ u.Λ
        rwa [φ.apply_symm_apply]⟩
    rw [h, Submodule.span_image, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.symm.surjective
  hol U f := ⟨(u.hol U f).1.preimage φ.continuous,
    (u.hol U f).2.comp φ.differentiable.differentiableOn fun _ hz => hz⟩
  fr i z := Complex.exp (Q z) * u.fr i (φ z)
  fr_hol i := hQ.cexp.differentiableOn.mul
    ((u.fr_hol i).comp φ.differentiable.differentiableOn fun _ hz => hz)
  fr_ne i z hz := mul_ne_zero (Complex.exp_ne_zero _) (u.fr_ne i _ hz)
  fr_compat i j z hz := by rw [u.fr_compat i j _ hz]; ring

theorem mem_change (z : Fin g → ℂ) : z ∈ (change u φ Q hQ).Λ ↔ φ z ∈ u.Λ := Iff.rfl

theorem isRig_change (h0 : Q 0 = 0) {rig : LB.Gen (L.pull (eSec A))} (h : u.IsRig rig) :
    (change u φ Q hQ).IsRig rig := fun j hj => by
  rw [← h j hj]
  simp [change, h0]

theorem isFn_change {s : L.Sec} {θ θ' : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ)
    (hθ : ∀ z, θ (φ z) = θ' z * Complex.exp (Q z)) : (change u φ Q hQ).IsFn s θ' := fun i z hz => by
  refine (h i (φ z) hz).trans ?_
  rw [hθ, _root_.mul_assoc]
  rfl

theorem isDiff_change {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (h : u.IsDiff (φ w) v) :
    (change u φ Q hQ).IsDiff w v := fun U hU f => by
  refine (h U hU f).trans ?_
  have := φ.comp_right_fderiv (f := fun z => valAt' (u.ex z).left U f) (x := 0)
  rw [map_zero] at this
  exact (congrArg (fun k => k w) this).symm

end Change

section Constants

open Complex Matrix

variable {g : ℕ}

theorem weight_eq {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) (p q : Fin g → ℝ) (c t : ℂ)
    {z : Fin g → ℂ} (hz : z = (fun i => (p i : ℂ)) + τ.mulVec (fun i => (q i : ℂ))) :
    ‖c * (cexp (Real.pi / 2 * (z ⬝ᵥ (CanTh.imInv τ).mulVec z)) * t)‖ ^ 2 *
        Real.exp (-Real.pi * (hermForm (CanTh.imInv τ) z z).re) =
      ‖c‖ ^ 2 * (‖t‖ ^ 2 * Real.exp (-2 * Real.pi * (q ⬝ᵥ (τ.map Complex.im).mulVec q))) := by
  have h1 := CanTh.dot_imInv_eq_hermForm_add hp q p z
  rw [← hz] at h1
  have h2 : (z ⬝ᵥ fun i => (q i : ℂ)).im = q ⬝ᵥ (τ.map Complex.im).mulVec q := by
    rw [hz]
    simp [dotProduct, mulVec, mul_comm]
  have h3 : ((Real.pi : ℂ) / 2 * (z ⬝ᵥ (CanTh.imInv τ).mulVec z)).re =
      Real.pi / 2 * ((hermForm (CanTh.imInv τ) z z).re - 2 * (q ⬝ᵥ (τ.map Complex.im).mulVec q)) := by
    rw [h1, ← h2, show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    simp [sub_eq_add_neg]
  rw [norm_mul, norm_mul, Complex.norm_exp, h3, mul_pow, mul_pow, ← Real.exp_nat_mul, _root_.mul_assoc,
    mul_right_comm (Real.exp _), ← Real.exp_add, mul_comm (Real.exp _)]
  congr 3
  push_cast
  ring

theorem weight_periodic {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) {k t : ℂ} (hk : ‖k‖ = 1)
    (z l : Fin g → ℂ) :
    ‖(k * cexp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ 1 * t‖ ^ 2 *
        Real.exp (-Real.pi * (hermForm Hm (z + l) (z + l)).re) =
      ‖t‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := by
  have h3 : ((Real.pi : ℂ) * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l).re =
      Real.pi * (hermForm Hm z l).re + Real.pi / 2 * (hermForm Hm l l).re := by
    rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.add_re, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
  rw [pow_one, norm_mul, norm_mul, hk, _root_.one_mul, Complex.norm_exp, h3,
    AppellHumbertTrivial.re_hermForm_add_self hH, mul_pow, ← Real.exp_nat_mul,
    mul_right_comm (Real.exp _), ← Real.exp_add, mul_comm (Real.exp _)]
  congr 2
  push_cast
  ring

theorem det_rows (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : ℂ) (M W : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i, W i = φ (s • M i)) : W.det = s ^ g * M.det * LinearMap.det φ := by
  have : W = (s • M) * (LinearMap.toMatrix' φ)ᵀ := by
    ext i j
    rw [h, ← LinearMap.toMatrix'_mulVec]
    simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_smul, Matrix.det_transpose, LinearMap.det_toMatrix', Fintype.card_fin]

theorem constant_eq (g : ℕ) {m c d y : ℝ} (hm : 0 < m) (hc : 0 < c) (hd : 0 < d) (hy : 0 < y) :
    m ^ 4 / c ^ 8 * (c ^ 2 * (Real.sqrt (2 ^ g * y))⁻¹) ^ 4 *
      (d ^ 2 * y / (Real.pi ^ g * (((2 * Real.pi)⁻¹) ^ g * m * d) ^ 2)) ^ 2 = (2 * Real.pi) ^ (2 * g) := by
  have h1 : Real.sqrt (2 ^ g * y) ^ 4 = (2 ^ g * y) ^ 2 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
  have h2 := Real.pi_pos
  rw [mul_pow (c ^ 2), inv_pow, h1, inv_pow, mul_comm 2 g, pow_mul, mul_pow 2 Real.pi g]
  generalize_proofs
  have h3 : (0 : ℝ) < 2 ^ g := by positivity
  have h4 : (0 : ℝ) < Real.pi ^ g := by positivity
  generalize (2 : ℝ) ^ g = s at *
  generalize Real.pi ^ g = t at *
  field_simp

end Constants

theorem det_ne_zero_of_basis
    (hlin : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g n : ℕ) (u : HolUnif A L g)
    (v : Fin n → (epsR ℂ ⟶ A)) (W : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A),
    (∀ i, IsTangent (v i)) → (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w)
    (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ)
    (hW : ∀ i, u.IsDiff (W i) (x.v i)) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) : W.det ≠ 0 := by
  have hs : Function.Surjective W.vecMul := fun w => by
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
    obtain ⟨c, hc, -⟩ := x.basis.2 v hv
    refine ⟨c, (h₁ v hv).unique ?_ hd⟩
    have := hlin x.P.A x.P.isAb x.P.L _ _ u x.v W c v x.basis.1 hW hc
    rwa [← Matrix.vecMul_eq_sum] at this
  exact ((Matrix.isUnit_iff_isUnit_det W).1 (Matrix.vecMul_surjective_iff_isUnit.1 hs)).ne_zero

theorem normal_form_of_parts
    (hcmp : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∀ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    (∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef) ∧
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v))
    (hlin : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g n : ℕ) (u : HolUnif A L g)
    (v : Fin n → (epsR ℂ ⟶ A)) (W : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A),
    (∀ i, IsTangent (v i)) → (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w)
    (hsec : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ), u.IsAH Hm χ → u.IsFn x.th θ → u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0)
    (hline : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (α : (Fin g → ℤ) → (Fin g → ℤ) → ℂ) (f : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → (∀ m n, α m n ^ 2 = 1) → Differentiable ℂ f → f ≠ 0 →
    (∀ (m n : Fin g → ℤ) (l z : Fin g → ℂ), l = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      f (z + l) = α m n * Complex.exp (Real.pi * hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) z l +
        Real.pi / 2 * hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) l l) * f z) →
    ∃ (a b : Fin g → ℝ) (c : ℂ), (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ c ≠ 0 ∧
      ∀ z, f z = c * (Complex.exp (Real.pi / 2 * (z ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)).mulVec z)) *
        thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) z))
    (hvol : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    (volume Fd).toReal = ‖LinearMap.det (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * (τ.map Complex.im).det)
    (havg : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    ∀ F : (Fin g → ℂ) → ℝ, (∀ (l : Λ) z, F (z + l) = F z) →
    ∫ z in Fd, F z = (volume Fd).toReal * ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
      F (φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ))))) :
    ThetaUnifAV → ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ∃ (u' : HolUnif x.P.A x.P.L x.P.g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
        τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
        (∀ z, z ∈ u'.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
        u'.IsRig x.rig ∧ c ≠ 0 ∧ u'.IsFn x.th (fun z => c * thetaChar τ a b z) ∧ M.det ≠ 0 ∧
        (∀ i, u'.IsDiff ((2 * Real.pi * Complex.I)⁻¹ • M i) (x.v i)) ∧
        ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g) := by
  intro hT x u Hm W χ θ Fd nth nη hAH hrig hfn hW hFd hnth hnη
  obtain ⟨⟨Ef, hE, hbij⟩, h₁, h₂⟩ := hcmp hT x.P x.rig x.rig_gen u Hm χ hAH
  have hWdet := det_ne_zero_of_basis hlin x u W hW h₁ h₂
  obtain ⟨⟨hθd, hθl⟩, hθ0⟩ := hsec x u Hm χ θ hAH hfn
  have := u.discrete
  obtain ⟨φ, τ, hs, hp, hΛ, hH⟩ := exists_coordinates u.Λ u.full Hm Ef hAH.1 hAH.2.1 hE hbij
  let ψ := φ.toContinuousLinearEquiv
  obtain ⟨a, b, c, ha, hb, hc, hθ⟩ := hline x.P.g τ
    (fun m n => χ ⟨φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))), (hΛ _).2 ⟨m, n, rfl⟩⟩)
    (fun z => θ (φ z)) hs hp (fun m n => semicharacter_sq_eq_one_of_symmetric x.P u Hm χ hAH _)
    (hθd.comp ψ.differentiable)
    (fun h => hθ0 (funext fun z => by simpa using congrFun h (φ.symm z)))
    (fun m n l z hl => by
      subst hl
      have := hθl ⟨_, (hΛ _).2 ⟨m, n, rfl⟩⟩ (φ z)
      rw [pow_one, hH, hH, ← map_add] at this
      exact this)
  have hQ : Differentiable ℂ fun z : Fin x.P.g → ℂ =>
      (Real.pi : ℂ) / 2 * (z ⬝ᵥ (CanTh.imInv τ).mulVec z) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := Matrix.of fun i => (2 * Real.pi * Complex.I : ℂ) • φ.symm (W i)
  have hM : ∀ i, W i = φ ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M i) := fun i => by
    change _ = φ ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • φ.symm (W i))
    rw [inv_smul_smul₀ hπ, φ.apply_symm_apply]
  have hdet := det_rows φ.toLinearMap _ M W hM
  have hMdet : M.det ≠ 0 := fun h => hWdet (by rw [hdet, h]; simp)
  have hφdet : LinearMap.det φ.toLinearMap ≠ 0 := fun h => hWdet (by rw [hdet, h]; simp)
  refine ⟨change u ψ _ hQ, τ, M, fun i => a i, fun i => b i, c, hs, hp,
    fun i => (ha i).imp (fun h => by simp [h]) (fun h => by simp [h]),
    fun i => (hb i).imp (fun h => by simp [h]) (fun h => by simp [h]), hΛ,
    isRig_change u ψ _ hQ (by simp) hrig, hc,
    isFn_change u ψ _ hQ hfn fun z => (hθ z).trans (by rw [_root_.mul_assoc, mul_comm (Complex.exp _)]; rfl),
    hMdet, fun i => isDiff_change u ψ _ hQ (by have := hW i; rwa [hM] at this), ?_⟩
  have hv := hvol _ u.Λ φ τ hp hΛ Fd hFd
  have hv0 : (volume Fd).toReal ≠ 0 := by
    rw [hv]
    exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hφdet)) hp.det_pos.ne'
  have hI := havg _ u.Λ φ τ hp hΛ Fd hFd (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re))
    (fun l z => by rw [hθl]; exact weight_periodic hAH.1 (hAH.2.2.1 l) z l)
  have hn : nth = ‖c‖ ^ 2 * (Real.sqrt (2 ^ x.P.g * (τ.map Complex.im).det))⁻¹ := by
    rw [hnth, div_eq_iff hv0, mul_comm _ (volume Fd).toReal]
    refine hI.trans ?_
    rw [← ThetaNorm.integral_norm_sq_thetaChar _ τ a b hs hp, ← integral_const_mul (‖c‖ ^ 2)]
    congr 2
    funext p
    rw [hH, hθ]
    exact weight_eq hp _ _ c _ rfl
  have hWn : ‖W.det‖ = ((2 * Real.pi)⁻¹) ^ x.P.g * ‖M.det‖ * ‖LinearMap.det φ.toLinearMap‖ := by
    rw [hdet, norm_mul, norm_mul, norm_pow, norm_inv]
    rw [show ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi by simp [abs_of_pos Real.pi_pos]]
  rw [hn, hnη, hv, hWn, norm_div, norm_pow, norm_pow]
  exact constant_eq _ (norm_pos_iff.2 hMdet) (norm_pos_iff.2 hc) (norm_pos_iff.2 hφdet) hp.det_pos

end GlobalTheory.KeyNormalForm
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace SectionFn

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem differentiable_of_isFn (hL : L.IsLB) {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) :
    Differentiable ℂ θ := by
  intro z
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hn := (u.hol (L.U i) (s.f i)).1.mem_nhds hi
  have d : DifferentiableOn ℂ (fun w => valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹)
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U i} :=
    (u.hol (L.U i) (s.f i)).2.mul ((u.fr_hol i).inv fun w hw => u.fr_ne i w hw)
  refine (d.differentiableAt hn).congr_of_eventuallyEq (Filter.mem_of_superset hn fun w hw => ?_)
  have := u.fr_ne i w hw
  change θ w = valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹
  rw [h i w hw]
  field_simp

theorem isThetaFn_of_isFn (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsThetaFn Hm χ 1 θ := by
  refine ⟨differentiable_of_isFn u hL h, fun l z => ?_⟩
  have hper : u.ex (z + l) = u.ex z := by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h i z hi
  have h2 := h i (z + l) hi'
  rw [hper, h1, hAH.2.2.2 l i z hi] at h2
  refine mul_right_cancel₀ (u.fr_ne i _ hi') ?_
  rw [← h2, pow_one]
  unfold hermForm
  ring

theorem ne_zero_of_isFn [LocallyOfFiniteType A.hom] {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ)
    {p : A.left} (hp : p ∈ Out.nonzeroLocus s) : θ ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  have hle : A.left.basicOpen (s.f i) ≤ ⊥ := by
    refine ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun y hy hyb => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk y hy)
    have hzy : (u.ex z).left = y := by rw [hz]; rfl
    subst hzy
    have hne := (top_le_preimage_basicOpen_iff _ _ _).1 hyb
    have hU := top_le_preimage_of_valAt'_ne_zero _ hne
    exact absurd (by simpa using h i z hU) hne
  exact hle hi

end SectionFn

theorem isThetaFn_and_ne_zero_of_isFn :
    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ), u.IsAH Hm χ → u.IsFn x.th θ → u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 := by
  intro x u Hm χ θ hAH h
  refine ⟨SectionFn.isThetaFn_of_isFn u x.P.isLB hAH h, ?_⟩
  obtain ⟨p, -, hp⟩ := x.th_ne (default : PrimeSpectrum ℂ)
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  exact SectionFn.ne_zero_of_isFn u h hp

end GlobalTheory
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodVol

def reImCoord (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g ⊕ Fin g → ℝ) where
  toFun z := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  invFun p := fun i => ⟨p (Sum.inl i), p (Sum.inr i)⟩
  map_add' z w := by ext (i | i) <;> simp
  map_smul' c z := by ext (i | i) <;> simp
  left_inv z := rfl
  right_inv p := by ext (i | i) <;> rfl

@[simp] theorem reImCoord_inl {g : ℕ} (z : Fin g → ℂ) (i : Fin g) : reImCoord g z (Sum.inl i) = (z i).re := rfl

@[simp] theorem reImCoord_inr {g : ℕ} (z : Fin g → ℂ) (i : Fin g) : reImCoord g z (Sum.inr i) = (z i).im := rfl

@[simp] theorem reImCoord_symm_re {g : ℕ} (p : Fin g ⊕ Fin g → ℝ) (i : Fin g) :
    ((reImCoord g).symm p i).re = p (Sum.inl i) := rfl

@[simp] theorem reImCoord_symm_im {g : ℕ} (p : Fin g ⊕ Fin g → ℝ) (i : Fin g) :
    ((reImCoord g).symm p i).im = p (Sum.inr i) := rfl

theorem volume_fundamentalDomain_reImCoord (g : ℕ) :
    volume (ZSpan.fundamentalDomain (Module.Basis.ofEquivFun (reImCoord g))) = 1 := by
  have h : ZSpan.fundamentalDomain (Module.Basis.ofEquivFun (reImCoord g)) =
      Set.pi Set.univ fun _ : Fin g =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [ZSpan.fundamentalDomain, forall_and]
    tauto
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

def periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
  ((reImCoord g).symm : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ)) ∘ₗ
    Matrix.toLin' (Matrix.fromBlocks 1 (τ.map Complex.re) 0 (τ.map Complex.im)) ∘ₗ
      ((reImCoord g).symm.symm : (Fin g → ℂ) →ₗ[ℝ] (Fin g ⊕ Fin g → ℝ))

theorem det_periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.det (periodMap τ) = (τ.map Complex.im).det := by
  rw [periodMap, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, _root_.one_mul]

theorem periodMap_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    periodMap τ z = (fun i => ((z i).re : ℂ)) + τ.mulVec (fun i => ((z i).im : ℂ)) := by
  ext i
  apply Complex.ext <;>
    simp [periodMap, Matrix.mulVec, dotProduct, Matrix.one_apply]

end GlobalTheory.PeriodVol

namespace GlobalTheory

open PeriodVol

theorem volume_fundamentalDomain_periodLattice :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    (volume Fd).toReal = ‖LinearMap.det (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * (τ.map Complex.im).det := by
  intro g Λ φ τ hτ hΛ Fd hFd
  have hpos := hτ.det_pos
  let S : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    LinearMap.equivOfDetNeZero (periodMap τ) (by rw [det_periodMap]; exact hpos.ne')
  have hS : ∀ z, S z = periodMap τ z := fun z => rfl
  let T : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := S.trans (φ.restrictScalars ℝ)
  let b₀ := Module.Basis.ofEquivFun (reImCoord g)
  have hspan : Λ = Submodule.span ℤ (Set.range (b₀.map T)) := by
    ext w
    obtain ⟨z, rfl⟩ := T.surjective w
    rw [Module.Basis.mem_span_iff_repr_mem]
    change φ (S z) ∈ Λ ↔ _
    rw [hΛ]
    simp only [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, b₀,
      Module.Basis.ofEquivFun_repr_apply]
    constructor
    · rintro ⟨m, n, h⟩
      have : z = fun i => ⟨m i, n i⟩ := S.injective (by rw [h, hS, periodMap_apply]; simp)
      subst this
      rintro (i | i)
      · exact ⟨m i, rfl⟩
      · exact ⟨n i, rfl⟩
    · intro h
      choose k hk using h
      refine ⟨fun i => k (Sum.inl i), fun i => k (Sum.inr i), ?_⟩
      have h1 : ∀ i, (z i).re = k (Sum.inl i) := fun i => (hk (Sum.inl i)).symm
      have h2 : ∀ i, (z i).im = k (Sum.inr i) := fun i => (hk (Sum.inr i)).symm
      rw [hS, periodMap_apply]
      simp [h1, h2]
  subst hspan
  have hdet : b₀.det (b₀.map T) =
      ‖LinearMap.det (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * (τ.map Complex.im).det := by
    have hT : (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) =
        (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℝ ∘ₗ periodMap τ := rfl
    have : ⇑(b₀.map T) = (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) ∘ b₀ := by
      ext1 i; simp
    rw [this, Module.Basis.det_comp, Module.Basis.det_self, _root_.mul_one, hT, LinearMap.det_comp,
      det_periodMap, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq]
  have : VAddInvariantMeasure (Submodule.span ℤ (Set.range (b₀.map T))) (Fin g → ℂ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : Fin g → ℂ) s⟩
  rw [hFd.measure_eq (ZSpan.isAddFundamentalDomain (b₀.map T) volume),
    ZSpan.measure_fundamentalDomain _ volume b₀, volume_fundamentalDomain_reImCoord, _root_.mul_one, hdet,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (by positivity)]

end GlobalTheory
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem setIntegral_periodic_eq_measure_mul_cube {E I : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
    (ν : Measure E) [ν.IsAddHaarMeasure] (T : (I → ℝ) ≃L[ℝ] E) (Λ : Submodule ℤ E)
    (hΛ : ∀ p, T p ∈ Λ ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = p i)
    (Fd : Set E) (hFd : IsAddFundamentalDomain Λ Fd ν)
    (F : E → ℝ) (hF : ∀ (l : Λ) z, F (z + l) = F z) :
    ∫ z in Fd, F z ∂ν = (ν Fd).toReal *
      ∫ p in Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1), F (T p) := by
  classical
  set b : Module.Basis I ℝ E := (Pi.basisFun ℝ I).map T.toLinearEquiv with hb
  have hrepr : ∀ p i, b.repr (T p) i = p i := by
    intro p i
    simp [hb]
  have hspan : Λ = Submodule.span ℤ (Set.range b) := by
    ext z
    obtain ⟨p, rfl⟩ := T.surjective z
    rw [hΛ, Module.Basis.mem_span_iff_repr_mem]
    simp [hrepr]
  subst hspan
  have hcell := ZSpan.isAddFundamentalDomain b ν
  have hpre : T ⁻¹' ZSpan.fundamentalDomain b
      = Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1) := by
    ext p
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hrepr, Set.mem_pi, Set.mem_univ,
      true_imp_iff]
  have hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) E ν :=
    ⟨fun c s _ => measure_preimage_add ν (c : E) s⟩
  have h1 : ∫ z in Fd, F z ∂ν = ∫ z in ZSpan.fundamentalDomain b, F z ∂ν :=
    hFd.setIntegral_eq hcell (fun l z => by
      have := hF l z
      rw [add_comm] at this
      exact this)
  have h2 : ν Fd = ν (ZSpan.fundamentalDomain b) := hFd.measure_eq hcell
  let e : (I → ℝ) ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have he : (e : (I → ℝ) → E) = T := rfl
  haveI : (Measure.map T (volume : Measure (I → ℝ))).IsAddHaarMeasure :=
    T.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • Measure.map e (volume : Measure (I → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν (Measure.map T volume)⟩
  have h3 : ν (ZSpan.fundamentalDomain b) = c := by
    rw [hc, Measure.smul_apply, e.map_apply, he, hpre, Real.volume_pi_Ico]
    simp
  rw [h1, h2, h3, hc, Measure.restrict_smul, integral_smul_nnreal_measure, setIntegral_map_equiv,
    he, hpre]
  simp [NNReal.smul_def]

theorem setIntegral_periodLattice_eq_volume_mul_cube :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    ∀ F : (Fin g → ℂ) → ℝ, (∀ (l : Λ) z, F (z + l) = F z) →
    ∫ z in Fd, F z = (volume Fd).toReal * ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
      F (φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))) := by
  intro g Λ φ τ hτ hΛ Fd hFd F hF
  let L : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun p => φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))
      map_add' := fun p q => by
        rw [← map_add]
        congr 1
        ext i
        simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c p => by
        have : ∀ v : Fin g → ℂ, c • v = (c : ℂ) • v := fun v => by ext i; simp
        rw [RingHom.id_apply, this, ← map_smul]
        congr 1
        ext i
        simp [Matrix.mulVec, dotProduct, mul_add, Finset.mul_sum, mul_left_comm] }
  have hL : ∀ p, L p = φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ))) :=
    fun _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL, LinearEquiv.map_eq_zero_iff] at hp
    have him : (τ.map Complex.im).mulVec (fun i => p (.inr i)) = 0 := by
      ext i
      have := congrArg Complex.im (congrFun hp i)
      simpa [Matrix.mulVec, dotProduct] using this
    have hr : (fun i => p (.inr i)) = 0 :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hτ.isUnit) (by rw [him, Matrix.mulVec_zero])
    have hr' : ∀ i, p (.inr i) = 0 := fun i => congrFun hr i
    ext (i | i)
    · have := congrFun hp i
      simpa [Matrix.mulVec, dotProduct, hr'] using this
    · exact hr' i
  have hdim : Module.finrank ℝ (Fin g ⊕ Fin g → ℝ) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  let T : (Fin g ⊕ Fin g → ℝ) ≃L[ℝ] (Fin g → ℂ) :=
    (L.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hT : ∀ p, T p = L p := fun _ => rfl
  refine setIntegral_periodic_eq_measure_mul_cube volume T Λ (fun p => ?_) Fd hFd F hF
  rw [hT, hL, hΛ]
  constructor
  · rintro ⟨m, n, h⟩
    have : L p = L (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) := by
      rw [hL, hL, h]
      simp
    have hp := hinj this
    rintro (i | i)
    · exact ⟨m i, by simp [hp]⟩
    · exact ⟨n i, by simp [hp]⟩
  · intro h
    choose k hk using h
    refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
    simp [← hk]

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem keyIn_normal_form_and_archimedean_constant :
    ThetaUnifAV → ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ∃ (u' : HolUnif x.P.A x.P.L x.P.g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
        τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
        (∀ z, z ∈ u'.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
        u'.IsRig x.rig ∧ c ≠ 0 ∧ u'.IsFn x.th (fun z => c * thetaChar τ a b z) ∧ M.det ≠ 0 ∧
        (∀ i, u'.IsDiff ((2 * Real.pi * Complex.I)⁻¹ • M i) (x.v i)) ∧
        ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g) :=
  KeyNormalForm.normal_form_of_parts unimodular_and_tangent_of_isAH isDiff_sum_smul_of_isLieComb
    isThetaFn_and_ne_zero_of_isFn exists_eq_mul_canonical_theta_of_sign_multiplier
    volume_fundamentalDomain_periodLattice setIntegral_periodLattice_eq_volume_mul_cube

end GlobalTheory
end
