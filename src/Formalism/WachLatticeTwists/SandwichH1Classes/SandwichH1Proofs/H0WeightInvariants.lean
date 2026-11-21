import Formalism.WachLatticeTwists.SandwichH1Classes.InvariantsOfTwistedModule
import Formalism.WachLatticeTwists.SandwichH1Classes.ComparisonMatrixIntertwinesEndomorphisms
import Formalism.WachLatticeTwists.SandwichH1Classes.PerturbationForScalarTwist
import Formalism.WachLatticeTwists.SandwichH1Classes.HypothesisWGivesUnitCongruence
import Formalism.WachLatticeTwists.SandwichH1Classes.PerturbationForEveryTwist

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

lemma mat_cancel {OC : Type} [CommRing OC] {r : ℕ} (t : OC) (ht : ∀ a : OC, t * a = 0 → a = 0)
    {A B : Matrix (Fin r) (Fin r) OC} (h : t • A = t • B) : A = B := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  have h2 : t * (A i j - B i j) = 0 := by rw [mul_sub, this, sub_self]
  exact sub_eq_zero.mp (ht _ h2)

lemma map_scalar {ℓ : ℕ} [Fact ℓ.Prime] {OC : Type} [CommRing OC] [Algebra ℤ_[ℓ] OC] {r : ℕ}
    (e : OC ≃ₐ[ℤ_[ℓ]] OC) :
    (((ℓ : OC)) • (1 : Matrix (Fin r) (Fin r) OC)).map e = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem interInv : StatInterInv := by
  intro ℓ _ G _ OC _ _ actO r S S' Y Y' hℓ hY h1 h2 g
  apply mat_cancel (ℓ : OC) hℓ
  calc (ℓ : OC) • (Y'.map (actO g) * S.Mx g)
      = Y'.map (actO g) * S.Mx g * ((ℓ : OC) • 1) := by rw [Matrix.mul_smul, Matrix.mul_one]
    _ = Y'.map (actO g) * (S.Mx g * Y) * Y' := by rw [← h1]; simp only [Matrix.mul_assoc]
    _ = (Y'.map (actO g) * Y.map (actO g)) * S'.Mx g * Y' := by rw [← hY g]; simp only [Matrix.mul_assoc]
    _ = ((ℓ : OC) • 1) * S'.Mx g * Y' := by
        rw [← map_scalar (actO g), ← h2, Matrix.map_mul]
    _ = (ℓ : OC) • (S'.Mx g * Y') := by rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]

theorem interTwist : StatInterTwist := by
  intro ℓ _ G _ OC _ _ actO r S S' Y χ i hY g
  show Y.map (actO g) * ((((χ g) ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S'.Mx g)
    = ((((χ g) ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S.Mx g) * Y
  rw [Matrix.mul_smul, Matrix.smul_mul, hY g]

theorem slOfInter : StatSLofInter := by
  intro ℓ _ G _ OC _ _ actO r S' Um Y Y' hℓ hU h1
  have cancelY : ∀ A B : Matrix (Fin r) (Fin r) OC, A * Y = B * Y → A = B := by
    intro A B h
    apply mat_cancel (ℓ : OC) hℓ
    have : A * Y * Y' = B * Y * Y' := by rw [h]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_one] at this
    exact this
  constructor
  · apply cancelY
    rw [← hU 1, S'.one, Matrix.mul_one, Matrix.one_mul]
    ext i j
    simp
  · intro g h
    apply cancelY
    rw [← hU (g * h), S'.mul, Matrix.mul_assoc, ← hU g, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.map_mul, ← hU h, Matrix.map_mul]
    congr 2
    ext i j
    simp [map_mul]

theorem sandwich_composite_on_H1 : SandwichCompositeOnH1 := by
  intro ℓ _ G G' _ _ _ OC _ _ _ _ _ actO r S S' Y Y' h h' p hYY x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  show Submodule.mkQ _ _ = (ℓ : ℤ_[ℓ]) • Submodule.mkQ _ c
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  funext g
  show (c.1 g ᵥ* Y') ᵥ* Y = (ℓ : ℤ_[ℓ]) • c.1 g
  rw [Matrix.vecMul_vecMul, hYY, Matrix.vecMul_smul, Matrix.vecMul_one]
  funext k
  simp [Algebra.smul_def]

lemma matAct_apply {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {r : ℕ}
    (V : Matrix (Fin r) (Fin r) R) (g0 : X →ₗ[R] X) (v : Fin r → X) :
    matAct V g0 v = fun k => ∑ t, V k t • g0 (v t) := by
  funext k
  simp [matAct, LinearMap.pi_apply, LinearMap.sum_apply]

lemma zpow_sub_one_dvd {ℓ : ℕ} [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (i : ℤ) :
    (w : ℤ_[ℓ]) - 1 ∣ ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
  have hn : ∀ n : ℕ, (w : ℤ_[ℓ]) - 1 ∣ ((w ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro n
    rw [Units.val_pow_eq_pow_val]
    simpa using sub_dvd_pow_sub_pow (w : ℤ_[ℓ]) 1 n
  obtain ⟨n, rfl | rfl⟩ := i.eq_nat_or_neg
  · simpa using hn n
  · obtain ⟨q, hq⟩ := hn n
    refine ⟨-(((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * q, ?_⟩
    have e1 : ((w ^ (-(n : ℤ)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by simp
    have e2 : (((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((w ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := by
      rw [← Units.val_mul]; simp
    rw [e1]
    calc (((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1
        = -(((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((w ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by
          rw [mul_sub, neg_mul, e2]; ring
      _ = ((w : ℤ_[ℓ]) - 1) * (-(((w ^ n)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * q) := by rw [hq]; ring

theorem t3W : PerturbationForEveryTwist := by
  intro ℓ _ Tt r Vm z z' ϖ ϖ₁ w i hz hϖ hc hT2 hV hw
  have hdv : z * ϖ ∣ algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    obtain ⟨q, hq⟩ := hw.trans (zpow_sub_one_dvd w i)
    have : algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1
        = algebraMap ℤ_[ℓ] Tt.Om (((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by simp
    rw [this, hq, map_mul, map_pow, sq, ← hz]
    nth_rewrite 2 [hz]
    rw [← hϖ]
    exact ⟨z' * ϖ₁ * algebraMap ℤ_[ℓ] Tt.Om q, by ring⟩
  have hVt : ∀ a b, z * ϖ ∣ (Vmᵀ - 1) a b := by
    intro a b
    have := hV b a
    simpa [Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm] using this
  have hVi := twistUm Tt.Om (z * ϖ) _ r Vmᵀ hdv hVt
  obtain ⟨h1, h2⟩ := unitCongruenceGivesPerturbation_statement ℓ Tt.Om Tt.Xm ϖ z z' r (Tt.Vi Vm w i) Tt.gX hz hc hT2.1 hT2.2.1 hT2.2.2 hVi
  constructor
  · intro v hv
    apply h1 v
    rw [← matAct_apply]
    exact hv
  · intro v
    obtain ⟨y, hy⟩ := h2 v
    refine ⟨y, ?_⟩
    rw [hy, ← matAct_apply]
    rfl

theorem logClass : StatLogClass := by
  intro ℓ _ G _ _ _ M _ _ _ _ _ _ a H γ lg c w0 hlg hadd hH hgen hfix hcH hcγ σ
  obtain ⟨hcc, hcoc⟩ := c.2
  have lg1 : lg 1 = 0 := by
    have := hadd 1 1
    rw [mul_one] at this
    exact (add_eq_left.mp this.symm)
  have c1 : c.1 1 = 0 := by
    have := hcoc 1 1
    rw [mul_one, map_one] at this
    exact (add_eq_left.mp this.symm)
  let S : Subgroup G :=
    { carrier := {σ | lg γ • c.1 σ = lg σ • w0}
      one_mem' := by
        show lg γ • c.1 1 = lg 1 • w0
        rw [lg1, c1, smul_zero, zero_smul]
      mul_mem' := by
        intro x y hx hy
        show lg γ • c.1 (x * y) = lg (x * y) • w0
        have hx' : lg γ • c.1 x = lg x • w0 := hx
        have hy' : lg γ • c.1 y = lg y • w0 := hy
        rw [hcoc, smul_add, hx', ← map_smul, hy', map_smul, hfix, hadd, add_smul]
      inv_mem' := by
        intro x hx
        show lg γ • c.1 x⁻¹ = lg x⁻¹ • w0
        have hx' : lg γ • c.1 x = lg x • w0 := hx
        have e1 : c.1 x⁻¹ + a x⁻¹ (c.1 x) = 0 := by rw [← hcoc, inv_mul_cancel, c1]
        have e2 : lg x⁻¹ + lg x = 0 := by rw [← hadd, inv_mul_cancel, lg1]
        have e3 : lg γ • c.1 x⁻¹ + lg x • w0 = 0 := by
          have := congrArg (fun t => lg γ • t) e1
          simp only [smul_add, smul_zero] at this
          rwa [← map_smul, hx', map_smul, hfix] at this
        have e4 : lg x⁻¹ • w0 + lg x • w0 = 0 := by rw [← add_smul, e2, zero_smul]
        exact add_right_cancel (e3.trans e4.symm) }
  have hS : S = ⊤ := by
    apply hgen S
    · exact isClosed_eq (hcc.const_smul _) (hlg.smul continuous_const)
    · intro h hh
      show lg γ • c.1 h = lg h • w0
      rw [hcH h hh, hH h hh, smul_zero, zero_smul]
    · show lg γ • c.1 γ = lg γ • w0
      rw [hcγ]
  have : σ ∈ S := hS ▸ Subgroup.mem_top σ
  exact this

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

variable {ℓ : ℕ} [Fact ℓ.Prime] (Tt : TateTr ℓ) {r : ℕ}

lemma Vi_apply (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (j : ℤ) (t q : Fin r) :
    Tt.Vi Vm w j t q = algebraMap ℤ_[ℓ] Tt.Om ((w ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * Vm q t := rfl

lemma gXI_coe (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (j : ℤ) (v : Fin r → Tt.Xm) (t : Fin r) :
    ((Tt.gXI Vm w j v t : Tt.Xm) : Tt.Oi) = ∑ q, Tt.Vi Vm w j t q • Tt.g0 (v q : Tt.Oi) := by
  show ((matAct (Tt.Vi Vm w j) Tt.gX v t : Tt.Xm) : Tt.Oi) = _
  rw [matAct_apply]
  simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul]
  rfl

lemma gmI_apply (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (j : ℤ) (v : Fin r → Tt.Om) :
    Tt.gmI Vm w j v = fun t => ∑ q, Tt.Vi Vm w j t q * v q := by
  show matAct (Tt.Vi Vm w j) LinearMap.id v = _
  rw [matAct_apply]
  rfl

lemma gmI_smul (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (j : ℤ) (a : Tt.Om) (v : Fin r → Tt.Om) :
    Tt.gmI Vm w j (a • v) = a • Tt.gmI Vm w j v :=
  (matAct (Tt.Vi Vm w j) LinearMap.id).map_smul a v

lemma pr_zsmul (c : ℤ_[ℓ]) (y : Tt.Oi) : Tt.pr (c • y) = c • Tt.pr y := by
  rw [← algebraMap_smul Tt.Om c y, map_smul, algebraMap_smul]

lemma ht_kill {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V] (f : V →ₗ[ℤ_[ℓ]] V) (w : ℤ_[ℓ]ˣ)
    (U : Finset ℤ) (i u : ℤ) (hu : u ∈ U) (x : V) (hx : f x = ((w ^ (i - u) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x) :
    aeval f (HTpoly ℓ w U i) x = 0 := by
  unfold HTpoly
  rw [← Finset.prod_erase_mul U _ hu, map_mul, Module.End.mul_apply]
  have : aeval f (X - C (((w ^ (i - u) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) x = 0 := by
    rw [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, hx, sub_self]
  rw [this, map_zero]

theorem htW : StatHTW := by
  intro ℓ _ Tt r Vm w U htf ⟨N, B, B', u, hu, _, hB'B, hrel⟩ hinj i
  set al := algebraMap Tt.Om Tt.Oi with hal
  let Bm : Matrix (Fin r) (Fin r) Tt.Om := fun k t => Tt.pr (B k t)
  let Bm' : Matrix (Fin r) (Fin r) Tt.Om := fun k t => Tt.pr (B' k t)

  have R2 : ∀ k t, ∑ q, Vm q t * Bm k q = ((w ^ (-(u k)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • Bm k t := by
    intro k t
    have := congrArg Tt.pr (hrel k t)
    rw [map_sum, pr_zsmul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm (Tt.g0 (B k q)), ← Algebra.smul_def, map_smul, Tt.pr_comp_g_zero, smul_eq_mul]

  have hB : ∀ k t, B k t = al (Bm k t) := by
    intro k
    let v : Fin r → Tt.Xm := fun t => ⟨B k t - al (Bm k t), by
      show Tt.pr (B k t - al (Bm k t)) = 0
      rw [map_sub, Tt.pr_alg, sub_self]⟩
    have hv : Tt.gXI Vm w (u k) v = v := by
      funext t
      apply Subtype.ext
      rw [gXI_coe]
      show ∑ q, Tt.Vi Vm w (u k) t q • Tt.g0 (B k q - al (Bm k q)) = B k t - al (Bm k t)
      have e1 : ∀ q, Tt.Vi Vm w (u k) t q • Tt.g0 (B k q - al (Bm k q))
          = ((w ^ (u k) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (Tt.g0 (B k q) * al (Vm q t) - al (Vm q t * Bm k q)) := by
        intro q
        rw [Vi_apply, map_sub, AlgHom.commutes, Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_mul]
        ring
      rw [Finset.sum_congr rfl fun q _ => e1 q, ← Finset.smul_sum, Finset.sum_sub_distrib, hrel k t,
        ← map_sum, R2 k t]
      have e2 : al (((w ^ (-(u k)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • Bm k t)
          = ((w ^ (-(u k)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • al (Bm k t) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
      rw [e2, ← smul_sub, smul_smul, ← Units.val_mul, ← _root_.zpow_add]
      simp
    have h0 := hinj (u k) (hu k) v hv
    intro t
    have := congrArg (fun z : Tt.Xm => (z : Tt.Oi)) (congrFun h0 t)
    exact sub_eq_zero.mp this

  have h1 : Bm' * Bm = ((ℓ : Tt.Om) ^ N) • (1 : Matrix (Fin r) (Fin r) Tt.Om) := by
    ext k t
    have := congrArg Tt.pr (congrFun (congrFun hB'B k) t)
    rw [Matrix.mul_apply, map_sum] at this
    rw [Matrix.mul_apply]
    have e3 : ∀ q, Tt.pr (B' k q * B q t) = Bm' k q * Bm q t := by
      intro q
      rw [hB q t, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl fun q _ => e3 q] at this
    rw [this]
    have e4 : (((ℓ : Tt.Oi) ^ N) • (1 : Matrix (Fin r) (Fin r) Tt.Oi)) k t
        = al ((((ℓ : Tt.Om) ^ N) • (1 : Matrix (Fin r) (Fin r) Tt.Om)) k t) := by
      by_cases h : k = t <;> simp [Matrix.one_apply, h, hal]
    rw [e4, Tt.pr_alg]

  have heig : ∀ k, Tt.gmI Vm w i (Bm k) = ((w ^ (i - u k) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • Bm k := by
    intro k
    rw [gmI_apply]
    funext t
    have e5 : ∀ q, Tt.Vi Vm w i t q * Bm k q
        = algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (Vm q t * Bm k q) := by
      intro q
      rw [Vi_apply, mul_assoc]
    rw [Finset.sum_congr rfl fun q _ => e5 q, ← Finset.mul_sum, R2 k t, ← Algebra.smul_def, smul_smul,
      ← Units.val_mul, ← _root_.zpow_add, Pi.smul_apply, sub_eq_add_neg]

  apply LinearMap.ext
  intro v
  set P := aeval (Tt.gmI Vm w i) (HTpoly ℓ w U i) with hP
  have hdec : ((ℓ : ℤ_[ℓ]) ^ N) • v = ∑ k, (v ᵥ* Bm') k • Bm k := by
    rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, h1, Matrix.vecMul_smul, Matrix.vecMul_one]
    funext t
    simp [Algebra.smul_def]
  have hz : ((ℓ : ℤ_[ℓ]) ^ N) • P v = 0 := by
    rw [← map_smul, hdec, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    apply ht_kill _ w U i (u k) (hu k)
    rw [gmI_smul, heig k, smul_comm]
  have tf : ∀ (n : ℕ) (y : Fin r → Tt.Om), ((ℓ : ℤ_[ℓ]) ^ n) • y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      apply ih
      rw [pow_succ', mul_smul] at hy
      funext t
      exact htf _ (congrFun hy t)
  exact tf N _ hz

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

section

variable {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) {r : ℕ}

def hat (M : Matrix (Fin r) (Fin r) R.As) : Matrix (Fin r) (Fin r) R.WC := (M.map R.jA).map R.ι

lemma hat_mul (M M' : Matrix (Fin r) (Fin r) R.As) : hat R (M * M') = hat R M * hat R M' := by
  unfold hat
  rw [Matrix.map_mul, Matrix.map_mul]

lemma hat_one : hat R (1 : Matrix (Fin r) (Fin r) R.As) = 1 := by
  unfold hat
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

lemma hat_inj {M0 h0 : ℕ} (F : R.Facts r M0 h0) {M M' : Matrix (Fin r) (Fin r) R.As}
    (h : hat R M = hat R M') : M = M' := by
  ext i j
  exact F.injj (F.injι (congrFun (congrFun h i) j))

lemma map_inj_ι {M0 h0 : ℕ} (F : R.Facts r M0 h0) {M M' : Matrix (Fin r) (Fin r) R.AA}
    (h : M.map R.ι = M'.map R.ι) : M = M' := by
  ext i j
  exact F.injι (congrFun (congrFun h i) j)

end

theorem gmCocycle : StatGmCocycle := by
  intro ℓ _ R r L En M0 h0 W F
  have cancel : ∀ M M' : Matrix (Fin r) (Fin r) R.WC, M * W.Xx = M' * W.Xx → M = M' := by
    intro M M' h
    have : M * W.Xx * W.Xi = M' * W.Xx * W.Xi := by rw [h]
    rwa [Matrix.mul_assoc, Matrix.mul_assoc, W.inv1, Matrix.mul_one, Matrix.mul_one] at this
  constructor
  · apply hat_inj R F
    apply cancel
    rw [hat_one, Matrix.one_mul]
    have := W.W2 1
    rw [L.one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
    rw [show hat R (W.Gm 1) * W.Xx = ((W.Gm 1).map R.jA).map R.ι * W.Xx from rfl, ← this]
    ext i j
    simp
  · intro h
    apply hat_inj R F
    apply cancel
    have e1 : (hat R (W.Gm h)).map (R.act R.γ) = hat R ((W.Gm h).map R.σ) := by
      ext i j
      show R.act R.γ (R.ι (R.jA (W.Gm h i j))) = R.ι (R.jA (R.σ (W.Gm h i j)))
      rw [← F.eqι, F.gσ]
    have e2 : ((L.ρ h).map (algebraMap ℤ_[ℓ] R.WC)).map (R.act R.γ)
        = (L.ρ h).map (algebraMap ℤ_[ℓ] R.WC) := by
      ext i j
      exact F.actZ _ _
    have e3 : W.Xx.map (R.act (R.γ * h)) = (W.Xx.map (R.act h)).map (R.act R.γ) := by
      ext i j
      simp [map_mul]
    calc hat R (W.Gm (R.γ * h)) * W.Xx
        = W.Xx.map (R.act (R.γ * h)) * ((L.ρ (R.γ * h)).map (algebraMap ℤ_[ℓ] R.WC)) := (W.W2 _).symm
      _ = (W.Xx.map (R.act h) * (L.ρ h).map (algebraMap ℤ_[ℓ] R.WC)).map (R.act R.γ)
            * (L.ρ R.γ).map (algebraMap ℤ_[ℓ] R.WC) := by
          rw [L.mul, Matrix.map_mul, Matrix.map_mul, e2, e3, Matrix.mul_assoc]
      _ = (hat R (W.Gm h)).map (R.act R.γ) * (W.Xx.map (R.act R.γ)
            * (L.ρ R.γ).map (algebraMap ℤ_[ℓ] R.WC)) := by
          rw [W.W2 h, Matrix.map_mul, Matrix.mul_assoc]
          rfl
      _ = hat R ((W.Gm h).map R.σ * W.Gm R.γ) * W.Xx := by
          rw [W.W2 R.γ, e1, hat_mul, Matrix.mul_assoc]
          rfl

theorem gmIter : StatGmIter := by
  intro ℓ _ R r L En M0 h0 W F k i
  obtain ⟨g1, gmul⟩ := gmCocycle ℓ R r L En M0 h0 W F
  induction k with
  | zero =>
    rw [pow_zero, g1, Function.iterate_zero, id]
    funext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  | succ k ih =>
    rw [pow_succ', gmul, Function.iterate_succ_apply', ← ih, Matrix.mul_apply_eq_vecMul]
    rfl

theorem w3Vm : HypothesisWGivesUnitCongruence := by
  intro ℓ _ R r L En M0 h0 W F a b
  have hℓ : ℓ.Prime := Fact.out
  have hz : R.z ∣ (ℓ : R.Tt.Om) := ⟨R.z', by rw [F.zz]; simp⟩
  have hϖ : R.ϖ ∣ (ℓ : R.Tt.Om) := ⟨R.ϖ₁, by rw [F.ϖϖ]; simp⟩
  have := w3Um ℓ hℓ R.As R.Tt.Om R.σ R.πs R.ϑs R.z R.ϖ R.ϖ' r R.s (n0 ℓ (M0 + h0)) (W.Gm R.γ)
    F.σ1 F.σ2 (W.W3 R.γ) F.ϑπ F.dv' hz hϖ F.dvd a b
  rw [← gmIter ℓ R r L En M0 h0 W F, ← F.pg] at this
  have e : (VmW R L W - 1) a b
      = R.ϑs (W.Gm (R.p R.gg) a b - (1 : Matrix (Fin r) (Fin r) R.As) a b) := by
    rw [map_sub, Matrix.sub_apply]
    congr 1
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  rw [e]
  exact this

theorem wInter : StatWInter := by
  intro ℓ _ R r L En M0 h0 W A F hA g
  have key : A.map (R.actA g) * (L.ρ g).map (algebraMap ℤ_[ℓ] R.AA)
      = ((R.cx g) ^ M0 • W.Gm g).map R.jA * A := by
    apply map_inj_ι R F
    have e1 : (A.map (R.actA g)).map R.ι = (A.map R.ι).map (R.act g) := by
      ext i j
      exact F.eqι g _
    have e2 : ((L.ρ g).map (algebraMap ℤ_[ℓ] R.AA)).map R.ι = (L.ρ g).map (algebraMap ℤ_[ℓ] R.WC) := by
      ext i j
      exact F.algι _
    have e3 : ((R.ι (R.jA R.x)) ^ M0 • W.Xx).map (R.act g)
        = (R.ι (R.jA (R.cx g)) * R.ι (R.jA R.x)) ^ M0 • W.Xx.map (R.act g) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
      rw [← F.eqι, F.gx, map_mul]
    have e4 : (((R.cx g) ^ M0 • W.Gm g).map R.jA).map R.ι
        = (R.ι (R.jA (R.cx g))) ^ M0 • ((W.Gm g).map R.jA).map R.ι := by
      ext i j
      simp
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, hA, e3, e4, Matrix.smul_mul, W.W2 g, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_pow]
  have := congrArg (fun M => M.map R.ϑ) key
  simp only [Matrix.map_mul] at this
  have f1 : (A.map (R.actA g)).map R.ϑ = (A.map R.ϑ).map (R.actO g) := by
    ext i j
    exact F.eqϑ g _
  have f2 : ((L.ρ g).map (algebraMap ℤ_[ℓ] R.AA)).map R.ϑ = (L.sl R.actO).Mx g := by
    ext i j
    exact F.algϑ _
  rw [f1, f2] at this
  exact this

theorem umVm : StatUmVm := by
  intro ℓ _ R r L En M0 h0 W F
  have hℓ : ℓ.Prime := Fact.out
  set X := R.ϑ (R.jA R.x) with hX
  have hN : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos hℓ.pos _) (Nat.sub_pos_of_lt hℓ.one_lt)
  have nzd : ∀ a : R.OC, X * a = 0 → a = 0 := by
    intro a ha
    apply F.lnzd
    obtain ⟨N, hN'⟩ := Nat.exists_eq_add_of_le hN
    rw [← F.thx, hN', add_comm, pow_succ]
    calc X ^ N * X * R.c * a = X ^ N * R.c * (X * a) := by ring
      _ = 0 := by rw [ha, mul_zero]
  have hc : R.ϑ (R.jA (R.cx (R.p R.gg))) = 1 := by
    have h1 := congrArg R.ϑ (F.gx (R.p R.gg))
    rw [F.eqϑ, F.fixx, map_mul] at h1
    have : X * (R.ϑ (R.jA (R.cx (R.p R.gg))) - 1) = 0 := by
      rw [mul_sub, mul_one, mul_comm, ← h1, sub_self]
    exact sub_eq_zero.mp (nzd _ this)
  ext a b
  show R.ϑ (R.jA ((R.cx (R.p R.gg)) ^ M0 * W.Gm (R.p R.gg) a b))
    = R.emb (algebraMap R.Tt.Om R.Tt.Oi (R.ϑs (W.Gm (R.p R.gg) a b)))
  rw [F.embϑ, map_mul, map_mul, map_pow, map_pow, hc, one_pow, one_mul]

lemma ofFun_Mx {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] {OC : Type} [CommRing OC] [Algebra ℤ_[ℓ] OC]
    (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) {r : ℕ} (Um : G → Matrix (Fin r) (Fin r) OC)
    (h : Um 1 = 1 ∧ ∀ g h, Um (g * h) = (Um h).map (actO g) * Um g) : (SL.ofFun actO Um).Mx = Um := by
  unfold SL.ofFun
  rw [dif_pos h]

lemma matrix_map_H1_eq_onH1 {ℓ : ℕ} [Fact ℓ.Prime] {G G' : Type} [Group G] [Group G'] [TopologicalSpace G'] {OC : Type}
    [CommRing OC] [Algebra ℤ_[ℓ] OC] [TopologicalSpace OC] [IsTopologicalRing OC]
    [ContinuousConstSMul ℤ_[ℓ] OC] {actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)} {r : ℕ} (S S' : SL actO r)
    (Y : Matrix (Fin r) (Fin r) OC) (p : G' →* G) (h : Inter S S' Y) :
    matrixMapOnH1 S S' Y p = (h.eqMap.comap p).onH := by
  unfold matrixMapOnH1
  rw [dif_pos h]

lemma w_facts {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) {r M0 h0 : ℕ} (F : R.Facts r M0 h0) :
    PadicInt.valuation ((R.w : ℤ_[ℓ]) - 1) = mOf ℓ R.s (M0 + h0) ∧ 1 ≤ mOf ℓ R.s (M0 + h0) ∧
      2 ≤ mOf ℓ R.s (M0 + h0) ∧ (ℓ : ℤ_[ℓ]) ^ 2 ∣ (R.w : ℤ_[ℓ]) - 1 := by
  obtain ⟨h1, h2, h3, _⟩ := genM ℓ (R.χ R.γ) R.s (M0 + h0) F.s1 F.s2 F.valγ
  have hw : R.w = (R.χ R.γ) ^ (ℓ ^ (R.s + n0 ℓ (M0 + h0) + 1)) := by
    unfold Setup.w
    rw [F.pg, map_pow]
  rw [← hw] at h1
  refine ⟨h1, h2, h3, ?_⟩
  by_cases h0' : (R.w : ℤ_[ℓ]) - 1 = 0
  · rw [h0']; exact dvd_zero _
  · rw [← Ideal.mem_span_singleton, PadicInt.mem_span_pow_iff_le_valuation _ h0', h1]
    exact h3

theorem pieceWThm : StatPieceW := by
  intro ℓ _ R r L En M0 h0 W U A Y' F hX hA hY1 hY2 hHT i infm infX hInf hT4
  obtain ⟨hv, hm1, hm2, hw2⟩ := w_facts R F
  have hI := wInter ℓ R r L En M0 h0 W A F hA
  have hcoc := slOfInter ℓ R.Gg R.OC R.actO r (L.sl R.actO) (UmW R L W) (A.map R.ϑ) Y' F.lnzd hI hY1
  have hMx := ofFun_Mx R.actO (UmW R L W) hcoc
  have hDT : Inter (SL.ofFun R.actO (UmW R L W)) (L.sl R.actO) (A.map R.ϑ) := by
    intro g
    rw [hMx]
    exact hI g
  have hTD := interInv ℓ R.Gg R.OC R.actO r _ _ _ Y' F.lnzd hDT hY1 hY2
  have hDTi := interTwist ℓ R.Gg R.OC R.actO r _ _ _ R.χ i hDT
  have hTDi := interTwist ℓ R.Gg R.OC R.actO r _ _ _ R.χ i hTD
  have hVm := w3Vm ℓ R r L En M0 h0 W F
  have hT3 : ∀ j : ℤ, _ := fun j => t3W ℓ R.Tt r (VmW R L W) R.z R.z' R.ϖ R.ϖ₁ R.w j F.zz F.ϖϖ hX.1 hX.2
    hVm hw2
  refine ⟨?_, hInf, hT4, hT3 i, ?_, ?_⟩
  · intro x
    show matrixMapOnH1 _ _ (A.map R.ϑ) R.p (matrixMapOnH1 _ _ Y' R.p x) = _
    rw [matrix_map_H1_eq_onH1 _ _ _ _ hDTi, matrix_map_H1_eq_onH1 _ _ _ _ hTDi]
    exact sandwich_composite_on_H1 ℓ R.Gg R.G R.OC R.actO r _ _ _ _ hDTi hTDi R.p hY2 x
  · intro x hx
    funext k
    exact F.omtf _ (congrFun hx k)
  · exact htW ℓ R.Tt r (VmW R L W) R.w U F.omtf hHT (fun u _ => (hT3 u).1) i

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

theorem betaAB : StatBetaAB := by
  intro ℓ hℓ s e hs
  by_cases he : e = 0
  · subst he
    simp only [bR, aR, beta, if_true, Nat.factorial_zero, padicValNat.one, mul_zero, add_zero]
    omega
  · have h1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
    rw [← betaCount ℓ hℓ s e h1]
    simp only [bR, aR, if_neg he]
    obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le hs
    push_cast
    simp only [Nat.add_sub_cancel_left]
    ring

lemma tf_pow' {ℓ : ℕ} [Fact ℓ.Prime] {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V]
    (h : ∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) (n : ℕ) (x : V) (hx : ((ℓ : ℤ_[ℓ]) ^ n) • x = 0) : x = 0 := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    apply ih
    rw [pow_succ', mul_smul] at hx
    exact h _ hx

theorem recip : StatRecip := by
  intro ℓ _ D s e Os _ _ cupL hs htf hLa hV x k n hx hn
  have hℓ : ℓ.Prime := Fact.out
  rw [hLa] at hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨z, hz⟩ := hV y
  refine ⟨z, ?_⟩
  have hab := betaAB ℓ hℓ s e hs
  have hnat : aR ℓ s e + n = bR ℓ s e + k := by omega
  have : ((ℓ : ℤ_[ℓ]) ^ aR ℓ s e) • (((ℓ : ℤ_[ℓ]) ^ n) • x - D.ex (D.jW z)) = 0 := by
    rw [smul_sub, hz, hy, smul_smul, smul_smul, ← pow_add, ← pow_add, hnat, sub_self]
  exact sub_eq_zero.mp (tf_pow' htf _ _ this)

theorem kerExp : StatKerExp := by
  intro F _ HV Tg _ _ _ _ _ _ ex Hf δ S c hc hS hval hdim ⟨Lu, hLf, hLk, hLd⟩ z hz
  have hsurj : LinearMap.range ex = ⊤ := by
    rw [eq_top_iff, ← hS, Submodule.span_le]
    intro y hy
    obtain ⟨z, hz⟩ := hval y hy
    refine ⟨c⁻¹ • z, ?_⟩
    rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hrn := LinearMap.finrank_range_add_finrank_ker ex
  rw [hsurj, finrank_top, hdim] at hrn
  have hk : Module.finrank F (LinearMap.ker ex) = δ := by omega
  have : Lu = LinearMap.ker ex := Submodule.eq_of_le_of_finrank_eq hLk (by rw [hLd, hk])
  exact hLf (this ▸ (LinearMap.mem_ker.mpr hz))

theorem class_of_w_zero_in_H1 : ClassOfWZeroInH1 := by
  intro ℓ _ G _ _ _ M _ _ _ _ _ _ MB _ _ _ _ _ a aB F H γ lg ε s N La c hlg hadd hH hgen hγ hfix hcH hLa
  have key := logClass ℓ G M a H γ lg c (c.1 γ) hlg hadd hH hgen hfix hcH rfl
  set y : MB := ((ε⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (((ℓ : ℤ_[ℓ]) ^ N) • F.f (c.1 γ)) with hy
  have hyfix : ∀ g, aB g y = y := by
    intro g
    rw [hy, map_smul, map_smul, ← F.eqv, hfix]
  let c' : Z1 aB := ⟨fun σ => lg σ • y, hlg.smul continuous_const, fun g h => by
    show lg (g * h) • y = lg g • y + aB g (lg h • y)
    rw [map_smul, hyfix, hadd, add_smul]⟩
  refine ⟨y, La.smul_mem _ hLa, c', fun σ => rfl, ?_⟩
  show ((ℓ : ℤ_[ℓ]) ^ (s + N)) • Submodule.mkQ _ (F.onZ c) = Submodule.mkQ _ c'
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  funext σ
  show ((ℓ : ℤ_[ℓ]) ^ (s + N)) • F.f (c.1 σ) = lg σ • y
  have e1 : ((ε⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (ε : ℤ_[ℓ]) = 1 := by rw [← Units.val_mul]; simp
  have e2 : ((ℓ : ℤ_[ℓ]) ^ s) • c.1 σ = (((ε⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * lg σ) • c.1 γ := by
    rw [mul_smul, ← key σ, hγ, smul_smul, ← mul_assoc, e1, one_mul]
  rw [hy, pow_add, mul_comm, mul_smul, ← map_smul F.f, e2, map_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

theorem pieceBThm : StatPieceB := by
  intro ℓ _ R r r₀ M0 h0 S Um Vm U Y Y' F hX hI hY1 hY2 hVm hHT i infm infX hInf hT4
  obtain ⟨hv, hm1, hm2, hw2⟩ := w_facts R F
  have hcoc := slOfInter ℓ R.Gg R.OC R.actO r S Um Y Y' F.lnzd hI hY1
  have hMx := ofFun_Mx R.actO Um hcoc
  have hDT : Inter (SL.ofFun R.actO Um) S Y := by
    intro g
    rw [hMx]
    exact hI g
  have hTD := interInv ℓ R.Gg R.OC R.actO r _ _ _ Y' F.lnzd hDT hY1 hY2
  have hDTi := interTwist ℓ R.Gg R.OC R.actO r _ _ _ R.χ i hDT
  have hTDi := interTwist ℓ R.Gg R.OC R.actO r _ _ _ R.χ i hTD
  have hT3 : ∀ j : ℤ, _ := fun j => t3W ℓ R.Tt r Vm R.z R.z' R.ϖ R.ϖ₁ R.w j F.zz F.ϖϖ hX.1 hX.2
    hVm hw2
  refine ⟨?_, hInf, hT4, hT3 i, ?_, ?_⟩
  · intro x
    show matrixMapOnH1 _ _ Y R.p (matrixMapOnH1 _ _ Y' R.p x) = _
    rw [matrix_map_H1_eq_onH1 _ _ _ _ hDTi, matrix_map_H1_eq_onH1 _ _ _ _ hTDi]
    exact sandwich_composite_on_H1 ℓ R.Gg R.G R.OC R.actO r _ _ _ _ hDTi hTDi R.p hY2 x
  · intro x hx
    funext k
    exact F.omtf _ (congrFun hx k)
  · exact htW ℓ R.Tt r Vm R.w U F.omtf hHT (fun u _ => (hT3 u).1) i

theorem square : StatSquare := by
  intro OC _ r c A B hc h
  have hpow : ∀ (n : ℕ) (a : OC), c ^ n * a = 0 → a = 0 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih =>
      intro a ha
      apply ih
      apply hc
      rw [← mul_assoc, ← pow_succ']
      exact ha
  have h0 : A * (B * A - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, sub_self]
  have h1 : A.det • (B * A - c • 1) = 0 := by
    have := congrArg (fun M => A.adjugate * M) h0
    simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_zero] at this
    exact this
  have hdet : A.det * B.det = c ^ r := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hz : B * A - c • 1 = 0 := by
    ext i j
    have e := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e
    apply hpow r
    rw [← hdet, mul_comm A.det, mul_assoc, e, mul_zero]
  exact sub_eq_zero.mp hz

theorem sec3 : StatSec3 := by
  intro ℓ _ G _ OC Om _ _ _ eO actO r ρ S Sτ Um Vm Y Y' Pp Sp Cm Bm t hℓ hinj hI hY2 hP hS hB hV
  set Cq := Cm.map eO with hCq
  set Bq := Bm.map eO with hBq
  set Z := Y * Pp with hZ
  have h1 : (Sp * Y' * Bq) * (Cq * Z) = (ℓ : OC) • (1 : Matrix (Fin ρ) (Fin ρ) OC) := by
    rw [Matrix.mul_assoc, ← hB, hZ, Matrix.mul_assoc, ← Matrix.mul_assoc Y', hY2, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, hS]
  have h2 := square OC ρ (ℓ : OC) _ _ hℓ h1
  have hCB : Cm * Bm = 1 := by
    have e1 : (Cq * Bq) * (Cq * Z) = Cq * Z := by rw [Matrix.mul_assoc, ← hB]
    have e2 : (ℓ : OC) • (Cq * Bq) = (ℓ : OC) • (1 : Matrix (Fin ρ) (Fin ρ) OC) := by
      have := congrArg (fun M => M * (Sp * Y' * Bq)) e1
      simp only [Matrix.mul_assoc (Cq * Bq), h2, Matrix.mul_smul, Matrix.mul_one] at this
      exact this
    have e3 := mat_cancel (ℓ : OC) hℓ e2
    ext a b
    apply hinj
    have := congrFun (congrFun e3 a) b
    rw [hCq, hBq, ← Matrix.map_mul] at this
    rw [show eO ((Cm * Bm) a b) = ((Cm * Bm).map eO) a b from rfl, this]
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  refine ⟨h1, h2, ?_, hCB, ?_⟩
  · intro g
    rw [Matrix.map_mul, hZ, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_assoc, hP g,
      ← Matrix.mul_assoc (Y.map _), hI g, Matrix.mul_assoc (Um g), ← hZ]
    conv_lhs => rw [hB]
    simp only [Matrix.mul_assoc]
  · intro a b
    have : Cm * Vm * Bm - (1 : Matrix (Fin ρ) (Fin ρ) Om) = Cm * (Vm - 1) * Bm := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hCB]
    rw [this, Matrix.mul_apply]
    refine Finset.dvd_sum fun q _ => ?_
    apply Dvd.dvd.mul_right
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun q' _ => Dvd.dvd.mul_left (hV q' q) _

theorem cyclotomicInvariantsZero_statement : CyclotomicInvariantsZero := by
  intro ℓ _ R r r₀ M0 h0 S Um Vm U Y Y' F hX hI hY1 hY2 hVm hHT h0U hfix hemb hg0 hUH hUg v hv
  obtain ⟨hval, hm1, hm2, hw2⟩ := w_facts R F
  have hcoc := slOfInter ℓ R.Gg R.OC R.actO r S Um Y Y' F.lnzd hI hY1
  have hMx := ofFun_Mx R.actO Um hcoc
  have hDT : Inter (SL.ofFun R.actO Um) S Y := by
    intro g
    rw [hMx]
    exact hI g
  have hTD := interInv ℓ R.Gg R.OC R.actO r _ _ _ Y' F.lnzd hDT hY1 hY2
  have hT3 := t3W ℓ R.Tt r Vm R.z R.z' R.ϖ R.ϖ₁ R.w 0 F.zz F.ϖϖ hX.1 hX.2 hVm hw2
  have hT3all : ∀ j : ℤ, _ := fun j => t3W ℓ R.Tt r Vm R.z R.z' R.ϖ R.ϖ₁ R.w j F.zz F.ϖϖ hX.1 hX.2
    hVm hw2
  have hHTp := htW ℓ R.Tt r Vm R.w U F.omtf hHT (fun u _ => (hT3all u).1) 0

  set y := v ᵥ* Y' with hy
  have hinv : ∀ g : R.G, (fun k => R.actO (R.p g) (y k)) ᵥ* Um (R.p g) = y := by
    intro g
    have h1 : (fun k => R.actO (R.p g) (v k)) ᵥ* S.Mx (R.p g) = v := by
      have := hv g
      have e : repS R S 0 g v = (fun k => R.actO (R.p g) (v k)) ᵥ*
          ((((R.χ (R.p g)) ^ (0 : ℤ) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • S.Mx (R.p g)) := rfl
      rw [e] at this
      simpa using this
    have h2 := hTD (R.p g)
    rw [hMx] at h2
    rw [hy, map_vecMul', Matrix.vecMul_vecMul, h2, ← Matrix.vecMul_vecMul, h1]

  have hcoord : ∀ k, ∃ a : R.Tt.Oi, R.emb a = y k := by
    intro k
    apply hfix
    intro h hh
    have := congrFun (hinv h) k
    rw [hUH h hh, Matrix.vecMul_one] at this
    exact this
  choose a ha using hcoord
  have hrel : ∀ t, ∑ q, R.Tt.g0 (a q) * algebraMap R.Tt.Om R.Tt.Oi (Vm q t) = a t := by
    intro t
    apply hemb
    have := congrFun (hinv R.gg) t
    rw [hUg] at this
    rw [ha t, ← this, map_sum]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, map_mul, ← hg0, ha]
    rfl

  let am : Fin r → R.Tt.Om := fun t => R.Tt.pr (a t)
  have ham : R.Tt.gmI Vm R.w 0 am = am := by
    rw [gmI_apply]
    funext t
    have := congrArg R.Tt.pr (hrel t)
    rw [map_sum] at this
    show ∑ q, R.Tt.Vi Vm R.w 0 t q * R.Tt.pr (a q) = R.Tt.pr (a t)
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e : R.Tt.pr (R.Tt.g0 (a q) * algebraMap R.Tt.Om R.Tt.Oi (Vm q t)) = Vm q t * R.Tt.pr (a q) := by
      rw [mul_comm, ← Algebra.smul_def, map_smul, R.Tt.pr_comp_g_zero, smul_eq_mul]
    rw [e, Vi_apply]
    simp
  have htf : ∀ x : Fin r → R.Tt.Om, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0 := by
    intro x hx
    funext k
    exact F.omtf _ (congrFun hx k)
  have ham0 : am = 0 := eigenInj ℓ R.w _ hm1 (fun _ => hm2) hval U 0 h0U (Fin r → R.Tt.Om)
    (R.Tt.gmI Vm R.w 0) htf hHTp am ham

  let aX : Fin r → R.Tt.Xm := fun t => ⟨a t, congrFun ham0 t⟩
  have haX : R.Tt.gXI Vm R.w 0 aX = aX := by
    funext t
    apply Subtype.ext
    rw [gXI_coe]
    show ∑ q, R.Tt.Vi Vm R.w 0 t q • R.Tt.g0 (a q) = a t
    rw [← hrel t]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Vi_apply, Algebra.smul_def, mul_comm]
    simp
  have haX0 := hT3.1 aX haX
  have ha0 : ∀ t, a t = 0 := fun t => congrArg (fun z : R.Tt.Xm => (z : R.Tt.Oi)) (congrFun haX0 t)
  have hy0 : y = 0 := by
    funext k
    rw [← ha k, ha0 k, map_zero]
    rfl
  have : (ℓ : R.OC) • v = 0 := by
    have e : (v ᵥ* Y') ᵥ* Y = (ℓ : R.OC) • v := by
      rw [Matrix.vecMul_vecMul, hY2, Matrix.vecMul_smul, Matrix.vecMul_one]
    rw [← e, ← hy, hy0, Matrix.zero_vecMul]
  funext k
  exact F.lnzd _ (congrFun this k)

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

lemma x_nzd {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) {r M0 h0 : ℕ} (F : R.Facts r M0 h0) :
    ∀ a : R.OC, R.ϑ (R.jA R.x) * a = 0 → a = 0 := by
  have hℓ : ℓ.Prime := Fact.out
  have hN : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos hℓ.pos _) (Nat.sub_pos_of_lt hℓ.one_lt)
  intro a ha
  apply F.lnzd
  obtain ⟨N, hN'⟩ := Nat.exists_eq_add_of_le hN
  rw [← F.thx, hN', add_comm, pow_succ]
  calc R.ϑ (R.jA R.x) ^ N * R.ϑ (R.jA R.x) * R.c * a
      = R.ϑ (R.jA R.x) ^ N * R.c * (R.ϑ (R.jA R.x) * a) := by ring
    _ = 0 := by rw [ha, mul_zero]

theorem umH : StatUmH := by
  intro ℓ _ R r L En M0 h0 W F FH h hh
  have hs := FH.pH h hh
  have hG : W.Gm (R.p h) = 1 := by
    apply hat_inj R F
    rw [hat_one]
    have e : hat R (W.Gm (R.p h)) * W.Xx = W.Xx := by
      rw [show hat R (W.Gm (R.p h)) * W.Xx = ((W.Gm (R.p h)).map R.jA).map R.ι * W.Xx from rfl,
        ← W.W2, W.fixH _ hs]
    have := congrArg (fun M => M * W.Xi) e
    simp only [Matrix.mul_assoc, W.inv1, Matrix.mul_one] at this
    exact this
  have hc : R.ϑ (R.jA (R.cx (R.p h))) = 1 := by
    have h1 := congrArg R.ϑ (F.gx (R.p h))
    rw [FH.fixAs _ hs, map_mul] at h1
    have : R.ϑ (R.jA R.x) * (R.ϑ (R.jA (R.cx (R.p h))) - 1) = 0 := by
      rw [mul_sub, mul_one, mul_comm, ← h1, sub_self]
    exact sub_eq_zero.mp (x_nzd R F _ this)
  ext a b
  show R.ϑ (R.jA ((R.cx (R.p h)) ^ M0 * W.Gm (R.p h) a b)) = _
  rw [hG, map_mul, map_mul, map_pow, map_pow, hc, one_pow, one_mul]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem h0W : InvariantsOfTwistedModule := by
  intro ℓ _ R r L En M0 h0 W A Y' F FH hA hY1 hY2 ρ Sτ Pp Sp Cm Bm Uτ hX hP hS hB hHT h0U hne infm infX X
    hInf hT4 hUn hFl hLES
  obtain ⟨hv, hm1, hm2, _⟩ := w_facts R F
  have hI := wInter ℓ R r L En M0 h0 W A F hA
  have hVm := w3Vm ℓ R r L En M0 h0 W F
  have hinjO : Function.Injective R.eOh := by
    intro a b hab
    have := FH.injE hab
    rw [← R.Tt.pr_alg a, this, R.Tt.pr_alg]
  obtain ⟨s1, s2, s3, s4, s5⟩ := sec3 ℓ R.Gg R.OC R.Tt.Om R.eOh R.actO r ρ (L.sl R.actO) Sτ (UmW R L W)
    (VmW R L W) (A.map R.ϑ) Y' Pp Sp Cm Bm (R.z * R.ϖ) F.lnzd hinjO hI hY2 hP hS hB hVm
  have hPiece := pieceBThm ℓ R ρ r M0 h0 Sτ _ (Cm * VmW R L W * Bm) Uτ _ _ F hX s3 s2 s1 s5 hHT 0 infm infX
    hInf hT4
  have hCB : Cm.map R.eOh * Bm.map R.eOh = 1 := by
    rw [← Matrix.map_mul, s4, Matrix.map_one _ (map_zero _) (map_one _)]
  have hzero := cyclotomicInvariantsZero_statement ℓ R ρ r M0 h0 Sτ _ (Cm * VmW R L W * Bm) Uτ _ _ F hX s3 s2 s1 s5 hHT h0U FH.t4
    FH.injE FH.g0E
    (by
      intro h hh
      show (Cm.map R.eOh).map (R.actO (R.p h)) * UmW R L W (R.p h) * Bm.map R.eOh = 1
      rw [umH ℓ R r L En M0 h0 W F FH h hh, Matrix.mul_one]
      have : (Cm.map R.eOh).map (R.actO (R.p h)) = Cm.map R.eOh := by
        ext a b
        exact FH.fixOi h hh _
      rw [this, hCB])
    (by
      show (Cm.map R.eOh).map (R.actO (R.p R.gg)) * UmW R L W (R.p R.gg) * Bm.map R.eOh = _
      have e1 : (Cm.map R.eOh).map (R.actO (R.p R.gg)) = Cm.map R.eOh := by
        ext a b
        show R.actO (R.p R.gg) (R.emb (algebraMap R.Tt.Om R.Tt.Oi (Cm a b))) = _
        rw [FH.g0E, AlgHom.commutes]
        rfl
      have e2 : UmW R L W (R.p R.gg) = (VmW R L W).map R.eOh := umVm ℓ R r L En M0 h0 W F
      rw [e1, e2, ← Matrix.map_mul, ← Matrix.map_mul]
      rfl)
  refine Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic.h0 ℓ R.w (mOf ℓ R.s (M0 + h0)) hm1 (fun _ => hm2) hv Uτ h0U hne (X.toH0 _) hPiece hUn hFl hLES
    ⟨?_, ?_⟩
  · intro x _ _
    exact Subtype.ext (hzero x.1 x.2)
  · intro x
    exact ⟨map_zero _, map_zero _⟩

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
end
end
