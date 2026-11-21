import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBoundAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SepDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatticeIsometry
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.NormProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.DetMono
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SymmetricDistance.SymDistOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeMultiplicity.EncardLeOfFinset
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.ArchPlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDefs

section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

open PI.LatCountG

theorem hsN_zero {n : ℕ} : hsN (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [hsN, Formalism.REAL.hs]

theorem hsN_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := Real.sqrt_nonneg _

theorem mem_gf (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (g : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (g : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := γ.2

def gm (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) : Matrix (Fin I.n) (Fin I.n) I.E :=
  (((mem_gf I γ).choose : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)

theorem gm_spec (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (gm I γ).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (gm I γ).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := (mem_gf I γ).choose_spec.2

theorem gm_inj (I : Formalism.MainNotions.S.AutInst) {γ γ' : I.GFset} (h : gm I γ = gm I γ') : γ = γ' := by
  obtain ⟨h1a, h1b⟩ := gm_spec I γ
  obtain ⟨h2a, h2b⟩ := gm_spec I γ'
  rw [h] at h1a h1b
  apply Subtype.ext
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((h1a v).trans (h2a v).symm))
  · exact Subtype.ext (Units.ext (h1b.trans h2b.symm))

theorem phi_eq (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (γ : I.GFset) (v : InfinitePlace I.F) :
    Formalism.MainNotions.S.uMat ((x⁻¹ * (γ : I.GA) * y).1 v) = amat I x y v (gm I γ) := by
  obtain ⟨h1, -⟩ := gm_spec I γ
  rw [amat, ← h1 v]
  simp only [Formalism.MainNotions.S.uMat, Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul,
    Units.val_mul]

theorem amat_sub (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (v : InfinitePlace I.F) (δ₁ δ₂ : Matrix (Fin I.n) (Fin I.n) I.E) :
    amat I x y v (δ₁ - δ₂) = amat I x y v δ₁ - amat I x y v δ₂ := by
  have hm : (δ₁ - δ₂).map (I.φ v) = δ₁.map (I.φ v) - δ₂.map (I.φ v) := by
    ext i j; simp
  simp only [amat, hm, mul_sub, sub_mul]

theorem latCountAll_of (hB : BoxBound) (hLM : LatMap) (hLS : LatSub) (hS : Sep) (hP : PackLem) (hN : NPos)
    (hC : CardPl) : LatCountAll := by
  classical
  intro I x y hx hy r hr S hSc
  have hn : 1 ≤ I.n := hN I x hx
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = PI.LatCountG.tau1 I x * PI.LatCountG.tau1 I y := ⟨_, rfl⟩
  rw [← hρdef]
  have hρ : 0 < ρ := by rw [hρdef]; exact mul_pos hx hy
  have hτx : PI.LatCountG.tau1 I x ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hτy : PI.LatCountG.tau1 I y ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hρle : ∀ v, ρ ≤ Real.sqrt I.n * Real.exp (r v) := fun v => by
    have h0 : ρ ≤ 1 / 2 * (1 / 2) := by rw [hρdef]; exact mul_le_mul hτx hτy hy.le (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.sqrt I.n := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have h3 : (1 : ℝ) ≤ Real.exp (r v) := Real.one_le_exp (hr v)
    nlinarith
  let g : I.GFset → (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
    fun γ v => amat I x y v (gm I γ)
  have hgsub : ∀ γ γ' : I.GFset, ∀ v, g γ v - g γ' v = amat I x y v (gm I γ - gm I γ') :=
    fun γ γ' v => (amat_sub I x y v _ _).symm
  have hlat : ∀ γ ∈ S, ∀ u ∈ PI.LatCountG.latSet I y, gm I γ *ᵥ u ∈ PI.LatCountG.latSet I x :=
    fun γ hγ u hu => hLM I x y γ (mem_gf I γ).choose (gm_spec I γ).2 (hSc γ hγ).1 u hu
  have hsep : ∀ γ ∈ S, ∀ γ' ∈ S, gm I γ ≠ gm I γ' → ∃ v, ρ ≤ hsN (g γ v - g γ' v) := by
    intro γ hγ γ' hγ' hne
    have hδ : gm I γ - gm I γ' ≠ 0 := sub_ne_zero.mpr hne
    have hmap : ∀ u ∈ PI.LatCountG.latSet I y,
        (gm I γ - gm I γ') *ᵥ u ∈ PI.LatCountG.latSet I x := by
      intro u hu
      rw [Matrix.sub_mulVec]
      exact hLS I x _ _ (hlat γ hγ u hu) (hlat γ' hγ' u hu)
    have hineq := hS I x y hx hy _ hδ hmap
    rw [← hρdef] at hineq
    by_contra hcon
    push_neg at hcon
    have hprod : ∏ v, hsN (g γ v - g γ' v) < ρ ^ I.f := by
      rw [← hC I, ← Finset.card_univ, ← Finset.prod_const]
      by_cases h0 : ∃ v, hsN (g γ v - g γ' v) = 0
      · obtain ⟨v, hv⟩ := h0
        rw [Finset.prod_eq_zero (Finset.mem_univ v) hv]
        exact Finset.prod_pos fun _ _ => hρ
      · push_neg at h0
        have hne' : (Finset.univ : Finset (InfinitePlace I.F)).Nonempty := by
          by_contra he
          rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at he
          have hf0 : I.f = 0 := by rw [← hC I]; exact Fintype.card_eq_zero
          have hpos : 0 < I.f := by
            first
              | exact (hC I) ▸ Fintype.card_pos
              | unfold Formalism.MainNotions.S.AutInst.f; exact Module.finrank_pos
          omega
        exact Finset.prod_lt_prod_of_nonempty
          (fun v _ => lt_of_le_of_ne (hsN_nonneg _) (h0 v).symm) (fun v _ => hcon v) hne'
    simp only [hgsub] at hprod
    linarith
  have hinj : Set.InjOn g S := by
    intro γ hγ γ' hγ' heq
    by_contra hne
    obtain ⟨v, hv⟩ := hsep γ hγ γ' hγ' (fun h => hne (gm_inj I h))
    rw [heq, sub_self, hsN_zero] at hv
    linarith
  have hbound : ∀ p ∈ S.image g, ∀ v, hsN (p v) ≤ Real.sqrt I.n * Real.exp (r v) := by
    intro p hp v
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    show hsN (amat I x y v (gm I γ)) ≤ _
    rw [← phi_eq]
    refine (hB I.n (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v)).trans ?_
    gcongr
    exact (hSc γ hγ).2 v
  have hsepT : ∀ p ∈ S.image g, ∀ q ∈ S.image g, p ≠ q → ∃ v, ρ ≤ hsN (p v - q v) := by
    intro p hp q hq hpq
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp hq
    exact hsep γ hγ γ' hγ' (fun h => hpq (by simp only [g, h]))
  have hpack := hP (InfinitePlace I.F) I.n (fun v => Real.sqrt I.n * Real.exp (r v)) (fun _ => ρ)
    (fun _ => hρ) (fun v => by positivity) (S.image g) hbound hsepT
  have hexp : ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) = Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnn : ∀ v, 0 ≤ 2 * (Real.sqrt I.n * Real.exp (r v)) + ρ := fun v => by
    have := Real.sqrt_nonneg (I.n : ℝ)
    have := Real.exp_pos (r v)
    nlinarith
  calc (S.card : ℝ) = ((S.image g).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ ∏ v, ((2 * (Real.sqrt I.n * Real.exp (r v)) + ρ) / ρ) ^ (2 * I.n ^ 2) := hpack
    _ ≤ ∏ v, ((3 * Real.sqrt I.n / ρ) * Real.exp (r v)) ^ (2 * I.n ^ 2) := by
        refine Finset.prod_le_prod (fun v _ => pow_nonneg (div_nonneg (hnn v) hρ.le) _)
          (fun v _ => ?_)
        refine pow_le_pow_left₀ (div_nonneg (hnn v) hρ.le) ?_ _
        rw [div_mul_eq_mul_div]
        gcongr
        nlinarith [hρle v]
    _ = (∏ v : InfinitePlace I.F, (3 * Real.sqrt I.n / ρ) ^ (2 * I.n ^ 2)) *
          ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) := by
        rw [← Finset.prod_mul_distrib]; simp_rw [mul_pow]
    _ = _ := by rw [hexp, Finset.prod_const, Finset.card_univ, hC I, ← pow_mul]

end PI.UnitaryGroupMassFormula.LCG
end
end

section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

theorem sublattice_of_lattice : LatSub := by
  intro I x u u' hu hu'
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu hu' ⊢
  have h : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((u - u') i)) =
      (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) -
        (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u' i)) := by
    funext i
    simp [map_sub]
  rw [h, Matrix.mulVec_sub]
  exact Submodule.sub_mem _ hu hu'

theorem lattice_map_image : LatMap := by
  intro I x y γ g hγ hK u hu
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu ⊢
  have h1 : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (((g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) =
      I.fmat γ.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) := by
    funext i
    rw [hγ]
    exact RingHom.map_mulVec _ _ _ i
  have hK' : ∀ v, v ∈ I.Lf ↔ I.fmat (x⁻¹ * γ * y).2 *ᵥ v ∈ I.Lf := hK
  have hk := (hK' (I.fmat y.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i))).1 hu
  rw [h1]
  convert hk using 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Formalism.MainNotions.S.AutInst.fmat, Prod.snd_mul, Prod.snd_inv]
  push_cast
  simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)),
    Matrix.mul_one]

theorem norm_positive : NPos := by
  intro I x h
  by_contra hn
  have hn0 : I.n = 0 := by omega
  have hE : IsEmpty (PI.LatCountG.Sub I x) := by
    constructor
    intro s
    have hj := s.j_pos
    apply s.b_ind.ne_zero ⟨0, by omega⟩
    funext i
    exact absurd i.2 (by omega)
  have h0 : PI.LatCountG.tau1 I x = 0 := by
    unfold PI.LatCountG.tau1
    rw [Real.iInf_of_isEmpty]
    exact min_eq_right (by norm_num)
  linarith

theorem card_places_bound : CardPl := by
  intro I
  haveI : NumberField.IsTotallyReal I.F := I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
  have h3 := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (K := I.F)
  show _ = Module.finrank ℚ I.F
  omega

end PI.UnitaryGroupMassFormula.LCG
end
end

section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

open PI.LatCountG

theorem hsN_nonneg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := by
  unfold hsN
  exact Real.sqrt_nonneg _

theorem lattice_is_discrete_group : LatIsG := by
  intro I x
  obtain ⟨Λ, h1, h2, h3⟩ := PI.UnitaryGroupMassFormula.LSC.lattice_isometry I x
  exact ⟨Λ, h1, h2, h3⟩

theorem gram_nonneg (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) : 0 ≤ ((gramV I z v b).det).re := by
  let C : Matrix (Fin I.n) (Fin j) ℂ := Matrix.of fun i a => coordV I z v (b a) i
  have hG : gramV I z v b = Cᴴ * C := by
    ext a c
    simp [gramV, C, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hG]
  exact (hDM I.n j C 1 1 zero_le_one (fun w => by simp)).1

theorem ht_eq (I : Formalism.MainNotions.S.AutInst) {z : I.GA} (s : Sub I z) :
    ht I s = (∏ v, ((gramV I z v s.b).det).re) / (idx I s.B s.b : ℝ) := rfl

theorem tau_pow_le_ht (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (hz : 0 < tau1 I z) (s : Sub I z) :
    tau1 I z ^ (2 * I.f * s.j) ≤ ht I s ∧ idx I s.B s.b ≠ 0 := by
  have hf : 0 < I.f := Module.finrank_pos
  have hj : 0 < s.j := s.j_pos
  have hN : (0 : ℝ) < 2 * (I.f : ℝ) * (s.j : ℝ) := by
    have : (0 : ℝ) < I.f := by exact_mod_cast hf
    have : (0 : ℝ) < s.j := by exact_mod_cast hj
    positivity
  have hht : ∀ t : Sub I z, 0 ≤ ht I t := by
    intro t
    rw [ht_eq]
    exact div_nonneg (Finset.prod_nonneg fun v _ => gram_nonneg hDM I z v t.b) (Nat.cast_nonneg _)
  have hsize : ∀ t : Sub I z, 0 ≤ size I t := fun t => Real.rpow_nonneg (hht t) _
  have hle : tau1 I z ≤ size I s :=
    (min_le_right _ _).trans (ciInf_le ⟨0, by rintro _ ⟨t, rfl⟩; exact hsize t⟩ s)
  have hpow : size I s ^ (2 * I.f * s.j) = ht I s := by
    unfold size
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hht s)]
    push_cast
    rw [one_div_mul_cancel hN.ne', Real.rpow_one]
  refine ⟨?_, ?_⟩
  · calc tau1 I z ^ (2 * I.f * s.j) ≤ size I s ^ (2 * I.f * s.j) := pow_le_pow_left₀ hz.le hle _
      _ = ht I s := hpow
  · intro h0
    have h1 : ht I s = 0 := by
      rw [ht_eq, h0]
      simp
    have hs0 : size I s = 0 := by
      unfold size
      rw [h1, Real.zero_rpow (one_div_pos.2 hN).ne']
    linarith

theorem separation_of_points : SepOf := by
  intro hLat hDual hCh hArch hIdx hNP hDM _hCard I x y hx hy δ hδ hmap
  obtain ⟨Λ, hFG, hspan, hΛ⟩ := hLat I y
  obtain ⟨k, u, b', hk, hu, hind1, hspan1, hb', hind2, hperp, hspan2⟩ := hCh I y δ hδ
  have huΛ : ∀ c, u c ∈ Λ := fun c => by
    have := hu c
    rw [hΛ] at this
    exact this
  have hbΛ : ∀ a, b' a ∈ Λ := fun a => by
    have := hb' a
    rw [hΛ] at this
    exact this
  let s₁ : Sub I x :=
    { j := k
      j_pos := hk
      b := fun c => δ *ᵥ u c
      b_ind := hind1
      B := imSub I Λ δ
      B_lat := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        exact hmap w (by rw [hΛ]; exact hw)
      b_mem := fun c => Submodule.mem_map.2 ⟨u c, huΛ c, rfl⟩
      B_span := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        exact hspan1 w }
  let s₂ : Sub I y :=
    { j := k
      j_pos := hk
      b := b'
      b_ind := hind2
      B := perpSub I Λ δ
      B_lat := by
        intro z hz
        rw [hΛ]
        exact (Submodule.mem_inf.1 hz).1
      b_mem := fun a => Submodule.mem_inf.2 ⟨hbΛ a, hperp a⟩
      B_span := fun z hz => hspan2 z (Submodule.mem_inf.1 hz).2 }
  obtain ⟨h1, hi1⟩ := tau_pow_le_ht hDM I x hx s₁
  obtain ⟨h2, hi2⟩ := tau_pow_le_ht hDM I y hy s₂
  rw [ht_eq] at h1 h2
  change tau1 I x ^ (2 * I.f * k) ≤ (∏ v, ((gramV I x v (fun c => δ *ᵥ u c)).det).re) /
    (idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) at h1
  change tau1 I y ^ (2 * I.f * k) ≤ (∏ v, ((gramV I y v b').det).re) / (idx I (perpSub I Λ δ) b' : ℝ) at h2
  change idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) ≠ 0 at hi1
  change idx I (perpSub I Λ δ) b' ≠ 0 at hi2
  have hdualΛ : ∀ w, (∀ w' ∈ Λ, hf I w' w ∈ (algebraMap (𝓞 I.E) I.E).range) → w ∈ Λ := by
    intro w hw
    have := hDual I y w (by rw [hΛ]; exact hw)
    rw [hΛ] at this
    exact this
  have hN := hIdx I Λ hFG hspan hdualΛ δ k u b' huΛ hind1 hspan1 hbΛ hind2 hperp hspan2 hi1 hi2
  have hNP' := hNP I (pairM I b' u).det
  have hi1' : (0 : ℝ) < idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) := by exact_mod_cast Nat.pos_of_ne_zero hi1
  have hi2' : (0 : ℝ) < idx I (perpSub I Λ δ) b' := by exact_mod_cast Nat.pos_of_ne_zero hi2
  have hHp : 0 ≤ ∏ v, hsN (amat I x y v δ) := Finset.prod_nonneg fun v _ => hsN_nonneg' _
  have key : ((tau1 I x * tau1 I y) ^ I.f) ^ (2 * k) ≤ (∏ v, hsN (amat I x y v δ)) ^ (2 * k) := by
    rw [← pow_mul, mul_pow, show I.f * (2 * k) = 2 * I.f * k by ring]
    calc tau1 I x ^ (2 * I.f * k) * tau1 I y ^ (2 * I.f * k)
        ≤ ((∏ v, ((gramV I x v (fun c => δ *ᵥ u c)).det).re) / (idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ)) *
          ((∏ v, ((gramV I y v b').det).re) / (idx I (perpSub I Λ δ) b' : ℝ)) :=
          mul_le_mul h1 h2 (pow_nonneg (hy.le) _) ((pow_nonneg hx.le _).trans h1)
      _ = (∏ v, (((gramV I x v (fun c => δ *ᵥ u c)).det).re * ((gramV I y v b').det).re)) /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          rw [Finset.prod_mul_distrib, div_mul_div_comm]
      _ ≤ (∏ v, (hsN (amat I x y v δ) ^ (2 * k) * ‖I.φ v (pairM I b' u).det‖ ^ 2)) /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (mul_pos hi1' hi2').le
          exact Finset.prod_le_prod (fun v _ => mul_nonneg (gram_nonneg hDM I x v _) (gram_nonneg hDM I y v _))
            (fun v _ => hArch I x y δ k u b' v hind1 hspan1 hind2 hperp)
      _ = (∏ v, hsN (amat I x y v δ)) ^ (2 * k) * |((Algebra.norm ℚ (pairM I b' u).det : ℚ) : ℝ)| /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, hNP']
      _ ≤ (∏ v, hsN (amat I x y v δ)) ^ (2 * k) := by
          rw [div_le_iff₀ (mul_pos hi1' hi2')]
          exact mul_le_mul_of_nonneg_left hN (pow_nonneg hHp _)
  exact le_of_pow_le_pow_left₀ (by omega) hHp key

end PI.UnitaryGroupMassFormula.LCG
end
end

section
noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace BoxB

variable {n : ℕ}

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra Matrix.frobeniusNormedSpace

lemma frob_sq (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ^ 2 = Formalism.REAL.hs A := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  simp only [Real.rpow_two]
  norm_num [Formalism.REAL.hs]

lemma frob_eq (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ = Real.sqrt (Formalism.REAL.hs A) := by
  rw [← frob_sq, Real.sqrt_sq (norm_nonneg A)]

lemma hs_one : Formalism.REAL.hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  unfold Formalism.REAL.hs
  have h1 : ∀ i : Fin n, ∑ j, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Matrix.one_apply_ne (Ne.symm hj)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp [h1]

lemma norm_one_eq : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [frob_eq, hs_one]

lemma term_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ ≤ Real.sqrt n * (‖X‖ ^ k / k.factorial) := by
  have hsq : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have hpow : ‖X ^ k‖ ≤ Real.sqrt n * ‖X‖ ^ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [norm_one_eq]
    · calc ‖X ^ k‖ ≤ ‖X‖ ^ k := norm_pow_le' X hk
        _ ≤ Real.sqrt n * ‖X‖ ^ k := le_mul_of_one_le_left (by positivity) hsq
  have hc : ‖((k.factorial : ℂ)⁻¹)‖ = (k.factorial : ℝ)⁻¹ := by simp
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [norm_smul, hc, inv_mul_eq_div, mul_div_assoc']
  exact div_le_div_of_nonneg_right hpow hf.le

lemma norm_exp_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.sqrt n * Real.exp ‖X‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  have hs := (NormedSpace.expSeries_div_hasSum_exp ‖X‖).mul_left (Real.sqrt n)
  rw [← Real.exp_eq_exp_ℝ] at hs
  exact tsum_of_norm_bounded hs (fun k => term_le hn X k)

lemma hs_exp_le (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (NormedSpace.exp X) ≤ (Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Formalism.REAL.hs]
  · rw [← frob_sq, ← frob_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_exp_le hn X) 2

end Frob

private lemma hs_eq_re_trace_conjTranspose_mul' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs M = (Mᴴ * M).trace.re := by
  unfold Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma hs_unitary_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : kᴴ * k = 1) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (k * M) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace_conjTranspose_mul', hs_eq_re_trace_conjTranspose_mul', Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k M, hk,
    Matrix.one_mul]

end BoxB

open BoxB in
theorem box_lattice_point_bound : BoxBound := by
  intro n ε g
  have hK : ∀ k : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε → kᴴ * k = 1 := by
    intro k hk
    simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hk
    exact Matrix.mem_unitaryGroup_iff'.mp hk.1
  have hP : Formalism.REAL.Polar := Formalism.REAL.polar_decomposition_holds
  have hgi : Formalism.REAL.inUJ ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) := g.2
  obtain ⟨k0, X0, hk0, hX0, hg0⟩ := (hP n ε).1 _ hgi
  set S := {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
      t = Real.sqrt (Formalism.REAL.hs X)} with hS
  have hne : S.Nonempty := ⟨_, k0, X0, hk0, hX0, hg0, rfl⟩
  have hbound : ∀ t ∈ S, hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp t := by
    rintro t ⟨k, X, hk, _, hgk, rfl⟩
    unfold hsN Formalism.MainNotions.S.uMat
    rw [hgk, hs_unitary_mul (hK k hk)]
    calc Real.sqrt (Formalism.REAL.hs (NormedSpace.exp X))
        ≤ Real.sqrt ((Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2) :=
          Real.sqrt_le_sqrt (hs_exp_le X)
      _ = Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X)) := Real.sqrt_sq (by positivity)
  show hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp (sInf S)
  by_contra hlt
  push_neg at hlt
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h0 : hsN (Formalism.MainNotions.S.uMat g) = 0 := by
      unfold hsN Formalism.REAL.hs
      simp
    rw [h0] at hlt
    simp at hlt
  · have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
    set a := hsN (Formalism.MainNotions.S.uMat g) with ha
    have hapos : 0 < a := lt_of_le_of_lt (by positivity) hlt
    have h1 : sInf S < Real.log (a / Real.sqrt n) := by
      rw [Real.lt_log_iff_exp_lt (div_pos hapos hsqpos), lt_div_iff₀ hsqpos, mul_comm]
      exact hlt
    obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hne h1
    have h2 := hbound t htS
    have h3 : Real.exp t < a / Real.sqrt n := by
      rw [← Real.exp_log (div_pos hapos hsqpos)]
      exact Real.exp_lt_exp.mpr htlt
    rw [lt_div_iff₀ hsqpos] at h3
    linarith

end PI.UnitaryGroupMassFormula.LCG
end
end

section
noncomputable section

open MeasureTheory Metric Module

namespace PI.UnitaryGroupMassFormula.LCG

def matVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : EuclideanSpace ℂ (Fin N × Fin N) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

theorem norm_matVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ‖matVec A‖ = hsN A := by
  rw [EuclideanSpace.norm_eq, hsN, Formalism.REAL.hs, Fintype.sum_prod_type]
  rfl

theorem matVec_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) : matVec (A - B) = matVec A - matVec B := by
  ext ij
  simp [matVec]

theorem finrank_matSpace (N : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin N × Fin N)) = 2 * N ^ 2 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, sq]

theorem lattice_packLem : PackLem := by
  intro ι _ N R ρ hρ hR T hT hsep
  classical
  let W := EuclideanSpace ℂ (Fin N × Fin N)
  let μ : Measure W := Measure.addHaar
  let ν : Measure (ι → W) := Measure.pi fun _ => μ
  let B : (ι → Matrix (Fin N) (Fin N) ℂ) → Set (ι → W) :=
    fun p => Set.univ.pi fun v => ball (matVec (p v)) (ρ v / 2)
  let Big : Set (ι → W) := Set.univ.pi fun v => ball (0 : W) (R v + ρ v / 2)
  have hdisj : (T : Set (ι → Matrix (Fin N) (Fin N) ℂ)).PairwiseDisjoint B := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    obtain ⟨v, hv⟩ := hsep p hp q hq hpq
    have h1 := (Set.mem_univ_pi.1 hzp) v
    have h2 := (Set.mem_univ_pi.1 hzq) v
    rw [mem_ball] at h1 h2
    have h3 : dist (matVec (p v)) (matVec (q v)) < ρ v := by
      calc dist (matVec (p v)) (matVec (q v)) ≤ dist (matVec (p v)) (z v) + dist (z v) (matVec (q v)) :=
            dist_triangle _ _ _
        _ < ρ v / 2 + ρ v / 2 := by rw [dist_comm] at h1; exact add_lt_add h1 h2
        _ = ρ v := by ring
    rw [dist_eq_norm, ← matVec_sub, norm_matVec] at h3
    linarith
  have hmeas : ∀ p ∈ T, MeasurableSet (B p) := fun p _ =>
    MeasurableSet.univ_pi fun v => measurableSet_ball
  have hsub : (⋃ p ∈ T, B p) ⊆ Big := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    refine Set.mem_univ_pi.2 fun v => ?_
    have h1 := (Set.mem_univ_pi.1 hz) v
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_ball_zero_iff]
    have h2 : ‖matVec (p v)‖ ≤ R v := by rw [norm_matVec]; exact hT p hp v
    calc ‖z v‖ = ‖(z v - matVec (p v)) + matVec (p v)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z v - matVec (p v)‖ + ‖matVec (p v)‖ := norm_add_le _ _
      _ < ρ v / 2 + R v := by linarith
      _ = R v + ρ v / 2 := by ring
  have key : ∑ p ∈ T, ν (B p) ≤ ν Big := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact measure_mono hsub
  set d := finrank ℝ W with hd
  set c := μ (ball (0 : W) 1) with hc
  have hc0 : c ≠ 0 := (measure_ball_pos μ (0 : W) one_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  have hB : ∀ p, ν (B p) = ∏ v, ENNReal.ofReal ((ρ v / 2) ^ d) * c := by
    intro p
    simp only [ν, B, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v])
  have hBig : ν Big = ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c := by
    simp only [ν, Big, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v, hR v])
  simp only [hB, Finset.sum_const, nsmul_eq_mul] at key
  rw [hBig] at key
  have hfin : ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c ≠ ⊤ :=
    ENNReal.prod_ne_top fun v _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  have key' := ENNReal.toReal_mono hfin key
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod, ENNReal.toReal_prod] at key'
  simp only [ENNReal.toReal_mul] at key'
  have hc' : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hpos : ∀ v, 0 < ρ v / 2 := fun v => by linarith [hρ v]
  simp only [fun v => ENNReal.toReal_ofReal (pow_nonneg (hpos v).le d),
    fun v => ENNReal.toReal_ofReal (pow_nonneg (add_pos_of_nonneg_of_pos (hR v) (hpos v)).le d)] at key'
  have hprodpos : 0 < ∏ v, (ρ v / 2) ^ d * c.toReal :=
    Finset.prod_pos fun v _ => mul_pos (pow_pos (hpos v) d) hc'
  rw [← le_div_iff₀ hprodpos, ← Finset.prod_div_distrib] at key'
  have hdN : d = 2 * N ^ 2 := finrank_matSpace N
  calc (T.card : ℝ) ≤ ∏ v, (R v + ρ v / 2) ^ d * c.toReal / ((ρ v / 2) ^ d * c.toReal) := key'
    _ = ∏ v, ((2 * R v + ρ v) / ρ v) ^ (2 * N ^ 2) := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [mul_div_mul_right _ _ hc'.ne', ← div_pow, hdN]
      congr 1
      have := hρ v
      field_simp

end PI.UnitaryGroupMassFormula.LCG

end
end

section
noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

theorem archimedean_inequality : ArchIneq := by
  intro n k A C D κ hκ hA hker
  have hGdet := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k D 1 1 zero_le_one (by intro w; simp)).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin k) (Fin k) ℂ, G = Dᴴ * D := ⟨_, rfl⟩
  rw [← hG] at hGdet ⊢
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : G.det.im = 0 := by
    have hstar : star G.det = G.det := by rw [← Matrix.det_conjTranspose, hGh]
    have h1 := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h1
    linarith
  by_cases hg : G.det = 0
  · rw [hg, Complex.zero_re, mul_zero]
    exact mul_nonneg (pow_nonneg hκ k) (sq_nonneg _)
  · have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hg
    obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin k) ℂ, X = D * G⁻¹ * Dᴴ * C := ⟨_, rfl⟩
    have hAP : A * (D * G⁻¹ * Dᴴ) = A := by
      apply Matrix.ext_of_mulVec_single
      intro j
      have h1 : Dᴴ *ᵥ ((Pi.single j 1 : Fin n → ℂ) - (D * G⁻¹ * Dᴴ) *ᵥ Pi.single j 1) = 0 := by
        have h3 : Dᴴ * (D * G⁻¹ * Dᴴ) = G * G⁻¹ * Dᴴ := by
          rw [hG]
          simp only [Matrix.mul_assoc]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h3, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul, sub_self]
      have h2 := hker _ h1
      rw [Matrix.mulVec_sub, sub_eq_zero] at h2
      rw [← Matrix.mulVec_mulVec, ← h2]
    have hAX : A * X = A * C := by
      rw [hX, ← Matrix.mul_assoc, hAP]
    have hdm := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k X A κ hκ hA).2
    rw [hAX] at hdm
    have hXh : Xᴴ = Cᴴ * D * G⁻¹ * Dᴴ := by
      rw [hX]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv,
        hGh, Matrix.mul_assoc]
    have hXX : Xᴴ * X = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by
      rw [hXh, hX]
      have hGG : G⁻¹ * (Dᴴ * D) = 1 := by
        rw [← hG]
        exact Matrix.nonsing_inv_mul G hGu
      calc Cᴴ * D * G⁻¹ * Dᴴ * (D * G⁻¹ * Dᴴ * C) = Cᴴ * D * (G⁻¹ * (Dᴴ * D)) * G⁻¹ * (Dᴴ * C) := by
            simp only [Matrix.mul_assoc]
        _ = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by rw [hGG, Matrix.mul_one]
    have hdetX : (Xᴴ * X).det = star (Dᴴ * C).det * (Dᴴ * C).det / G.det := by
      have hCD : Cᴴ * D = (Dᴴ * C)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hXX, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hCD,
        Matrix.det_conjTranspose]
      ring
    have h5 : (Xᴴ * X).det * G.det = star (Dᴴ * C).det * (Dᴴ * C).det := by
      rw [hdetX, div_mul_cancel₀ _ hg]
    have hval : (Xᴴ * X).det.re * G.det.re = ‖(Dᴴ * C).det‖ ^ 2 := by
      have h6 := congrArg Complex.re h5
      rw [Complex.mul_re, him, mul_zero, sub_zero] at h6
      rw [h6, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    calc (((A * C)ᴴ * (A * C)).det).re * G.det.re ≤ κ ^ k * (Xᴴ * X).det.re * G.det.re :=
          mul_le_mul_of_nonneg_right hdm hGdet
      _ = κ ^ k * ‖(Dᴴ * C).det‖ ^ 2 := by rw [mul_assoc, hval]

end PI.UnitaryGroupMassFormula.LCG
end
end

section
noncomputable section

open NumberField Matrix TensorProduct

namespace PI.UnitaryGroupMassFormula.LCG

namespace DualI

open Formalism.UG Formalism.UG.P

abbrev AA (I : Formalism.MainNotions.S.AutInst) : Type := I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F

abbrev SS (I : Formalism.MainNotions.S.AutInst) : Subring (AA I) := Formalism.MainNotions.S.IntAf I.F I.E

abbrev iA (I : Formalism.MainNotions.S.AutInst) : I.E →+* AA I := Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)

theorem sig_eq (I : Formalism.MainNotions.S.AutInst) :
    ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := rfl

theorem mem_latSet (I : Formalism.MainNotions.S.AutInst) (y : I.GA) (u : Fin I.n → I.E) :
    u ∈ PI.LatCountG.latSet I y ↔
      (((y.2 : GL (Fin I.n) (AA I))⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ
        (fun i => iA I (u i)) ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L := by
  unfold PI.LatCountG.latSet
  rw [Set.mem_setOf_eq, PI.UnitaryGroupMassFormula.LSC.LatIs.lamAf_eq I]
  rfl

theorem hform_smul_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (a : A) (w x : n → A) : hform τ J w (a • x) = a * hform τ J w x := by
  unfold hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w x x' : n → A) : hform τ J w (x + x') = hform τ J w x + hform τ J w x' := by
  unfold hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_sub_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w x x' : n → A) : hform τ J w (x - x') = hform τ J w x - hform τ J w x' := by
  unfold hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_zero_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w : n → A) : hform τ J w 0 = 0 := by
  unfold hform
  simp

theorem pair_int (I : Formalism.MainNotions.S.AutInst) (w : Fin I.n → I.E) (hw : w ∈ I.L)
    (x : Fin I.n → AA I) (hx : x ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L) :
    hform (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (I.J.map (iA I)) (fun i => iA I (w i)) x ∈ SS I := by
  unfold latS at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨l, hl, rfl⟩ := h
    exact csDual_span I.cm.sig I.J I.L l ((I.L_dual l).mp hl) (fun i => iA I (w i))
      (Submodule.subset_span ⟨w, hw, rfl⟩)
  | zero =>
    rw [hform_zero_right]
    exact (SS I).zero_mem
  | add x y _ _ hx hy =>
    rw [hform_add_right]
    exact (SS I).add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, hform_smul_right]
    exact (SS I).mul_mem a.2 hx

end DualI

open DualI Formalism.UG Formalism.UG.P in
theorem dual_lattice_inclusion : DualIncl := by
  intro I y u hu
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hdet : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
  set g : GL (Fin I.n) (AA I) := (y.2 : GL (Fin I.n) (AA I)) with hg
  have hU : cT (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (g : Matrix (Fin I.n) (Fin I.n) (AA I)) * I.J.map (iA I) *
      (g : Matrix (Fin I.n) (Fin I.n) (AA I)) = I.J.map (iA I) := y.2.2

  have hu' : ∀ w ∈ Formalism.UG.CS.globLat g I.L, hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J w u ∈
      (algebraMap (𝓞 I.E) I.E).range := by
    intro w hw
    apply hu w
    rw [mem_latSet]
    exact hw
  obtain ⟨z, hz⟩ : ∃ z, z = ((g⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ
      (fun i => iA I (u i)) := ⟨_, rfl⟩
  have hxz : (fun i => iA I (u i)) = (g : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ z := by
    rw [hz, mulVec_mulVec, Units.mul_inv, one_mulVec]

  have hw : ∀ w ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L,
      hform (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (I.J.map (iA I)) w z ∈ SS I := by
    intro w hw
    have hu2 := (span_recovery_of_integral_adelic_approx csGlob_intAdApprox I.F I.E (Fin I.n) I.L hfin I.L_span g
      ((g : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ w)).2
      (by rwa [mulVec_mulVec, Units.inv_mul, one_mulVec])
    have := csDual_span I.cm.sig I.J (Formalism.UG.CS.globLat g I.L) u hu' _ hu2
    rwa [hxz, hform_mulVec, hU] at this
  obtain ⟨c, hc, hlow⟩ := adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Fin I.n × Fin I.n => (I.J⁻¹) p.1 p.2)
  have hi : ∀ i, levelafC I.E c * ((I.J.map (iA I)) *ᵥ z) i ∈ SS I := by
    intro i
    have h1 := hw _ (hlow (Pi.single i (1 : AA I)) (fun k => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _))
    have h2 : (fun k => levelafC I.E c * (Pi.single i (1 : AA I) : Fin I.n → _) k) =
        levelafC I.E c • (Pi.single i (1 : AA I) : Fin I.n → _) := by
      funext k; simp [Pi.smul_apply]
    rwa [h2, csDual_hform_smul_left, csDual_sig_C, sf_single] at h1
  have hinv : (I.J⁻¹).map (iA I) * I.J.map (iA I) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul I.J hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hz2 : (I.J⁻¹).map (iA I) *ᵥ ((I.J.map (iA I)) *ᵥ z) = z := by
    rw [mulVec_mulVec, hinv, one_mulVec]
  have hv : ∀ k, levelafC I.E c * iA I (m : I.E) * z k ∈ SS I := by
    intro k
    have := csDual_expand (F := I.F) (I.J⁻¹) ((I.J.map (iA I)) *ᵥ z) (levelafC I.E c) (iA I (m : I.E)) k
    rw [hz2] at this
    rw [this]
    refine sum_mem fun i _ => mul_mem ?_ (hi i)
    rw [← map_mul]
    exact adelstabL_incl_int (F := I.F) _ (hm (k, i))

  set D : 𝓞 I.F := c * (m : 𝓞 I.F) with hD
  have hD0 : D ≠ 0 := mul_ne_zero hc (Int.cast_ne_zero.2 hm0)
  have hmC : levelafC I.E ((m : 𝓞 I.F)) = iA I (m : I.E) := by
    rw [← adelstab_incl_C, map_intCast]
  have hDl : levelafC I.E D = levelafC I.E c * iA I (m : I.E) := by
    rw [hD, levelafC_mul, hmC]
  have hDE : algebraMap (𝓞 I.F) I.E D ≠ 0 := adelstab_algebraMap_ne_zero (F := I.F) (E := I.E) D hD0
  have happ : ∀ k, ∃ b : 𝓞 I.E, ∃ t ∈ SS I, levelafC I.E D * z k =
      iA I (algebraMap (𝓞 I.E) I.E b) + levelafC I.E (D * c) * t := by
    intro k
    obtain ⟨b, t, ht, hbt⟩ := csGlob_approx (F := I.F) (E := I.E) csGlob_intAdApprox (D * c)
      (mul_ne_zero hD0 hc) (levelafC I.E D * z k) (by rw [hDl]; exact hv k)
    exact ⟨b, t, ht, hbt⟩
  choose b t ht hbt using happ
  set v : Fin I.n → I.E := fun k => algebraMap (𝓞 I.E) I.E (b k) * (algebraMap (𝓞 I.F) I.E D)⁻¹ with hvdef
  have hq : iA I ((algebraMap (𝓞 I.F) I.E D)⁻¹) * levelafC I.E D = 1 := by
    rw [← adelstab_incl_C, ← map_mul, inv_mul_cancel₀ hDE, map_one]
  have hzk : ∀ k, z k = iA I (v k) + levelafC I.E c * t k := by
    intro k
    have h1 := hbt k
    rw [levelafC_mul D c] at h1
    have h3 : iA I (v k) = iA I (algebraMap (𝓞 I.E) I.E (b k)) * iA I ((algebraMap (𝓞 I.F) I.E D)⁻¹) := by
      rw [hvdef]; exact map_mul _ _ _
    rw [h3]
    linear_combination iA I ((algebraMap (𝓞 I.F) I.E D)⁻¹) * h1 - z k * hq + (levelafC I.E c * t k) * hq
  have hct : (fun k => levelafC I.E c * t k) ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L := hlow _ ht
  have hzv : (fun k => iA I (v k)) = z - (fun k => levelafC I.E c * t k) := by
    funext k
    rw [Pi.sub_apply, hzk k]
    ring

  have hvL : v ∈ I.L := by
    rw [I.L_dual v]
    intro w hwL
    have hint : IsIntegral ℤ (Formalism.UG.hform (starRingEnd I.E) I.J w v) := by
      apply csGlob_int (F := I.F)
      rw [← sig_eq, ← csDual_hform_incl, hzv, hform_sub_right]
      exact sub_mem (hw _ (Submodule.subset_span ⟨w, hwL, rfl⟩)) (pair_int I w hwL _ hct)
    exact ⟨⟨_, hint⟩, rfl⟩
  rw [mem_latSet]
  show ((g⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ (fun i => iA I (u i)) ∈ _
  rw [← hz]
  have hz3 : z = (fun k => iA I (v k)) + (fun k => levelafC I.E c * t k) := by
    rw [hzv]; abel
  rw [hz3]
  exact add_mem (Submodule.subset_span ⟨v, hvL, rfl⟩) hct

end PI.UnitaryGroupMassFormula.LCG
end
end

section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace ChooseW

section Gen

variable {K : Type*} [Field K] {n : ℕ}

lemma ann_range (δ : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (ha : ∀ z, δ *ᵥ z = 0 → a ⬝ᵥ z = 0) : ∃ t, a = t ᵥ* δ := by
  let ℓ : Module.Dual K (Fin n → K) :=
    { toFun := fun z => a ⬝ᵥ z
      map_add' := fun x y => dotProduct_add a x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hmem : ℓ ∈ (LinearMap.ker δ.mulVecLin).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact ha z (by simpa using hz)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨fun j => φ (fun r => if j = r then 1 else 0), ?_⟩
  funext i
  have h1 := LinearMap.congr_fun hφ (fun r => if i = r then 1 else 0)
  rw [LinearMap.dualMap_apply] at h1
  have h2 : ℓ (fun r => if i = r then 1 else 0) = a i := by
    simp [ℓ, dotProduct]
  rw [h2, LinearMap.pi_apply_eq_sum_univ φ] at h1
  rw [← h1]
  simp [Matrix.vecMul, dotProduct, Matrix.mulVec, mul_comm]

lemma scaled_li {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] (d : ι → V)
    (hli : LinearIndependent K d) (m : ι → K) (hm : ∀ c, m c ≠ 0) :
    LinearIndependent K (fun c => m c • d c) := by
  have := hli.units_smul (fun c => Units.mk0 (m c) (hm c))
  convert this using 1
  funext c
  simp [Units.smul_def]

lemma scaled_span {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] (d : ι → V) (m : ι → K)
    (hm : ∀ c, m c ≠ 0) :
    Submodule.span K (Set.range d) ≤ Submodule.span K (Set.range fun c => m c • d c) := by
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : d c = (m c)⁻¹ • (m c • d c) := by rw [smul_smul, inv_mul_cancel₀ (hm c), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

lemma basis_range (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : A.rank = k) :
    ∃ z : Fin k → Fin n → K, LinearIndependent K (fun c => A *ᵥ z c) ∧
      ∀ w, A *ᵥ w ∈ Submodule.span K (Set.range fun c => A *ᵥ z c) := by
  let R := LinearMap.range A.mulVecLin
  let bas := Module.finBasisOfFinrankEq K R hk
  have hz : ∀ c, ∃ z, A *ᵥ z = (bas c : Fin n → K) := fun c => by
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (bas c).2
    exact ⟨z, by simpa using hz⟩
  choose z hz using hz
  have hspan : Submodule.span K (Set.range fun c => (bas c : Fin n → K)) = R := by
    rw [show (fun c => (bas c : Fin n → K)) = R.subtype ∘ bas from rfl, Set.range_comp,
      ← Submodule.map_span, bas.span_eq, Submodule.map_top, Submodule.range_subtype]
  refine ⟨z, ?_, ?_⟩
  · simp only [hz]
    exact bas.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
  · intro w
    simp only [hz]
    rw [hspan]
    exact LinearMap.mem_range.mpr ⟨w, by simp⟩

lemma rank_pos (δ : Matrix (Fin n) (Fin n) K) (hδ : δ ≠ 0) : 1 ≤ δ.rank := by
  by_contra h
  have h0 : δ.rank = 0 := by omega
  have hbot : LinearMap.range δ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hz : Matrix.toLin' δ = 0 := by
    rw [Matrix.toLin'_apply']
    exact LinearMap.range_eq_bot.mp hbot
  exact hδ (Matrix.toLin'.injective (by rw [hz, map_zero]))

end Gen

section Star

variable {E : Type*} [Field E] [StarRing E] {n : ℕ}

def sv (w : Fin n → E) : Fin n → E := fun i => starRingEnd E (w i)

lemma sv_sv (w : Fin n → E) : sv (sv w) = w := by
  funext i; simp [sv]

lemma star_li {k : ℕ} (v : Fin k → Fin n → E) (h : LinearIndependent E v) :
    LinearIndependent E (fun a => sv (v a)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 : ∑ a, starRingEnd E (g a) • v a = 0 := by
    funext j
    have := congrArg (starRingEnd E) (congrFun hg j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sv, map_sum, map_mul,
      starRingEnd_self_apply, map_zero, Pi.zero_apply] at this ⊢
    rw [← this]
  have := h _ h0 i
  simpa using this

lemma star_span {k : ℕ} (v : Fin k → Fin n → E) (w : Fin n → E)
    (hw : sv w ∈ Submodule.span E (Set.range v)) :
    w ∈ Submodule.span E (Set.range fun a => sv (v a)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hw
  refine (Submodule.mem_span_range_iff_exists_fun E).mpr ⟨fun a => starRingEnd E (c a), ?_⟩
  rw [← sv_sv w, ← hc]
  funext j
  simp [sv, Finset.sum_apply, map_sum, map_mul]

end Star

lemma scale {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : E) • w ∈ Λ := by
  classical
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := hΛ ▸ Submodule.mem_top
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.mp hw
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ ((y : E) * f i) := by
    have := hint (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
    simpa [zsmul_eq_mul] using this
  rw [smul_smul]
  have := Λ.smul_mem (⟨(y : E) * f i, hi⟩ : 𝓞 E) (g i).2
  convert this using 1
  exact (algebraMap_smul E _ _).symm

lemma hf_eq (I : Formalism.MainNotions.S.AutInst) (w z : Fin I.n → I.E) : hf I w z = (sv w ᵥ* I.J) ⬝ᵥ z := by
  simp only [hf, Formalism.UG.hform, dotProduct, vecMul, Finset.sum_mul, sv]
  rw [Finset.sum_comm]

end ChooseW

open ChooseW in
theorem choice_of_generators : Choose := by
  intro I y δ hδ
  obtain ⟨Λ, _, hΛs, hΛ0⟩ := PI.UnitaryGroupMassFormula.LSC.lattice_isometry I y
  have hΛ : PI.LatCountG.latSet I y = (Λ : Set (Fin I.n → I.E)) := hΛ0
  have hJ : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
  set k := δ.rank with hk
  have hk1 : 1 ≤ k := rank_pos δ hδ

  obtain ⟨z, hzli, hzsp⟩ := basis_range δ k hk.symm
  have hsc : ∀ c, ∃ m : ℤ, m ≠ 0 ∧ ((m : I.E) • z c) ∈ Λ := fun c => scale Λ hΛs (z c)
  choose mu hmu0 hmuΛ using hsc

  set B : Matrix (Fin I.n) (Fin I.n) I.E := (δ * I.J⁻¹)ᵀ with hB
  have hBr : B.rank = k := by
    rw [hB, Matrix.rank_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_nonsing_inv_det I.J hJ)]
  obtain ⟨t, htli, htsp⟩ := basis_range B k hBr
  have hsc' : ∀ a, ∃ m : ℤ, m ≠ 0 ∧ ((m : I.E) • sv (B *ᵥ t a)) ∈ Λ := fun a => scale Λ hΛs _
  choose mb hmb0 hmbΛ using hsc'
  have hmu0' : ∀ c, ((mu c : ℤ) : I.E) ≠ 0 := fun c => Int.cast_ne_zero.mpr (hmu0 c)
  have hmb0' : ∀ a, ((mb a : ℤ) : I.E) ≠ 0 := fun a => Int.cast_ne_zero.mpr (hmb0 a)

  have hperpB : ∀ s w, δ *ᵥ w = 0 → ((B *ᵥ s) ᵥ* I.J) ⬝ᵥ w = 0 := by
    intro s w hw
    rw [hB, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hJ, Matrix.mul_one, ← Matrix.dotProduct_mulVec, hw, dotProduct_zero]
  refine ⟨k, fun c => ((mu c : ℤ) : I.E) • z c, fun a => ((mb a : ℤ) : I.E) • sv (B *ᵥ t a), hk1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c; rw [hΛ]; exact hmuΛ c
  · simp only [Matrix.mulVec_smul]
    exact scaled_li (fun c => δ *ᵥ z c) hzli (fun c => ((mu c : ℤ) : I.E)) hmu0'
  · intro w
    simp only [Matrix.mulVec_smul]
    exact scaled_span (fun c => δ *ᵥ z c) (fun c => ((mu c : ℤ) : I.E)) hmu0' (hzsp w)
  · intro a; rw [hΛ]; exact hmbΛ a
  · exact scaled_li (fun a => sv (B *ᵥ t a)) (star_li (fun a => B *ᵥ t a) htli)
      (fun a => ((mb a : ℤ) : I.E)) hmb0'
  · intro a w hw
    rw [hf_eq]
    have hs : sv (((mb a : ℤ) : I.E) • sv (B *ᵥ t a)) = ((mb a : ℤ) : I.E) • (B *ᵥ t a) := by
      funext i; simp [sv]
    rw [hs, Matrix.smul_vecMul, smul_dotProduct, hperpB _ _ hw, smul_zero]
  · intro w hw
    have hann : ∀ z', δ *ᵥ z' = 0 → (sv w ᵥ* I.J) ⬝ᵥ z' = 0 := fun z' hz' => by
      rw [← hf_eq]; exact hw z' hz'
    obtain ⟨s, hs⟩ := ann_range δ _ hann
    have hsv : sv w = B *ᵥ s := by
      have : sv w = (sv w ᵥ* I.J) ᵥ* I.J⁻¹ := by
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJ, Matrix.vecMul_one]
      rw [this, hs, Matrix.vecMul_vecMul, hB, Matrix.mulVec_transpose]
    have h1 : sv w ∈ Submodule.span I.E (Set.range fun a => B *ᵥ t a) := hsv ▸ htsp s
    exact scaled_span (fun a => sv (B *ᵥ t a)) (fun a => ((mb a : ℤ) : I.E)) hmb0'
      (star_span (fun a => B *ᵥ t a) w h1)

end PI.UnitaryGroupMassFormula.LCG
end
end

section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace DIdx

def qI {S : Type} [CommRing S] (𝔞 : Ideal S) (a : S) : Ideal S where
  carrier := {y | ∀ c ∈ 𝔞, c * y ∈ Ideal.span {a}}
  add_mem' := by
    intro y y' hy hy' c hc
    rw [mul_add]
    exact add_mem (hy c hc) (hy' c hc)
  zero_mem' := by
    intro c _
    rw [mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro r y hy c hc
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ r (hy c hc)

def aI {K : Type} [Field K] [NumberField K] {k : ℕ} (X : Submodule (𝓞 K) (Fin k → K)) (x : Fin k → K) :
    Ideal (𝓞 K) where
  carrier := {c | c • x ∈ X}
  add_mem' := by
    intro c c' hc hc'
    rw [Set.mem_ofPred_eq, add_smul]
    exact add_mem hc hc'
  zero_mem' := by
    rw [Set.mem_ofPred_eq, zero_smul]
    exact zero_mem _
  smul_mem' := by
    intro r c hc
    rw [Set.mem_ofPred_eq, smul_eq_mul, mul_smul]
    exact X.smul_mem r hc

theorem absNorm_eq_index {S : Type} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (I : Ideal S) : Ideal.absNorm I = I.toAddSubgroup.index := rfl

theorem quot_le (K : Type) [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (a : 𝓞 K)
    (ha0 : a ≠ 0) :
    Ideal.span {a} ≤ qI 𝔞 a ∧
    (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≠ 0 ∧
    (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≤ Ideal.absNorm 𝔞 := by
  have hle : Ideal.span {a} ≤ qI 𝔞 a := by
    intro y hy c _
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [Ideal.mem_span_singleton']
    exact ⟨c * z, by ring⟩
  have hmul : 𝔞 * qI 𝔞 a ≤ Ideal.span {a} := Ideal.mul_le.mpr fun r hr s hs => hs r hr
  have hq0 : qI 𝔞 a ≠ ⊥ := by
    intro h
    have : a ∈ qI 𝔞 a := hle (Ideal.mem_span_singleton_self a)
    rw [h, Ideal.mem_bot] at this
    exact ha0 this
  have hNq : Ideal.absNorm (qI 𝔞 a) ≠ 0 := fun h => hq0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hNa : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    exact ha0 h
  have hN𝔞 : Ideal.absNorm 𝔞 ≠ 0 := fun h => h𝔞 (Ideal.absNorm_eq_zero_iff.mp h)
  have hrel : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) =
      Ideal.absNorm (Ideal.span {a}) := by
    rw [absNorm_eq_index, absNorm_eq_index]
    exact AddSubgroup.relIndex_mul_index ((Submodule.toAddSubgroup_le _ _).mpr hle)
  have hdvd : Ideal.absNorm (Ideal.span {a}) ∣ Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a) := by
    have := Ideal.absNorm_dvd_absNorm_of_le hmul
    rwa [map_mul] at this
  have hr0 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrel
    exact hNa hrel.symm
  refine ⟨hle, hr0, ?_⟩
  have h1 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) ≤
      Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a) := by
    rw [hrel]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hN𝔞 hNq)) hdvd
  exact Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_ne_zero hNq)

theorem dualL_anti {K : Type} [Field K] [NumberField K] {k : ℕ} {X Y : Submodule (𝓞 K) (Fin k → K)}
    (h : X ≤ Y) : dualL Y ≤ dualL X :=
  fun _ ht s hs => ht s (h hs)

theorem smul_dot {K : Type} [Field K] [NumberField K] {k : ℕ} (c : 𝓞 K) (x t : Fin k → K) :
    (c • x) ⬝ᵥ t = algebraMap (𝓞 K) K c * (x ⬝ᵥ t) := by
  simp only [dotProduct, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem step (K : Type) [Field K] [NumberField K] (k : ℕ) (X Y : Submodule (𝓞 K) (Fin k → K)) (hXY : X ≤ Y)
    (hne : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) (x : Fin k → K) (hxY : x ∈ Y) :
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤
      X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
  have hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y :=
    sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)
  have hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hneX1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0 := fun h =>
    hne (AddSubgroup.relIndex_eq_zero_of_le_right ((Submodule.toAddSubgroup_le _ _).mpr hX1Y) h)

  let g : 𝓞 K →+ (Fin k → K) := AddMonoidHom.mk' (fun c => c • x) (fun c c' => add_smul c c' x)
  have e1 : (aI X x).toAddSubgroup = X.toAddSubgroup.comap g := by
    ext c
    exact Iff.rfl
  have hrange : g.range ≤ (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
    rintro _ ⟨c, rfl⟩
    exact (X ⊔ Submodule.span (𝓞 K) {x}).smul_mem c hxX1
  have hN : Ideal.absNorm (aI X x) = X.toAddSubgroup.relIndex g.range := by
    rw [absNorm_eq_index, e1, AddSubgroup.index_comap]
  have hNne : Ideal.absNorm (aI X x) ≠ 0 := by
    rw [hN]
    exact fun h => hneX1 (AddSubgroup.relIndex_eq_zero_of_le_right hrange h)
  have hNle : Ideal.absNorm (aI X x) ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
    rw [hN]
    exact AddSubgroup.relIndex_le_of_le_right hrange hneX1
  have h𝔞 : aI X x ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hNne
    exact hNne rfl
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  have hax : a • x ∈ X := ha
  obtain ⟨hle, hq0, hqle⟩ := quot_le K (aI X x) h𝔞 a ha0

  let ψ : (Fin k → K) →+ K := AddMonoidHom.mk' (fun t => algebraMap (𝓞 K) K a * (x ⬝ᵥ t))
    (fun t t' => by simp only [dotProduct_add, mul_add])
  let mO : 𝓞 K →+ K := (algebraMap (𝓞 K) K).toAddMonoidHom
  have hinj : Function.Injective mO := IsFractionRing.injective (𝓞 K) K
  have ha0K : algebraMap (𝓞 K) K a ≠ 0 := fun h => ha0 (hinj (h.trans (map_zero _).symm))
  have claim1 : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup =
      ((Ideal.span {a}).toAddSubgroup.map mO).comap ψ ⊓ (dualL X).toAddSubgroup := by
    ext t
    constructor
    · intro ht
      refine ⟨?_, dualL_anti le_sup_left ht⟩
      obtain ⟨o, ho⟩ := ht x hxX1
      refine ⟨a * o, Ideal.mul_mem_right o _ (Ideal.mem_span_singleton_self a), ?_⟩
      show algebraMap (𝓞 K) K (a * o) = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)
      rw [map_mul, ho]
    · rintro ⟨⟨r, hr, hrt⟩, htX⟩
      obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      have hrt' : algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t) := by
        rw [← map_mul, mul_comm a o]
        exact hrt
      have hxt : x ⬝ᵥ t = algebraMap (𝓞 K) K o := (mul_left_cancel₀ ha0K hrt').symm
      intro s hs
      obtain ⟨s0, hs0, s1, hs1, rfl⟩ := Submodule.mem_sup.mp hs
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs1
      rw [add_dotProduct, smul_dot, hxt, ← map_mul]
      exact add_mem (htX s0 hs0) ⟨c * o, rfl⟩
  have claim2 : (dualL X).toAddSubgroup.map ψ ≤ (qI (aI X x) a).toAddSubgroup.map mO := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨o, ho⟩ := (show t ∈ dualL X from ht) (a • x) hax
    refine ⟨o, ?_, ?_⟩
    · intro c hc
      obtain ⟨o', ho'⟩ := (show t ∈ dualL X from ht) (c • x) hc
      have : c * o = o' * a := by
        apply hinj
        show algebraMap (𝓞 K) K (c * o) = algebraMap (𝓞 K) K (o' * a)
        rw [map_mul, map_mul, ho, ho', smul_dot, smul_dot]
        ring
      rw [this, Ideal.mem_span_singleton']
      exact ⟨o', rfl⟩
    · show algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)
      rw [ho, smul_dot]
  have hmapQ : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) =
      (Ideal.span {a}).toAddSubgroup.relIndex (qI (aI X x) a).toAddSubgroup :=
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hrel : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup =
      ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((dualL X).toAddSubgroup.map ψ) := by
    rw [claim1, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  have hQne : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) ≠ 0 := by
    rw [hmapQ]; exact hq0
  rw [hrel]
  refine ⟨fun h => hQne (AddSubgroup.relIndex_eq_zero_of_le_right claim2 h), ?_⟩
  calc ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((dualL X).toAddSubgroup.map ψ)
      ≤ ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) :=
        AddSubgroup.relIndex_le_of_le_right claim2 hQne
    _ = (Ideal.span {a}).toAddSubgroup.relIndex (qI (aI X x) a).toAddSubgroup := hmapQ
    _ ≤ Ideal.absNorm (aI X x) := hqle
    _ ≤ _ := hNle

end DIdx

open DIdx in
theorem dual_index_formula : DualIdx := by
  intro K _ _ k X Y hXY hne
  suffices H : ∀ m : ℕ, ∀ X Y : Submodule (𝓞 K) (Fin k → K), X ≤ Y →
      X.toAddSubgroup.relIndex Y.toAddSubgroup = m → m ≠ 0 →
      (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
        (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤ X.toAddSubgroup.relIndex Y.toAddSubgroup from
    H _ X Y hXY rfl hne
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X Y hXY hm hm0
  by_cases hYX : Y ≤ X
  · have e : X = Y := le_antisymm hXY hYX
    subst e
    rw [AddSubgroup.relIndex_self, AddSubgroup.relIndex_self]
    exact ⟨one_ne_zero, le_rfl⟩
  · obtain ⟨x, hxY, hxX⟩ := Set.not_subset.mp hYX
    have hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y :=
      sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)
    have hXX1 : X ≤ X ⊔ Submodule.span (𝓞 K) {x} := le_sup_left
    have hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    obtain ⟨h0, hle⟩ := step K k X Y hXY (by rw [hm]; exact hm0) x hxY
    have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXX1)
      ((Submodule.toAddSubgroup_le _ _).mpr hX1Y)
    rw [hm] at hmul
    have hb0 : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := by
      intro h; rw [h, mul_zero] at hmul; exact hm0 hmul.symm
    have ha0 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0 := by
      intro h; rw [h, zero_mul] at hmul; exact hm0 hmul.symm
    have ha1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 1 := by
      intro h
      rw [AddSubgroup.relIndex_eq_one] at h
      exact hxX (h hxX1)
    have hlt : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup < m := by
      rw [← hmul]
      have h2 : 2 ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by omega
      have hbpos := Nat.pos_of_ne_zero hb0
      nlinarith
    obtain ⟨ih0, ihle⟩ := ih _ hlt (X ⊔ Submodule.span (𝓞 K) {x}) Y hX1Y rfl hb0
    have hdmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hX1Y))
      ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hXX1))
    rw [← hdmul, hm, ← hmul]
    refine ⟨mul_ne_zero ih0 h0, ?_⟩
    rw [mul_comm (X.toAddSubgroup.relIndex _)]
    exact Nat.mul_le_mul ihle hle

end PI.UnitaryGroupMassFormula.LCG
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LCG

theorem latCountAll_of_steps (hB : BoxBound) (hP : PackLem) (hD : DualIncl) (hCh : Choose) (hA : ArchIneq)
    (hAP : ArchPlaceOf) (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of hB lattice_map_image sublattice_of_lattice
    (separation_of_points lattice_is_discrete_group hD hCh (hAP hA) hI PI.UnitaryGroupMassFormula.LSC.norm_product_formula PI.UnitaryGroupMassFormula.LSC.determinant_monotone card_places_bound)
    hP norm_positive card_places_bound

theorem latCountAll_of_open (hD : DualIncl) (hCh : Choose) (hAP : ArchPlaceOf) (hI : IndexIneq) :
    PI.LatCountG.LatCountAll :=
  latCountAll_of_steps box_lattice_point_bound lattice_packLem hD hCh archimedean_inequality hAP hI

theorem latCountAll_of_open2 (hAP : ArchPlaceOf) (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of_open dual_lattice_inclusion choice_of_generators hAP hI

theorem latCountAll_of_index (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of_open2 archimedean_place_exists hI

theorem latCountAll_of_idx (hD2 : DetIdx) (hIO : IndexOf) : PI.LatCountG.LatCountAll :=
  latCountAll_of_index (hIO dual_index_formula hD2)

end PI.UnitaryGroupMassFormula.LCG
end
end
