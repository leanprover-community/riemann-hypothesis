import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Dual

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
  {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem vLE_ne_zero' {κ : KK O} {D : ℝ} (h : vLE p κ D) : κ ≠ 0 := by
  rintro rfl
  obtain ⟨q, hq, -⟩ := h
  rw [valuation_zero_alt] at hq
  exact WithTop.top_ne_coe hq

theorem nv_irr' {w : O} (hw : Irreducible w) : dvrOrderNat w = 1 := by
  simp [dvrOrderNat, IsDiscreteValuationRing.addVal_uniformizer hw]

theorem vK_int_form (x : KK O) (hx : x ≠ 0) : ∃ k : ℤ, vK p x = (((k : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  unfold vK ordW
  rw [if_neg hx]
  exact ⟨_, rfl⟩

theorem vK_le_zero_of_not_int (S : UniformizedDVR p O) (a : KK O)
    (h : ¬ (0 : WithTop ℚ) ≤ vK p (a * (algebraMap O (KK O) S.w)⁻¹)) :
    ∃ q : ℚ, vK p a = (q : WithTop ℚ) ∧ q ≤ 0 := by
  have hw0 : S.w ≠ 0 := S.w_irr.ne_zero
  have hw0' : algebraMap O (KK O) S.w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hw0
  have hepos : (0 : ℚ) < ramE p O := by
    have := ramification_index_ne_zero S
    exact_mod_cast Nat.pos_of_ne_zero this
  have ha : a ≠ 0 := by
    rintro rfl
    apply h
    rw [zero_mul, valuation_zero_alt]
    exact le_top
  obtain ⟨k, hk⟩ := vK_int_form a ha
  have hwinv : vK p ((algebraMap O (KK O) S.w)⁻¹) =
      (((-1 : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
    rw [valuation_eq_of_fraction p _ 1 S.w one_ne_zero hw0 (by rw [inv_mul_cancel₀ hw0', map_one]),
      nv_irr' S.w_irr]
    simp [dvrOrderNat]
  rw [valuation_mul_alt, hk, hwinv, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at h
  push_neg at h
  refine ⟨(k : ℚ) / (ramE p O : ℚ), hk, ?_⟩
  have h2 : ((k : ℚ) - 1) / (ramE p O : ℚ) < 0 := by
    rw [sub_div]
    rw [neg_div] at h
    linarith
  have h3 : (k : ℚ) - 1 < 0 := by
    by_contra hc
    push_neg at hc
    exact absurd h2 (not_lt.2 (div_nonneg hc hepos.le))
  have h4 : k < 1 := by exact_mod_cast (by linarith : (k : ℚ) < 1)
  have h5 : (k : ℚ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
  exact div_nonpos_of_nonpos_of_nonneg h5 hepos.le

theorem be_sum_left (be : V → V → KK O) (hsm : ∀ (a : KK O) (u v : V), be (a • u) v = a * be u v)
    (hadd : ∀ u u' v, be (u + u') v = be u v + be u' v) {n : ℕ} (a : Fin n → KK O) (x : Fin n → V) (v : V) :
    be (∑ i, a i • x i) v = ∑ i, a i * be (x i) v := by
  classical
  have h0 : be 0 v = 0 := by
    have := hsm 0 0 v
    rwa [zero_smul, zero_mul] at this
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [h0]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsm, ih]

theorem goodSub_of_dual (S : UniformizedDVR p O) (be : V → V → KK O)
    (hsm : ∀ (a : KK O) (u v : V), be (a • u) v = a * be u v)
    (hadd : ∀ u u' v, be (u + u') v = be u v + be u' v)
    (L : Submodule O V) {n : ℕ} (x y : Fin n → V) (hx : ∀ i, x i ∈ L) (hy : ∀ i, y i ∈ L)
    (c : KK O) (hxy : ∀ i j, be (x i) (y j) = if i = j then c else 0) (D : ℝ) (hc : vLE p c D) :
    ∃ L₂ : Submodule O V, GoodSub p be L L₂ D ∧ n ≤ Module.finrank O L₂ := by
  classical
  have hc0 : c ≠ 0 := vLE_ne_zero' hc
  have hw0 : S.w ≠ 0 := S.w_irr.ne_zero
  have hw0' : algebraMap O (KK O) S.w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hw0
  have hbe0 : ∀ v, be 0 v = 0 := fun v => by
    have := hsm 0 0 v
    rwa [zero_smul, zero_mul] at this
  have hsum : ∀ (t : Fin n → KK O) (j : Fin n), be (∑ i, t i • x i) (y j) = t j * c := by
    intro t j
    rw [be_sum_left be hsm hadd t x (y j)]
    simp [hxy]
  have hspan : ∀ s : Fin n → O,
      (∑ i, s i • x i) ∈ (Submodule.span (KK O) (Set.range x)).restrictScalars O := by
    intro s
    rw [Submodule.restrictScalars_mem]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul (KK O) (s i) (x i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O, ⟨⟨inf_le_left, ?_⟩, ?_⟩, ?_⟩
  · intro o u ho hu hou
    refine Submodule.mem_inf.2 ⟨hu, ?_⟩
    have h2 := (Submodule.mem_inf.1 hou).2
    rw [Submodule.restrictScalars_mem] at h2 ⊢
    have ho' : algebraMap O (KK O) o ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 ho
    have hu' : u = (algebraMap O (KK O) o)⁻¹ • (o • u) := by
      rw [← algebraMap_smul (KK O) o u, smul_smul, inv_mul_cancel₀ ho', one_smul]
    rw [hu']
    exact Submodule.smul_mem _ _ h2
  · rintro u ⟨hu, hprim⟩
    obtain ⟨hul, huw⟩ := Submodule.mem_inf.1 hu
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_range_iff_exists_fun] at huw
    obtain ⟨t, rfl⟩ := huw
    by_cases hall : ∀ j, 0 ≤ vK p (t j * (algebraMap O (KK O) S.w)⁻¹)
    · exfalso
      choose s hs using fun j => (valuation_nonneg_iff_integral S _).1 (hall j)
      have ht : ∀ j, t j = algebraMap O (KK O) S.w * algebraMap O (KK O) (s j) := by
        intro j
        rw [← hs j, mul_comm (t j), ← mul_assoc, mul_inv_cancel₀ hw0', one_mul]
      have hx' : (∑ i, s i • x i) ∈ L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O :=
        Submodule.mem_inf.2 ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i), hspan s⟩
      have hu' : (∑ i, t i • x i) = S.w • ∑ i, s i • x i := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [ht i, mul_smul, algebraMap_smul, algebraMap_smul]
      exact S.w_irr.not_isUnit (hprim S.w _ hx' hu')
    · push_neg at hall
      obtain ⟨j, hj⟩ := hall
      obtain ⟨q, hq, hq0⟩ := vK_le_zero_of_not_int S (t j) (not_le.2 hj)
      obtain ⟨qc, hqc, hqcD⟩ := hc
      have hq0' : (q : ℝ) ≤ 0 := by exact_mod_cast hq0
      refine ⟨y j, hy j, q + qc, ?_, ?_⟩
      · rw [hsum, valuation_mul_alt, hq, hqc, ← WithTop.coe_add]
      · push_cast
        linarith
  · have hli : LinearIndependent (KK O) x := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have := hsum g i
      rw [hg, hbe0] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hc0
    have hliO : LinearIndependent O x := (LinearIndependent.iff_fractionRing O (KK O)).2 hli
    let f : Fin n → (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O : Submodule O V) :=
      fun i => ⟨x i, Submodule.mem_inf.2 ⟨hx i, by
        rw [Submodule.restrictScalars_mem]
        exact Submodule.subset_span ⟨i, rfl⟩⟩⟩
    have hf : LinearIndependent O f :=
      LinearIndependent.of_comp (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O).subtype hliO
    let φ : (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O : Submodule O V) →ₗ[O]
        (Fin n → KK O) :=
      { toFun := fun u j => be u (y j)
        map_add' := fun u u' => by
          funext j
          exact hadd _ _ _
        map_smul' := fun o u => by
          funext j
          simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply]
          rw [← algebraMap_smul (KK O) o (u : V), hsm, Algebra.smul_def] }
    have hφ : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      obtain ⟨-, huw⟩ := Submodule.mem_inf.1 u.2
      rw [Submodule.restrictScalars_mem, Submodule.mem_span_range_iff_exists_fun] at huw
      obtain ⟨t, ht⟩ := huw
      have ht0 : ∀ j, t j = 0 := fun j => by
        have h1 := congrFun hu j
        have h2 := hsum t j
        rw [ht] at h2
        change be (u : V) (y j) = 0 at h1
        rw [h1] at h2
        exact (mul_eq_zero.1 h2.symm).resolve_right hc0
      ext
      rw [← ht]
      simp [ht0]
    have hup : Module.rank O (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O :
        Submodule O V) ≤ n := by
      calc Module.rank O (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O :
            Submodule O V)
          ≤ Module.rank O (Fin n → KK O) := LinearMap.rank_le_of_injective φ hφ
        _ = Module.rank (KK O) (Fin n → KK O) :=
          (IsFractionRing.rank_right_eq (R := O) (S := KK O) (N := Fin n → KK O)).symm
        _ = n := by simp
    have hlow : (n : Cardinal) ≤ Module.rank O
        (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O : Submodule O V) := by
      simpa using hf.cardinal_le_rank
    rw [Module.finrank_eq_of_rank_eq (le_antisymm hup hlow)]

end Dual

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Map

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (ι : ℚ_[p] →+* KK O)

theorem map_glAct {N r : ℕ} (LL : ChainLetters N) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d (map ι F) =
      map ι (Formalism.GM.M.glAct p (gmL LL) j c d F) := by
  simp only [glAct, Formalism.GM.M.glAct, gmL, LinearMap.sum_apply, map_sum, Set.mem_setOf_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < j <;> by_cases h2 : LL.vec i = true <;> simp [h1, h2, pderiv_map]

theorem gm_ycond_stable {N r : ℕ} [NeZero r] (LL : Formalism.GM.M.Letters N) (j : ℕ) (Mt : WithTop ℤ) (c d : Fin r) :
    ∀ x ∈ Formalism.GM.M.YCond p (r := r) LL j Mt, Formalism.GM.M.glAct p LL j c d x ∈ Formalism.GM.M.YCond p (r := r) LL j Mt := by
  intro x hx
  have key : Formalism.GM.M.YCond p (r := r) LL j Mt ≤
      (Formalism.GM.M.YCond p (r := r) LL j Mt).comap (Formalism.GM.M.glAct p LL j c d) := by
    conv_lhs => unfold Formalism.GM.M.YCond
    refine sSup_le fun S hS y hy => ?_
    rw [Submodule.mem_comap]
    unfold Formalism.GM.M.YCond
    exact le_sSup hS (hS.2 c d y hy)
  exact key hx

theorem gm_ycond_supp {N r : ℕ} [NeZero r] (LL : Formalism.GM.M.Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    Formalism.GM.M.YCond p (r := r) LL j Mt ≤
      restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((Formalism.GM.M.wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1

theorem map_mem_restrictSupport {σ : Type} {s : Set (σ →₀ ℕ)} (F : MvPolynomial σ ℚ_[p])
    (hF : F ∈ restrictSupport ℚ_[p] s) : map ι F ∈ restrictSupport (KK O) s := by
  rw [mem_restrictSupport_iff] at hF ⊢
  exact (Finset.coe_subset.2 (support_map_subset ι F)).trans hF

theorem map_ycond {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt) :
    map ι y ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt := by
  have hsupp : Submodule.span (KK O) (map ι '' ((Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
      restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact map_mem_restrictSupport ι z (gm_ycond_supp (gmL LL) j Mt hz)
  have hstab : chStable (KK O) (r := r) LL j
      (Submodule.span (KK O) (map ι '' ((Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))) := by
    intro c d x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      apply Submodule.subset_span
      exact ⟨_, gm_ycond_stable (gmL LL) j Mt c d z hz, (map_glAct ι LL j c d z).symm⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | smul k a _ ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ k ha
  have hy' : map ι y ∈ Submodule.span (KK O) (map ι '' ((Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))) :=
    Submodule.subset_span ⟨y, hy, rfl⟩
  unfold Formalism.MainNotions.G.YCond
  exact le_sSup (show _ ∈ {S : Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) |
      S ≤ restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧
        chStable (KK O) LL j S} from ⟨hsupp, hstab⟩) hy'

theorem map_Y {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Formalism.GM.M.Y p (r := r) (gmL LL) J M) :
    map ι y ∈ Yjt (KK O) (r := r) LL J M := by
  rw [Formalism.GM.M.Y, Submodule.mem_inf, Submodule.mem_iInf] at hy
  rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨?_, fun k => map_ycond ι LL (J k) (M k) y (hy.2 k)⟩
  exact map_mem_restrictSupport ι y hy.1

variable {ι}

theorem map_int {σ : Type} (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y)
    (F : MvPolynomial σ ℚ_[p]) (hF : F ∈ Formalism.GM.M.IntPol p σ) : map ι F ∈ IntPol O σ := by
  obtain ⟨G, rfl⟩ := hF
  induction G using MvPolynomial.induction_on' with
  | monomial m a =>
    obtain ⟨y, hy⟩ := hint a
    refine ⟨monomial m y, ?_⟩
    simp [hy]
  | add a b ha hb =>
    rw [map_add, map_add]
    exact add_mem ha hb

theorem map_YZ {N r : ℕ} [NeZero r] (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y)
    (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Formalism.GM.M.YZ p (r := r) (gmL LL) J M) :
    map ι y ∈ YjtZ O (r := r) LL J M := by
  rw [Formalism.GM.M.YZ, Submodule.mem_inf] at hy
  have h2 : y ∈ Submodule.restrictScalars ℤ_[p] (Formalism.GM.M.Pol p r (gmL LL)) ⊓ Formalism.GM.M.IntPol p (Fin N × Fin r) := hy.2
  exact Submodule.mem_inf.2 ⟨map_Y ι LL J M y hy.1, map_int hint y (Submodule.mem_inf.1 h2).2⟩

theorem map_XiPolZ {N r t b : ℕ} (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y)
    (g : MvPolynomial (Formalism.GM.M.BVar N r t) ℚ_[p]) (hg : g ∈ Formalism.GM.M.XiPolZ p N r t b) :
    map ι g ∈ XiPolZ O N r t b := by
  have hg' := Submodule.mem_inf.1 hg
  exact Submodule.mem_inf.2 ⟨map_mem_restrictSupport ι g hg'.1, map_int hint g hg'.2⟩

end Map

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Formalism.MainNotions.G

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem castPow_zero (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) :
    ((p ^ n : ℕ) : O ⧸ (IsLocalRing.maximalIdeal O) ^ n) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ n)) (p ^ n), Nat.cast_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hpm n

def iotaN (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) :
    ℤ_[p] →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ n :=
  RingHom.comp (ZMod.castHom (ringChar.dvd (castPow_zero p O hpm n)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ n))
    (PadicInt.toZModPow n)

theorem iotaN_compat (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp (iotaN p O hpm n) = iotaN p O hpm m := by
  have hz := PadicInt.zmod_cast_comp_toZModPow (p := p) m n hle
  have key : ∀ (f g : ZMod (p ^ n) →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ m), f = g :=
    fun f g => RingHom.ext_zmod f g
  unfold iotaN
  rw [← hz]
  ext x
  simp only [RingHom.comp_apply]
  exact congrArg (fun f => f (PadicInt.toZModPow n x))
    (key ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp
      (ZMod.castHom (ringChar.dvd (castPow_zero p O hpm n)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ n)))
      ((ZMod.castHom (ringChar.dvd (castPow_zero p O hpm m)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ m)).comp
        (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ m)))))

def iota0 (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : ℤ_[p] →+* O :=
  ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal O)).symm : AdicCompletion (IsLocalRing.maximalIdeal O) O →+* O).comp
    (AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal O) (iotaN p O hpm) (fun hle => iotaN_compat p O hpm hle))

theorem padic_integers_embedding_map_prime (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    iota0 p O hpm (p : ℤ_[p]) = (p : O) :=
  map_natCast (iota0 p O hpm) p

theorem padic_integers_embedding_injective (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : Function.Injective (iota0 p O hpm) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hspec := PadicInt.unitCoeff_spec hne
  have h2 := congrArg (iota0 p O hpm) hspec
  rw [hx, map_mul, map_pow, padic_integers_embedding_map_prime] at h2
  have hu : IsUnit (iota0 p O hpm (PadicInt.unitCoeff hne : ℤ_[p])) := (Units.isUnit _).map _
  rcases mul_eq_zero.mp h2.symm with h3 | h3
  · exact hu.ne_zero h3
  · exact hp0 (pow_eq_zero_iff'.mp h3).1

def iotaQ (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : ℚ_[p] →+* KK O :=
  IsFractionRing.lift (A := ℤ_[p]) (K := ℚ_[p]) (g := (algebraMap O (KK O)).comp (iota0 p O hpm))
    ((IsFractionRing.injective O (KK O)).comp (padic_integers_embedding_injective p O hpm hp0))

theorem iotaQ_int (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : ℤ_[p]) :
    iotaQ p O hpm hp0 (x : ℚ_[p]) = algebraMap O (KK O) (iota0 p O hpm x) := by
  unfold iotaQ
  exact IsFractionRing.lift_algebraMap _ x

def iotaX (X : flipOneThree.Inst) : ℚ_[X.p] →+* KK X.O :=
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal X.O) X.O := X.setting.complete
  iotaQ X.p X.O X.setting.p_mem X.setting.p_ne

theorem iotaX_int (X : flipOneThree.Inst) (x : ℤ_[X.p]) :
    ∃ y : X.O, iotaX X (x : ℚ_[X.p]) = algebraMap X.O (KK X.O) y := by
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal X.O) X.O := X.setting.complete
  exact ⟨_, iotaQ_int X.p X.O X.setting.p_mem X.setting.p_ne x⟩

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Gens

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : ℚ_[p] →+* KK O} {N r : ℕ} [NeZero r]

theorem map_Ehat (D : BlockData N) (i : Fin (gmB D).T.t) :
    map ι ((gmB D).Ehat p (r := r) i) = D.Ehat O (r := r) i := by
  unfold Formalism.GM.M.BlockData.Ehat Formalism.MainNotions.G.BlockData.Ehat
  simp only [map_add, map_mul, map_X, map_sum]
  rfl

theorem map_Eplus (D : BlockData N) :
    map ι ((gmB D).Eplus p (r := r)) = D.Eplus O (r := r) := by
  unfold Formalism.GM.M.BlockData.Eplus Formalism.MainNotions.G.BlockData.Eplus
  simp only [map_add, map_mul, map_X, map_sum]
  rfl

theorem map_gens (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y) (D : BlockData N)
    (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p])
    (hx : x ∈ (gmB D).gens p (r := r) j jp) : map ι x ∈ D.gens O (r := r) j jp := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  refine ⟨map ι y, map_YZ hint (D.lettersAt j jp) D.T.J D.T.thr y hy, map ι g, map_XiPolZ hint g hg, ?_⟩
  simp only [map_mul, map_prod, map_pow, map_X, map_Ehat, map_Eplus, map_rename]
  rfl

theorem map_smul_Q {σ : Type} (c : ℚ_[p]) (x : MvPolynomial σ ℚ_[p]) : map ι (c • x) = ι c • map ι x := by
  rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]

theorem map_SSZ (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y) (D : BlockData N)
    (x : MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p]) (hx : x ∈ (gmB D).SSZ p (r := r)) :
    map ι x ∈ Submodule.span (KK O) (D.SSZ O (r := r) : Set (MvPolynomial (BVar N r D.T.t) (KK O))) := by
  unfold Formalism.GM.M.BlockData.SSZ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hok, hx⟩ := hx
    have hm : MvPolynomial.map ι x ∈ D.gens O (r := r) j jp := map_gens hint D j jp x hx
    exact Submodule.subset_span (Submodule.subset_span
      (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hok, hm⟩⟩⟩))
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | smul a x _ hx =>
    rw [← algebraMap_smul ℚ_[p] a x, map_smul_Q]
    exact Submodule.smul_mem _ _ hx

abbrev intMap (σ : Type) : MvPolynomial σ ℤ_[p] →ₐ[ℤ_[p]] MvPolynomial σ ℚ_[p] :=
  MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p])

theorem mem_intPol_iff {σ : Type} (F : MvPolynomial σ ℚ_[p]) :
    F ∈ Formalism.GM.M.IntPol p σ ↔ F ∈ (intMap (p := p) σ).range := Iff.rfl

private theorem X_mem_intMap {σ : Type} (v : σ) :
    (X v : MvPolynomial σ ℚ_[p]) ∈ (intMap (p := p) σ).range :=
  ⟨X v, by simp⟩

theorem gens_int (D : Formalism.GM.M.BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (Formalism.GM.M.BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.gens p (r := r) j jp) : x ∈ Formalism.GM.M.IntPol p (Formalism.GM.M.BVar N r D.T.t) := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  rw [mem_intPol_iff]
  rw [Formalism.GM.M.YZ] at hy
  rw [Formalism.GM.M.XiPolZ] at hg
  have h1 : y ∈ Formalism.GM.M.PolZ p r (D.lettersAt j jp) := (Submodule.mem_inf.1 hy).2
  rw [Formalism.GM.M.PolZ] at h1
  have h2 : y ∈ Formalism.GM.M.IntPol p (Fin N × Fin r) := (Submodule.mem_inf.1 h1).2
  have hE : ∀ i, D.Ehat p (r := r) i ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    intro i
    unfold Formalism.GM.M.BlockData.Ehat
    exact add_mem (mul_mem (X_mem_intMap _) (X_mem_intMap _))
      (sum_mem fun c _ => mul_mem (X_mem_intMap _) (X_mem_intMap _))
  have hP : D.Eplus p (r := r) ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    unfold Formalism.GM.M.BlockData.Eplus
    exact add_mem (mul_mem (X_mem_intMap _) (X_mem_intMap _))
      (sum_mem fun c _ => mul_mem (X_mem_intMap _) (X_mem_intMap _))
  have hy' : rename (Formalism.GM.M.chainEmb N r D.T.t) y ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    obtain ⟨G, rfl⟩ := (mem_intPol_iff y).1 h2
    exact ⟨rename (Formalism.GM.M.chainEmb N r D.T.t) G, by simp [map_rename]⟩
  have hg' : g ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range :=
    (mem_intPol_iff g).1 (Submodule.mem_inf.1 hg).2
  refine mul_mem (mul_mem (mul_mem ?_ (pow_mem (X_mem_intMap _) _)) hy') hg'
  exact mul_mem (mul_mem (prod_mem fun i _ => pow_mem (hE i) _) (pow_mem hP _))
    (prod_mem fun i _ => pow_mem (X_mem_intMap _) _)

theorem SSZ_int (D : Formalism.GM.M.BlockData N) (x : MvPolynomial (Formalism.GM.M.BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.SSZ p (r := r)) : x ∈ Formalism.GM.M.IntPol p (Formalism.GM.M.BVar N r D.T.t) := by
  unfold Formalism.GM.M.BlockData.SSZ at hx
  refine (Submodule.span_le.2 ?_) hx
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨j, jp, -, hz⟩ := hz
  exact gens_int D j jp z hz

end Gens

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
