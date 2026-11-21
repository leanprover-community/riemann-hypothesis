import Mathlib
import GroundTheory.PAdicHodge.WAFracAnnCris
import GroundTheory.PAdicHodge.WAFracAnnPt

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0}

theorem exists_pos_le_annNorm (v : T.Ann ρ0 σ0) (hv : ∀ r, 0 < T.annNorm ρ0 σ0 r v) :
    ∃ μ > 0, ∀ r, μ ≤ T.annNorm ρ0 σ0 r v := by
  have hK : IsCompact (Set.Icc (σ0 : ℝ) ρ0) := isCompact_Icc
  have hne : (Set.Icc (σ0 : ℝ) ρ0).Nonempty := ⟨σ0, le_rfl, σ0.2.2⟩
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (T.continuousOn_annNormR v)
  refine ⟨T.annNormR v x, ?_, fun r => ?_⟩
  · rw [T.annNormR_of_mem v ⟨x, hx⟩]; exact hv _
  · rw [← T.annNormR_of_mem v r]; exact hmin r.2

theorem annNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → T.Ann ρ0 σ0) (r : AnnRad ρ0 σ0) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ s, T.annNorm ρ0 σ0 r (f i) ≤ M) :
    T.annNorm ρ0 σ0 r (∑ i ∈ s, f i) ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, annNorm_zero]; exact hM
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (T.annNorm_add_le r _ _).trans (max_le (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem isUnit_one_add_ann (e : T.Ann ρ0 σ0) (h1 : T.annNorm ρ0 σ0 (annIn ρ0 σ0) e < 1)
    (h2 : T.annNorm ρ0 σ0 (annOut ρ0 σ0) e < 1) : IsUnit (1 + e) := by
  set lam := max (T.annNorm ρ0 σ0 (annIn ρ0 σ0) e) (T.annNorm ρ0 σ0 (annOut ρ0 σ0) e) with hlam
  have hl1 : lam < 1 := max_lt h1 h2
  have hl0 : 0 ≤ lam := le_max_of_le_left (T.annNorm_nonneg _ _)
  have hpow : ∀ (r : AnnRad ρ0 σ0), (r = annIn ρ0 σ0 ∨ r = annOut ρ0 σ0) → ∀ n : ℕ,
      T.annNorm ρ0 σ0 r ((-e) ^ n) ≤ lam ^ n := by
    intro r hr n
    rw [annNorm_pow, annNorm_neg]
    refine pow_le_pow_left₀ (T.annNorm_nonneg _ _) ?_ n
    rcases hr with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  set S : ℕ → T.Ann ρ0 σ0 := fun n => ∑ k ∈ Finset.range n, (-e) ^ k
  have hS : ∀ (r : AnnRad ρ0 σ0), (r = annIn ρ0 σ0 ∨ r = annOut ρ0 σ0) → ∀ m n, m ≤ n →
      T.annNorm ρ0 σ0 r (S n - S m) ≤ lam ^ m := by
    intro r hr m n hmn
    have e1 : S n - S m = ∑ k ∈ Finset.Ico m n, (-e) ^ k := by
      simp only [S]; rw [Finset.sum_Ico_eq_sub _ hmn]
    rw [e1]
    refine T.annNorm_sum_le _ _ r (pow_nonneg hl0 m) fun k hk => ?_
    exact (hpow r hr k).trans (pow_le_pow_of_le_one hl0 hl1.le (Finset.mem_Ico.1 hk).1)
  obtain ⟨g, hg⟩ := T.exists_limit_ann (z := S) fun ε hε => by
    obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one hε hl1
    refine ⟨J₀, fun J hJ K hK => ?_⟩
    have key : ∀ r : AnnRad ρ0 σ0, (r = annIn ρ0 σ0 ∨ r = annOut ρ0 σ0) →
        T.annNorm ρ0 σ0 r (S J - S K) ≤ ε := by
      intro r hr
      rcases le_total K J with h | h
      · exact (hS r hr K J h).trans ((pow_le_pow_of_le_one hl0 hl1.le hK).trans hJ₀.le)
      · rw [annNorm_sub_comm]
        exact (hS r hr J K h).trans ((pow_le_pow_of_le_one hl0 hl1.le hJ).trans hJ₀.le)
    exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩
  refine IsUnit.of_mul_eq_one g (T.eq_of_annNorm_sub ?_ ?_)
  all_goals
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (T.annNorm_nonneg _ _)
    rw [zero_add]
  · set r := annIn ρ0 σ0
    set B := T.annNorm ρ0 σ0 r (1 + e) + 1
    have hB : 0 < B := by have := T.annNorm_nonneg r (1 + e); positivity
    obtain ⟨J₁, hJ₁⟩ := eventually_atTop.1 ((hg r).eventually (gt_mem_nhds (div_pos hε hB)))
    obtain ⟨J₂, hJ₂⟩ := exists_pow_lt_of_lt_one hε hl1
    set J := max J₁ J₂
    have hgeom : (1 + e) * S J = 1 - (-e) ^ J := by
      simp only [S]
      have := geom_sum_mul_neg (-e) J
      rw [mul_comm, show 1 + e = 1 - -e by ring]; exact this
    have e1 : (1 + e) * g - 1 = (1 + e) * (g - S J) + -((-e) ^ J) := by
      rw [mul_sub, hgeom]; ring
    rw [e1]
    refine (T.annNorm_add_le r _ _).trans (max_le ?_ ?_)
    · rw [annNorm_mul, annNorm_sub_comm]
      have h3 := (hJ₁ J (le_max_left _ _)).le
      calc T.annNorm ρ0 σ0 r (1 + e) * T.annNorm ρ0 σ0 r (S J - g) ≤ B * (ε / B) :=
            mul_le_mul (by linarith) h3 (T.annNorm_nonneg _ _) hB.le
        _ = ε := by field_simp
    · rw [annNorm_neg]
      exact (hpow r (Or.inl rfl) J).trans ((pow_le_pow_of_le_one hl0 hl1.le (le_max_right _ _)).trans hJ₂.le)
  · set r := annOut ρ0 σ0
    set B := T.annNorm ρ0 σ0 r (1 + e) + 1
    have hB : 0 < B := by have := T.annNorm_nonneg r (1 + e); positivity
    obtain ⟨J₁, hJ₁⟩ := eventually_atTop.1 ((hg r).eventually (gt_mem_nhds (div_pos hε hB)))
    obtain ⟨J₂, hJ₂⟩ := exists_pow_lt_of_lt_one hε hl1
    set J := max J₁ J₂
    have hgeom : (1 + e) * S J = 1 - (-e) ^ J := by
      simp only [S]
      have := geom_sum_mul_neg (-e) J
      rw [mul_comm, show 1 + e = 1 - -e by ring]; exact this
    have e1 : (1 + e) * g - 1 = (1 + e) * (g - S J) + -((-e) ^ J) := by
      rw [mul_sub, hgeom]; ring
    rw [e1]
    refine (T.annNorm_add_le r _ _).trans (max_le ?_ ?_)
    · rw [annNorm_mul, annNorm_sub_comm]
      have h3 := (hJ₁ J (le_max_left _ _)).le
      calc T.annNorm ρ0 σ0 r (1 + e) * T.annNorm ρ0 σ0 r (S J - g) ≤ B * (ε / B) :=
            mul_le_mul (by linarith) h3 (T.annNorm_nonneg _ _) hB.le
        _ = ε := by field_simp
    · rw [annNorm_neg]
      exact (hpow r (Or.inr rfl) J).trans ((pow_le_pow_of_le_one hl0 hl1.le (le_max_right _ _)).trans hJ₂.le)

theorem isUnit_of_annNorm_sub_lt {u x : T.Ann ρ0 σ0} (hu : IsUnit u)
    (h1 : T.annNorm ρ0 σ0 (annIn ρ0 σ0) (x - u) < T.annNorm ρ0 σ0 (annIn ρ0 σ0) u)
    (h2 : T.annNorm ρ0 σ0 (annOut ρ0 σ0) (x - u) < T.annNorm ρ0 σ0 (annOut ρ0 σ0) u) : IsUnit x := by
  obtain ⟨u', rfl⟩ := hu
  have hx : x = (u' : T.Ann ρ0 σ0) * (1 + ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) * (x - u')) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]; ring
  rw [hx]
  refine u'.isUnit.mul (T.isUnit_one_add_ann _ ?_ ?_)
  · have hn := congrArg (T.annNorm ρ0 σ0 (annIn ρ0 σ0)) (Units.inv_mul u')
    rw [annNorm_mul, annNorm_one] at hn
    have hpos : 0 < T.annNorm ρ0 σ0 (annIn ρ0 σ0) (u' : T.Ann ρ0 σ0) :=
      lt_of_le_of_lt (T.annNorm_nonneg _ _) h1
    rw [annNorm_mul]
    calc T.annNorm ρ0 σ0 (annIn ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) *
          T.annNorm ρ0 σ0 (annIn ρ0 σ0) (x - u')
        < T.annNorm ρ0 σ0 (annIn ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) *
          T.annNorm ρ0 σ0 (annIn ρ0 σ0) (u' : T.Ann ρ0 σ0) := by
          refine mul_lt_mul_of_pos_left h1 ?_
          by_contra h0
          have : T.annNorm ρ0 σ0 (annIn ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) = 0 :=
            le_antisymm (not_lt.1 h0) (T.annNorm_nonneg _ _)
          rw [this, zero_mul] at hn; exact zero_ne_one hn
      _ = 1 := hn
  · have hn := congrArg (T.annNorm ρ0 σ0 (annOut ρ0 σ0)) (Units.inv_mul u')
    rw [annNorm_mul, annNorm_one] at hn
    rw [annNorm_mul]
    calc T.annNorm ρ0 σ0 (annOut ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) *
          T.annNorm ρ0 σ0 (annOut ρ0 σ0) (x - u')
        < T.annNorm ρ0 σ0 (annOut ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) *
          T.annNorm ρ0 σ0 (annOut ρ0 σ0) (u' : T.Ann ρ0 σ0) := by
          refine mul_lt_mul_of_pos_left h2 ?_
          by_contra h0
          have : T.annNorm ρ0 σ0 (annOut ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) = 0 :=
            le_antisymm (not_lt.1 h0) (T.annNorm_nonneg _ _)
          rw [this, zero_mul] at hn; exact zero_ne_one hn
      _ = 1 := hn

def monoB (i : ℤ) (a : L) : T.B := ((T.piB ^ i : T.Bˣ) : T.B) * algebraMap Γ T.B (T.teich a)

theorem coeffB_monoB (i : ℤ) (a : L) : T.coeffB (T.monoB i a) = Pi.single i a := by
  funext n
  rw [monoB, coeffB_piB_zpow_mul, zcoeff_teich]
  by_cases h : n = i
  · subst h; simp
  · rw [Pi.single_apply, if_neg (sub_ne_zero.2 h), Pi.single_apply, if_neg h]

theorem monoB_mul_monoB (i j : ℤ) (a b : L) : T.monoB i a * T.monoB j b = T.monoB (i + j) (a * b) := by
  rw [monoB, monoB, monoB, T.teich_mul, map_mul, zpow_add, Units.val_mul]; ring

theorem monoB_zero_one : T.monoB 0 1 = 1 := by
  rw [monoB, zpow_zero, Units.val_one, T.teich_one, map_one, one_mul]

theorem monoB_mem_Econ (i : ℤ) (a : L) (ρ : Set.Ioo (0 : ℝ) 1) : T.monoB i a ∈ T.Econ ρ := by
  rw [mem_Econ, coeffB_monoB]; exact convergesAt_pi_single _ _ _

theorem gaussNorm_monoB (i : ℤ) (a : L) {s : ℝ} (hs : 0 < s) :
    gaussNorm (T.coeffB (T.monoB i a)) s = ‖a‖ * s ^ i := by
  rw [coeffB_monoB]
  refine le_antisymm (gaussNorm_le fun n => ?_) ?_
  · by_cases h : n = i
    · subst h; simp
    · rw [Pi.single_apply, if_neg h, norm_zero, zero_mul]; positivity
  · have := (convergesAt_pi_single (L := L) i a s).le_gaussNorm i
    simpa using this

theorem coeffB_sub_monoB (b : T.B) (i : ℤ) (hi : T.coeffB b i ≠ 0) :
    T.coeffB (b - T.monoB i (T.coeffB b i)) = Function.update (T.coeffB b) i 0 := by
  classical
  have hX := T.num_spec b
  set N := T.den b
  set X := T.num b
  have hb' := T.coeffB_eq hX
  have hiN : 0 ≤ i + N := by
    by_contra h
    apply hi
    rw [hb']
    exact T.zcoeff_of_neg _ (not_le.1 h)
  set k0 := (i + N).toNat with hk0def
  have hk0 : (k0 : ℤ) = i + N := Int.toNat_of_nonneg hiN
  set a := T.coeffB b i with hadef
  have ha : T.coeff X k0 = a := by
    rw [hadef, hb']; simp only; rw [← hk0, zcoeff_natCast]
  set f : ℕ → L := Function.update (T.coeff X) k0 0
  have hg : T.ofCoeff (Pi.single k0 a) = T.π ^ k0 * T.teich a :=
    T.eq_of_coeff_eq (funext fun n => by
      rw [coeff_ofCoeff, coeff_π_pow_mul_teich, Pi.single_apply])
  have hXf : X = T.ofCoeff f + T.π ^ k0 * T.teich a := by
    rw [← hg, T.ofCoeff_add_of_disjoint (fun n => by
      by_cases h : n = k0
      · left; rw [h]; simp [f]
      · right; rw [Pi.single_apply, if_neg h])]
    conv_lhs => rw [← T.ofCoeff_coeff X]
    congr 1
    funext n
    by_cases h : n = k0
    · subst h; simp [f, ha]
    · simp [f, h]
  have hd : T.monoB i a * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (T.π ^ k0 * T.teich a) := by
    rw [monoB, map_mul, map_pow]
    have e : ((T.piB ^ i : T.Bˣ) : T.B) * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B T.π ^ k0 := by
      rw [← piB_val, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
        ← Units.val_mul, ← zpow_add, ← zpow_natCast, hk0]
    calc ((T.piB ^ i : T.Bˣ) : T.B) * algebraMap Γ T.B (T.teich a) * algebraMap Γ T.B T.π ^ N
        = (((T.piB ^ i : T.Bˣ) : T.B) * algebraMap Γ T.B T.π ^ N) * algebraMap Γ T.B (T.teich a) := by ring
      _ = _ := by rw [e]
  have hsub : (b - T.monoB i a) * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (T.ofCoeff f) := by
    rw [sub_mul, hX, hd, ← map_sub, hXf, add_sub_cancel_right]
  rw [T.coeffB_eq hsub]
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self, ← hk0, zcoeff_natCast, coeff_ofCoeff]
    simp [f]
  · rw [Function.update_of_ne hk, hb']
    simp only
    rcases lt_or_ge (k + N) 0 with hkN | hkN
    · rw [T.zcoeff_of_neg _ hkN, T.zcoeff_of_neg _ hkN]
    · lift k + N to ℕ using hkN with m hm
      rw [zcoeff_natCast, zcoeff_natCast, coeff_ofCoeff]
      have hm' : m ≠ k0 := by
        intro h; apply hk; omega
      simp [f, Function.update_of_ne hm']

theorem gaussNorm_sub_monoB_lt {b : T.B} {s : ℝ} (hs0 : 0 < s) (hb : ConvergesAt (T.coeffB b) s)
    (hb0 : T.coeffB b ≠ 0) (hli : lowIndex (T.coeffB b) s = highIndex (T.coeffB b) s) :
    gaussNorm (T.coeffB (b - T.monoB (lowIndex (T.coeffB b) s) (T.coeffB b (lowIndex (T.coeffB b) s)))) s <
      gaussNorm (T.coeffB b) s := by
  set i := lowIndex (T.coeffB b) s
  have hmem := lowIndex_mem hs0 hb hb0
  have hi : T.coeffB b i ≠ 0 := ne_zero_of_mem_domSet hs0 hb hb0 hmem
  have hpos : 0 < gaussNorm (T.coeffB b) s := gaussNorm_pos hs0 hb hb0
  rw [T.coeffB_sub_monoB b i hi]
  have hconv : ConvergesAt (Function.update (T.coeffB b) i 0) s :=
    (convergesAt_of_norm_le hs0 (fun n => by
      by_cases h : n = i
      · subst h; simp
      · rw [Function.update_of_ne h]) hb).1
  by_cases h0 : Function.update (T.coeffB b) i 0 = 0
  · rw [h0]; simpa [gaussNorm] using hpos
  obtain ⟨j, hj⟩ := hconv.exists_eq_gaussNorm hs0 h0
  rw [← hj]
  have hji : j ≠ i := by
    intro h; subst h
    rw [Function.update_self, norm_zero, zero_mul] at hj
    have := gaussNorm_pos hs0 hconv h0
    linarith
  rw [Function.update_of_ne hji]
  refine lt_of_le_of_ne (hb.le_gaussNorm j) fun heq => hji ?_
  have hjmem : j ∈ domSet (T.coeffB b) s := heq
  exact le_antisymm (hli ▸ le_highIndex hs0 hb hb0 hjmem) (lowIndex_le hs0 hb hb0 hjmem)

theorem coe_ne_zero_of_annNorm_sub_lt {v : T.Ann ρ0 σ0} {c : T.Econ ρ0} (r : AnnRad ρ0 σ0)
    (hc : T.annNorm ρ0 σ0 r (v - T.coeAnn c) < T.annNorm ρ0 σ0 r v) : (c : T.RobbaExt ρ0) ≠ 0 := by
  intro h0
  have hc0 : c = 0 := T.coe_injective_Econ (by rw [h0, Completion.coe_zero])
  rw [hc0, map_zero, sub_zero] at hc
  exact lt_irrefl _ hc

theorem annNorm_eq_of_sub_lt {x y : T.Ann ρ0 σ0} {r : AnnRad ρ0 σ0}
    (h : T.annNorm ρ0 σ0 r (x - y) < T.annNorm ρ0 σ0 r x) :
    T.annNorm ρ0 σ0 r y = T.annNorm ρ0 σ0 r x := by
  have h1 := T.annNorm_sub_le r x (x - y)
  rw [sub_sub_cancel] at h1
  have h2 := T.annNorm_add_le r (x - y) y
  rw [sub_add_cancel] at h2
  apply le_antisymm
  · exact h1.trans (max_le le_rfl h.le)
  · rcases le_max_iff.1 h2 with h3 | h3
    · exact absurd h3 (not_le.2 h)
    · exact h3

theorem isUnit_annRes_of_mult_eq_zero (v : T.Ann ρ0 σ0) (c : T.Econ ρ0)
    (hc : ∀ r, T.annNorm ρ0 σ0 r (v - T.coeAnn c) < T.annNorm ρ0 σ0 r v)
    {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1} (h : (ρ1 : ℝ) < ρ0) (hs : (σ0 : ℝ) ≤ σ1)
    (hm : ∀ s : ℝ, (σ1 : ℝ) ≤ s → s ≤ ρ1 → T.mult (c : T.RobbaExt ρ0) s = 0) :
    IsUnit (T.annRes h.le hs v) := by
  have hc0 : (c : T.RobbaExt ρ0) ≠ 0 := T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hc _)
  have ha : (0 : ℝ) < σ1 := σ1.2.1
  have hab : (σ1 : ℝ) ≤ ρ1 := σ1.2.2

  have hsum := T.sum_mult_breaksR hc0 ha hab h
  have h0 : ∑ ρ ∈ (T.breaksR_finite hc0 ha hab h).toFinset, T.mult (c : T.RobbaExt ρ0) ρ = 0 :=
    Finset.sum_eq_zero fun ρ hρ => by
      simp only [Set.Finite.mem_toFinset, breaksR, Set.mem_ofPred_eq] at hρ
      exact hm ρ hρ.1.1 hρ.1.2
  have hma := hm σ1 le_rfl hab
  have hmb := hm ρ1 hab le_rfl
  rw [mult] at hma hmb
  have hia := T.idx_coe hc0 ⟨ha, hab.trans_lt h⟩
  have hib := T.idx_coe hc0 ⟨ha.trans_le hab, h⟩
  set a := T.coeffB (c : T.B)
  have hA : ConvergesAt a σ1 := T.convergesAt_rad ρ0 c ⟨σ1, ha, hab.trans h.le⟩
  have hB : ConvergesAt a ρ1 := T.convergesAt_rad ρ0 c ⟨ρ1, ha.trans_le hab, h.le⟩
  have ha0 : a ≠ 0 := by
    intro h0'
    apply hc0
    have : (c : T.B) = 0 := by
      obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj T.π (c : T.B)
      have hy0 : y = 0 := by
        refine (T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)
        have := congrFun h0' (k - N)
        rw [show a = T.coeffB (c : T.B) from rfl, T.coeffB_eq hy] at this
        simpa using this
      rw [hy0, map_zero] at hy
      exact T.eq_zero_of_mul_pow hy
    rw [show c = 0 from Subtype.ext this, Completion.coe_zero]
  have e1 : lowIndex a σ1 = highIndex a σ1 := by rw [← hia.1, ← hia.2]; omega
  have e2 : lowIndex a ρ1 = highIndex a ρ1 := by rw [← hib.1, ← hib.2]; omega
  have e3 : lowIndex a ρ1 = lowIndex a σ1 := by rw [← hib.1, ← hia.1]; omega
  set i := lowIndex a σ1
  set d : T.Econ ρ0 := ⟨T.monoB i (a i), T.monoB_mem_Econ _ _ _⟩
  set dinv : T.Econ ρ0 := ⟨T.monoB (-i) (a i)⁻¹, T.monoB_mem_Econ _ _ _⟩
  have hai : a i ≠ 0 := ne_zero_of_mem_domSet ha hA ha0 (lowIndex_mem ha hA ha0)
  have hdd : d * dinv = 1 := Subtype.ext (by
    show T.monoB i (a i) * T.monoB (-i) (a i)⁻¹ = 1
    rw [monoB_mul_monoB, add_neg_cancel, mul_inv_cancel₀ hai, monoB_zero_one])

  have hlt1 := T.gaussNorm_sub_monoB_lt ha hA ha0 e1
  have hlt2 := T.gaussNorm_sub_monoB_lt (ha.trans_le hab) hB ha0 e2
  rw [e3] at hlt2
  have hdn : ∀ s : ℝ, 0 < s → gaussNorm (T.coeffB (d : T.B)) s = ‖a i‖ * s ^ i := fun s hs =>
    T.gaussNorm_monoB i (a i) hs
  have hcn1 : gaussNorm a σ1 = ‖a i‖ * (σ1 : ℝ) ^ i := (lowIndex_mem ha hA ha0).symm
  have hcn2 : gaussNorm a ρ1 = ‖a i‖ * (ρ1 : ℝ) ^ i := by
    have := (lowIndex_mem (ha.trans_le hab) hB ha0).symm
    rw [e3] at this; exact this

  set C := T.annRes h.le hs (T.coeAnn c)
  set D := T.annRes h.le hs (T.coeAnn d)
  have hD : IsUnit D := IsUnit.of_mul_eq_one (T.annRes h.le hs (T.coeAnn dinv)) (by
    rw [← map_mul, ← map_mul, hdd, map_one, map_one])
  have hnC : ∀ r : AnnRad ρ1 σ1, T.annNorm ρ1 σ1 r C = gaussNorm a r := fun r => by
    rw [T.annNorm_annRes, annNorm_coeAnn]; rfl
  have hnD : ∀ r : AnnRad ρ1 σ1, T.annNorm ρ1 σ1 r D = gaussNorm (T.coeffB (d : T.B)) r := fun r => by
    rw [T.annNorm_annRes, annNorm_coeAnn]; rfl
  have hnCD : ∀ r : AnnRad ρ1 σ1, T.annNorm ρ1 σ1 r (C - D) =
      gaussNorm (T.coeffB ((c : T.B) - T.monoB i (a i))) r := fun r => by
    rw [← map_sub, ← map_sub, T.annNorm_annRes, annNorm_coeAnn]; rfl
  have hCu : IsUnit C := by
    refine T.isUnit_of_annNorm_sub_lt hD ?_ ?_
    · rw [hnCD, hnD, coe_annIn, hdn _ ha, ← hcn1]; exact hlt1
    · rw [hnCD, hnD, coe_annOut, hdn _ (ha.trans_le hab), ← hcn2]; exact hlt2
  refine T.isUnit_of_annNorm_sub_lt hCu ?_ ?_
  all_goals
    rw [← map_sub, T.annNorm_annRes, T.annNorm_annRes, annRadOf]
    refine (hc _).trans_le (le_of_eq ?_)
    exact (T.annNorm_eq_of_sub_lt (hc _)).symm

theorem ptEvalB_monoB {ξ : T.int} (hξ : T.IsPrimOne ξ) (i : ℤ) (c : L) :
    ‖T.ptEvalB hξ (T.monoB i c)‖ = ‖c‖ * T.ptRad ξ ^ i := by
  rw [ptEvalB, coeffB_monoB, ptEvalSeq, tsum_eq_single i (fun n hn => by
    rw [ptTerm, Pi.single_apply, if_neg hn, map_zero, mul_zero]), norm_ptTerm, Pi.single_eq_same]

theorem norm_ptEvalB_of_dom {ξ : T.int} (hξ : T.IsPrimOne ξ) {b : T.B}
    (hb : ConvergesAt (T.coeffB b) (T.ptRad ξ)) (hb0 : T.coeffB b ≠ 0)
    (hli : lowIndex (T.coeffB b) (T.ptRad ξ) = highIndex (T.coeffB b) (T.ptRad ξ)) :
    ‖T.ptEvalB hξ b‖ = gaussNorm (T.coeffB b) (T.ptRad ξ) := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  set i := lowIndex (T.coeffB b) (T.ptRad ξ)
  set m := T.monoB i (T.coeffB b i)
  have hmc : ConvergesAt (T.coeffB m) (T.ptRad ξ) := by
    rw [coeffB_monoB]; exact convergesAt_pi_single _ _ _
  have hdc : ConvergesAt (T.coeffB (b - m)) (T.ptRad ξ) := by
    rw [sub_eq_add_neg]
    exact (T.convergesAt_coeffB_add hr0 hr1 hb (T.convergesAt_coeffB_neg hr0 hr1 hmc).1).1
  have hlt := T.gaussNorm_sub_monoB_lt hr0 hb hb0 hli
  have hdom : gaussNorm (T.coeffB b) (T.ptRad ξ) = ‖T.coeffB b i‖ * T.ptRad ξ ^ i :=
    (lowIndex_mem hr0 hb hb0).symm
  have h1 : ‖T.ptEvalB hξ m‖ = gaussNorm (T.coeffB b) (T.ptRad ξ) := by
    rw [T.ptEvalB_monoB hξ, hdom]
  have h2 : ‖T.ptEvalB hξ (b - m)‖ < gaussNorm (T.coeffB b) (T.ptRad ξ) :=
    (T.norm_ptEvalB_le hξ hdc).trans_lt hlt
  have e : b = m + (b - m) := by ring
  rw [e, T.ptEvalB_add hξ hmc hdc, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by rw [h1]; exact h2.ne'), h1, max_eq_left h2.le]
  rw [← e]

theorem norm_ptEval_of_mult_eq_zero {u : T.RobbaExt ρ0} (hu : u ≠ 0) {ξ : T.int} (hξ : T.IsPrimOne ξ)
    (hr : T.ptRad ξ < ρ0) (hm : T.mult u (T.ptRad ξ) = 0) :
    ‖T.ptEval hξ hr.le u‖ = T.extNorm ρ0 (T.ptRadIoc hξ hr.le) u := by
  have h : 0 < T.ptRad ξ ∧ T.ptRad ξ < ρ0 := ⟨T.ptRad_pos' hξ, hr⟩
  have hc := T.approx_spec hu h (T.ptRadIoc hξ hr.le) le_rfl (mid_rad h).2.2.le
  have hl := T.lowIdx_eq_approx hu h
  have hh := T.highIdx_eq_approx hu h
  rw [mult, hh, hl] at hm
  set c := T.approx hu h
  have hc0 : (c : T.B) ≠ 0 := T.coe_ne_zero_of_approx hc
  have hcoeff0 : T.coeffB (c : T.B) ≠ 0 := by
    intro h0
    obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj T.π (c : T.B)
    have hy0 : y = 0 := by
      refine (T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)
      have := congrFun h0 (k - N)
      rw [T.coeffB_eq hy] at this
      simpa using this
    rw [hy0, map_zero] at hy
    exact hc0 (T.eq_zero_of_mul_pow hy)
  have hcv : ConvergesAt (T.coeffB (c : T.B)) (T.ptRad ξ) := T.convergesAt_rad ρ0 c (T.ptRadIoc hξ hr.le)
  have h1 : ‖T.ptEval hξ hr.le (c : T.RobbaExt ρ0)‖ = T.extNorm ρ0 (T.ptRadIoc hξ hr.le) u := by
    rw [ptEval_coe, T.norm_ptEvalB_of_dom hξ hcv hcoeff0 (by omega), ← T.extNorm_eq_of_lt hc,
      extNorm_coe]
    rfl
  have h2 : ‖T.ptEval hξ hr.le (u - c)‖ < T.extNorm ρ0 (T.ptRadIoc hξ hr.le) u :=
    (T.norm_ptEval_le hξ hr.le _).trans_lt hc
  have e : u = (c : T.RobbaExt ρ0) + (u - c) := by ring
  rw [e, map_add, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2.ne'), h1,
    max_eq_left h2.le, ← e]

def annLogNorm (q : T.Ann ρ0 σ0) (t : ℝ) : ℝ := Real.log (T.annNormR q (Real.exp t))

theorem annLogNorm_of_mem (q : T.Ann ρ0 σ0) (r : AnnRad ρ0 σ0) :
    T.annLogNorm q (Real.log r) = Real.log (T.annNorm ρ0 σ0 r q) := by
  rw [annLogNorm, Real.exp_log (σ0.2.1.trans_le r.2.1), T.annNormR_of_mem q r]

theorem exp_mem_of_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (Real.log σ0) (Real.log ρ0)) :
    Real.exp t ∈ Set.Icc (σ0 : ℝ) ρ0 := by
  constructor
  · rw [← Real.exp_log σ0.2.1]; exact Real.exp_le_exp.2 ht.1
  · rw [← Real.exp_log ρ0.2.1]; exact Real.exp_le_exp.2 ht.2

theorem convexOn_annLogNorm (q : T.Ann ρ0 σ0) (hq : ∀ r, 0 < T.annNorm ρ0 σ0 r q) :
    ConvexOn ℝ (Set.Icc (Real.log σ0) (Real.log ρ0)) (T.annLogNorm q) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  set r₁ : AnnRad ρ0 σ0 := ⟨Real.exp x, exp_mem_of_mem_Icc hx⟩
  set r₂ : AnnRad ρ0 σ0 := ⟨Real.exp y, exp_mem_of_mem_Icc hy⟩
  have hz : a • x + b • y ∈ Set.Icc (Real.log σ0) (Real.log ρ0) := (convex_Icc _ _) hx hy ha hb hab
  set r : AnnRad ρ0 σ0 := ⟨Real.exp (a • x + b • y), exp_mem_of_mem_Icc hz⟩
  have hr : (r : ℝ) = (r₁ : ℝ) ^ (1 - b) * (r₂ : ℝ) ^ b := by
    show Real.exp (a • x + b • y) = Real.exp x ^ (1 - b) * Real.exp y ^ b
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, smul_eq_mul, smul_eq_mul,
      show 1 - b = a by linarith]
    ring_nf
  have hi := T.annNorm_interp_le r₁ r₂ r (by linarith) (by linarith) hr q
  have h1 := hq r₁
  have h2 := hq r₂
  have hlog := Real.log_le_log (hq r) hi
  rw [Real.log_mul (Real.rpow_pos_of_pos h1 _).ne' (Real.rpow_pos_of_pos h2 _).ne',
    Real.log_rpow h1, Real.log_rpow h2, show 1 - b = a by linarith] at hlog
  simp only [smul_eq_mul]
  have e1 : T.annLogNorm q x = Real.log (T.annNorm ρ0 σ0 r₁ q) := by
    rw [annLogNorm, T.annNormR_of_mem q r₁]
  have e2 : T.annLogNorm q y = Real.log (T.annNorm ρ0 σ0 r₂ q) := by
    rw [annLogNorm, T.annNormR_of_mem q r₂]
  have e3 : T.annLogNorm q (a • x + b • y) = Real.log (T.annNorm ρ0 σ0 r q) := by
    rw [annLogNorm, T.annNormR_of_mem q r]
  rw [smul_eq_mul, smul_eq_mul] at e3
  rw [e1, e2, e3]
  linarith

theorem slope_le_slope_of_convexOn {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {a b c d : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    (f b - f a) / (b - a) ≤ (f d - f c) / (d - c) := by
  rcases eq_or_lt_of_le hbc with h | h
  · subst h
    exact hf.slope_mono_adjacent ha hd hab hcd
  · exact (hf.slope_mono_adjacent ha hc hab h).trans (hf.slope_mono_adjacent hb hd h hcd)

theorem annNorm_list_prod_ξAnn (l : List T.Pt) (r : AnnRad ρ0 σ0) :
    T.annNorm ρ0 σ0 r (l.map fun P => T.ξAnn P.1).prod =
      (l.map fun P => max (T.ptRad P.1) (r : ℝ)).prod := by
  induction l with
  | nil => simp [annNorm_one]
  | cons P l ih => rw [List.map_cons, List.prod_cons, annNorm_mul, T.annNorm_ξAnn P.2, ih,
      List.map_cons, List.prod_cons]

theorem list_prod_max_eq_left (l : List T.Pt) {s : ℝ} (h : ∀ P ∈ l, s ≤ T.ptRad P.1) :
    (l.map fun P => max (T.ptRad P.1) s).prod = (l.map fun P => T.ptRad P.1).prod := by
  induction l with
  | nil => rfl
  | cons P l ih =>
    rw [List.map_cons, List.prod_cons, max_eq_left (h P List.mem_cons_self),
      ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)]; rfl

theorem list_prod_max_eq_right (l : List T.Pt) {s : ℝ} (h : ∀ P ∈ l, T.ptRad P.1 ≤ s) :
    (l.map fun P => max (T.ptRad P.1) s).prod = s ^ l.length := by
  induction l with
  | nil => simp
  | cons P l ih =>
    rw [List.map_cons, List.prod_cons, max_eq_right (h P List.mem_cons_self),
      ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ), List.length_cons, pow_succ]; ring


theorem length_le_of_prod_dvd (w : T.Ann ρ0 σ0) (hw : ∀ r, 0 < T.annNorm ρ0 σ0 r w)
    (a b c d : AnnRad ρ0 σ0) (hab : (a : ℝ) < b) (hbc : (b : ℝ) ≤ c) (hcd : (c : ℝ) < d)
    (l : List T.Pt) (hl : ∀ P ∈ l, (b : ℝ) ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ c)
    (hdvd : (l.map fun P => T.ξAnn P.1).prod ∣ w) :
    (l.length : ℝ) ≤
      (Real.log (T.annNorm ρ0 σ0 d w) - Real.log (T.annNorm ρ0 σ0 c w)) / (Real.log d - Real.log c) -
      (Real.log (T.annNorm ρ0 σ0 b w) - Real.log (T.annNorm ρ0 σ0 a w)) / (Real.log b - Real.log a) := by
  obtain ⟨q, hq⟩ := hdvd
  set P := (l.map fun P => T.ξAnn P.1).prod
  have hpos : ∀ r : AnnRad ρ0 σ0, 0 < T.annNorm ρ0 σ0 r P := fun r => by
    rw [T.annNorm_list_prod_ξAnn]
    exact List.prod_pos fun x hx => by
      obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
      exact lt_of_lt_of_le (T.ptRad_pos' Q.2) (le_max_left _ _)
  have hqpos : ∀ r, 0 < T.annNorm ρ0 σ0 r q := fun r => by
    have h := hw r
    rw [hq, annNorm_mul] at h
    exact pos_of_mul_pos_right h (hpos r).le
  have hnw : ∀ r : AnnRad ρ0 σ0, Real.log (T.annNorm ρ0 σ0 r w) =
      Real.log (T.annNorm ρ0 σ0 r P) + Real.log (T.annNorm ρ0 σ0 r q) := fun r => by
    rw [hq, annNorm_mul, Real.log_mul (hpos r).ne' (hqpos r).ne']
  have hPa : T.annNorm ρ0 σ0 a P = (l.map fun P => T.ptRad P.1).prod := by
    rw [T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_left l fun Q hQ => hab.le.trans (hl Q hQ).1]
  have hPb : T.annNorm ρ0 σ0 b P = (l.map fun P => T.ptRad P.1).prod := by
    rw [T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_left l fun Q hQ => (hl Q hQ).1]
  have hPc : T.annNorm ρ0 σ0 c P = (c : ℝ) ^ l.length := by
    rw [T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_right l fun Q hQ => (hl Q hQ).2]
  have hPd : T.annNorm ρ0 σ0 d P = (d : ℝ) ^ l.length := by
    rw [T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_right l fun Q hQ => (hl Q hQ).2.trans hcd.le]
  have hmem : ∀ r : AnnRad ρ0 σ0, Real.log r ∈ Set.Icc (Real.log σ0) (Real.log ρ0) := fun r =>
    ⟨Real.log_le_log σ0.2.1 r.2.1, Real.log_le_log (σ0.2.1.trans_le r.2.1) r.2.2⟩
  have hc0 : (0 : ℝ) < c := σ0.2.1.trans_le c.2.1
  have hd0 : (0 : ℝ) < d := σ0.2.1.trans_le d.2.1
  have ha0 : (0 : ℝ) < a := σ0.2.1.trans_le a.2.1
  have hb0 : (0 : ℝ) < b := σ0.2.1.trans_le b.2.1
  have hlab : Real.log a < Real.log b := Real.log_lt_log ha0 hab
  have hlbc : Real.log b ≤ Real.log c := Real.log_le_log hb0 hbc
  have hlcd : Real.log c < Real.log d := Real.log_lt_log hc0 hcd
  have key := slope_le_slope_of_convexOn (T.convexOn_annLogNorm q hqpos) (hmem a) (hmem b) (hmem c)
    (hmem d) hlab hlbc hlcd
  rw [T.annLogNorm_of_mem, T.annLogNorm_of_mem, T.annLogNorm_of_mem, T.annLogNorm_of_mem] at key
  rw [hnw a, hnw b, hnw c, hnw d, hPa, hPb, hPc, hPd, Real.log_pow, Real.log_pow]
  have e1 : (Real.log (l.map fun P => T.ptRad P.1).prod + Real.log (T.annNorm ρ0 σ0 b q) -
      (Real.log (l.map fun P => T.ptRad P.1).prod + Real.log (T.annNorm ρ0 σ0 a q))) /
      (Real.log b - Real.log a) =
      (Real.log (T.annNorm ρ0 σ0 b q) - Real.log (T.annNorm ρ0 σ0 a q)) / (Real.log b - Real.log a) := by
    congr 1; ring
  have e2 : ((l.length : ℝ) * Real.log d + Real.log (T.annNorm ρ0 σ0 d q) -
      ((l.length : ℝ) * Real.log c + Real.log (T.annNorm ρ0 σ0 c q))) / (Real.log d - Real.log c) =
      l.length + (Real.log (T.annNorm ρ0 σ0 d q) - Real.log (T.annNorm ρ0 σ0 c q)) /
        (Real.log d - Real.log c) := by
    have hne : Real.log d - Real.log c ≠ 0 := by linarith
    field_simp
    ring
  rw [e1, e2]
  linarith

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0} [CompleteSpace L] [IsAlgClosed L]

theorem mult_ptProd (l : List T.Pt) {r : ℝ} (hr : 0 < r ∧ r < ρ0) (hl : ∀ P ∈ l, T.ptRad P.1 = r) :
    T.mult (T.ptProd ρ0 l) r = l.length := by
  induction l with
  | nil =>
    rw [ptProd_nil, T.mult_one hr]; rfl
  | cons P l ih =>
    rw [ptProd_cons, T.mult_mul (T.ptExt_ne_zero P.2) (T.ptProd_ne_zero l) hr,
      T.mult_ptExt P.2 hr, if_pos (hl P List.mem_cons_self).symm,
      ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ), List.length_cons]
    push_cast; ring

theorem extNorm_ptProd (l : List T.Pt) (s : Set.Ioc (0 : ℝ) ρ0) (hl : ∀ P ∈ l, T.ptRad P.1 ≤ s) :
    T.extNorm ρ0 s (T.ptProd ρ0 l) = (s : ℝ) ^ l.length := by
  induction l with
  | nil => rw [ptProd_nil, extNorm_one]; simp
  | cons P l ih =>
    rw [ptProd_cons, extNorm_mul, T.extNorm_ξExt P.2, max_eq_right (hl P List.mem_cons_self),
      ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ), List.length_cons, pow_succ]; ring

def intEval {ξ : T.int} (hξ : T.IsPrimOne ξ) : T.int →+* T.UntiltField hξ :=
  (T.toUntiltField hξ).comp (T.toUntilt ξ)

theorem intEval_apply {ξ : T.int} (hξ : T.IsPrimOne ξ) (X : T.int) :
    T.intEval hξ X = T.ptE hξ (X : Γ) := (T.ptE_int hξ X.2).symm

theorem norm_intEval_le_one {ξ : T.int} (hξ : T.IsPrimOne ξ) (X : T.int) : ‖T.intEval hξ X‖ ≤ 1 := by
  rw [intEval, RingHom.comp_apply, norm_toUntiltField]; exact T.untiltNorm_le_one hξ _

theorem exists_step_pt {P Q : T.Pt} {δ : ℝ} (hrad : T.ptRad Q.1 = T.ptRad P.1) (hδ : δ < T.ptRad P.1)
    (hv : ‖T.ptE P.2 (Q.1 : Γ)‖ ≤ δ) :
    ∃ (q : T.int) (z : L) (V : Γ), IsUnit q ∧ ‖z‖ ≤ δ ∧ V ∈ T.int ∧
      (Q.1 : Γ) = P.1 * q + T.teich z * V := by
  have hr1 := T.ptRad_lt_one' P.2
  have hw1 : ‖T.ptE P.2 (Q.1 : Γ)‖ ≤ 1 := hv.trans (hδ.trans hr1).le
  obtain ⟨z, hz, V, hV, hzV⟩ := T.exists_lift_value P.2 hw1
  have hz1 : ‖z‖ ≤ 1 := hz ▸ hw1
  set W : T.int := ⟨T.teich z * V, T.int.mul_mem (T.teich_mem_int hz1) hV⟩
  have h0 : T.toUntilt P.1 (Q.1 - W) = 0 := by
    rw [← T.toUntiltField_eq_zero_iff P]
    change T.intEval P.2 (Q.1 - W) = 0
    rw [map_sub, intEval_apply, intEval_apply]
    show T.ptE P.2 (Q.1 : Γ) - T.ptE P.2 (T.teich z * V) = 0
    rw [hzV, sub_self]
  obtain ⟨B, hB, hQB⟩ := (T.toUntilt_eq_zero_iff).1 h0
  refine ⟨⟨B, hB⟩, z, V, ?_, hz ▸ hv, hV, ?_⟩
  · rw [T.isUnit_int_iff]
    have hred : T.red (Q.1 : Γ) = T.red (P.1 : Γ) * T.red B + z * T.red V := by
      have : (Q.1 : Γ) = P.1 * B + T.teich z * V := by
        have h := hQB
        simp only [AddSubgroupClass.coe_sub] at h
        rw [show (W : Γ) = T.teich z * V from rfl] at h
        linear_combination h
      rw [this, map_add, map_mul, map_mul, red_teich]
    have hQ : ‖T.red (Q.1 : Γ)‖ = T.ptRad P.1 := by rw [← coeff_zero, ← hrad]; rfl
    have hP : ‖T.red (P.1 : Γ)‖ = T.ptRad P.1 := by rw [← coeff_zero]; rfl
    have hzV' : ‖z * T.red V‖ < T.ptRad P.1 := by
      rw [norm_mul]
      calc ‖z‖ * ‖T.red V‖ ≤ δ * 1 :=
            mul_le_mul (hz ▸ hv) (T.norm_red_le_one V hV) (norm_nonneg _) ((norm_nonneg _).trans (hz ▸ hv))
        _ < T.ptRad P.1 := by rw [mul_one]; exact hδ
    have hPB : ‖T.red (P.1 : Γ) * T.red B‖ = T.ptRad P.1 := by
      have e : T.red (P.1 : Γ) * T.red B = T.red (Q.1 : Γ) - z * T.red V := by rw [hred]; ring
      rw [e, ultra_norm_sub_eq_left (by rw [hQ]; exact hzV'), hQ]
    rw [norm_mul, hP] at hPB
    have hr0 := T.ptRad_pos' P.2
    field_simp at hPB
    linarith [hPB]
  · have h := hQB
    simp only [AddSubgroupClass.coe_sub] at h
    rw [show (W : Γ) = T.teich z * V from rfl] at h
    show (Q.1 : Γ) = P.1 * B + T.teich z * V
    linear_combination h

theorem exists_limit_pt {r : ℝ} (ξ : ℕ → T.int) (hξ : ∀ J, T.IsPrimOne (ξ J)) (hr : ∀ J, T.ptRad (ξ J) = r)
    (q : ℕ → T.int) (hq : ∀ J, IsUnit (q J)) (z : ℕ → L) (V : ℕ → Γ) (hV : ∀ J, V J ∈ T.int)
    (hstep : ∀ J, ((ξ (J + 1) : T.int) : Γ) = ξ J * q J + T.teich (z J) * V J)
    (B : ℕ → ℝ) (hBanti : Antitone B) (hBlim : Tendsto B atTop (𝓝 0)) (hzB : ∀ J, ‖z J‖ ≤ B J)
    (hBr : B 0 < r ^ 2) :
    ∃ (η : T.int) (hη : T.IsPrimOne η), T.ptRad η = r ∧
      Tendsto (fun J => ‖T.ptE hη ((ξ J : T.int) : Γ)‖) atTop (𝓝 0) := by
  have hr0 : 0 < r := hr 0 ▸ T.ptRad_pos' (hξ 0)
  have hr1 : r < 1 := hr 0 ▸ T.ptRad_lt_one' (hξ 0)
  have hB0 : ∀ J, 0 ≤ B J := fun J => (norm_nonneg _).trans (hzB J)

  set u : ℕ → (T.int)ˣ := fun J => ∏ i ∈ Finset.range J, (hq i).unit with hudef
  have hu0 : u 0 = 1 := by simp [hudef]
  have husucc : ∀ J, u (J + 1) = u J * (hq J).unit := fun J => by simp [hudef, Finset.prod_range_succ]
  set η : ℕ → Γ := fun J => (ξ J : Γ) * ((((u J)⁻¹ : (T.int)ˣ) : T.int) : Γ) with hηdef
  have hηint : ∀ J, η J ∈ T.int := fun J => T.int.mul_mem (ξ J).2 (((u J)⁻¹ : (T.int)ˣ) : T.int).2
  set W : ℕ → Γ := fun J => V J * ((((u (J + 1))⁻¹ : (T.int)ˣ) : T.int) : Γ) with hWdef
  have hWint : ∀ J, W J ∈ T.int := fun J => T.int.mul_mem (hV J) (((u (J + 1))⁻¹ : (T.int)ˣ) : T.int).2
  have hdiff : ∀ J, η (J + 1) - η J = T.teich (z J) * W J := by
    intro J
    have h1 : ((((u (J + 1))⁻¹ : (T.int)ˣ) : T.int) : Γ) =
        ((((u J)⁻¹ : (T.int)ˣ) : T.int) : Γ) * (((((hq J).unit)⁻¹ : (T.int)ˣ) : T.int) : Γ) := by
      rw [husucc, mul_inv_rev, Units.val_mul, Subring.coe_mul, mul_comm]
    have h2 : ((q J : T.int) : Γ) * (((((hq J).unit)⁻¹ : (T.int)ˣ) : T.int) : Γ) = 1 := by
      rw [← Subring.coe_mul]
      have : (q J : T.int) * ((((hq J).unit)⁻¹ : (T.int)ˣ) : T.int) = 1 := (hq J).mul_val_inv
      rw [this]; rfl
    simp only [hηdef, hWdef, hstep J, h1]
    linear_combination ((ξ J : Γ) * ((((u J)⁻¹ : (T.int)ˣ) : T.int) : Γ)) * h2
  have hconv : ∀ X : Γ, X ∈ T.int → ConvergesAt (T.zcoeff X) r := fun X hX =>
    T.convergesAt_of_mem_int hX hr0 hr1
  have hinc : ∀ J, gaussNorm (T.zcoeff (η (J + 1) - η J)) r ≤ B J := by
    intro J
    rw [hdiff J]
    exact (T.gaussNorm_teich_mul_int_le (hWint J) hr0 hr1).trans (hzB J)
  have hbound : ∀ J K, J ≤ K → gaussNorm (T.zcoeff (η K - η J)) r ≤ B J := by
    intro J K hJK
    induction K, hJK using Nat.le_induction with
    | base => rw [sub_self, (T.zcoeff_eq_zero_iff 0).2 rfl]; simpa [gaussNorm] using hB0 J
    | succ K hK ih =>
      have e : η (K + 1) - η J = (η (K + 1) - η K) + (η K - η J) := by ring
      rw [e]
      refine (T.gaussNorm_zcoeff_add_le hr0 hr1.le (hconv _ (sub_mem (hηint _) (hηint _)))
        (hconv _ (sub_mem (hηint _) (hηint _)))).trans (max_le ((hinc K).trans (hBanti hK)) ih)
  have hsymm : ∀ J K, gaussNorm (T.zcoeff (η K - η J)) r ≤ B (min J K) := by
    intro J K
    rcases le_total J K with h | h
    · rw [min_eq_left h]; exact hbound J K h
    · rw [min_eq_right h, ← neg_sub, T.gaussNorm_zcoeff_neg hr0 hr1 (hconv _ (sub_mem (hηint _) (hηint _)))]
      exact hbound K J h
  obtain ⟨hcoef, hLconv, hlim⟩ := T.exists_limit_gaussNorm hr0 hr1 (x := η) (fun k => hconv _ (hηint k))
    (fun ε hε => by
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hBlim.eventually (ge_mem_nhds hε))
      exact ⟨N, fun k hk l hl => by
        rw [← neg_sub, T.gaussNorm_zcoeff_neg hr0 hr1 (hconv _ (sub_mem (hηint _) (hηint _)))]
        exact (hsymm k l).trans (hN _ (le_min hk hl))⟩)
  set ηL := T.coeffLim η
  have hLint : ηL ∈ T.int := T.mem_int_iff.2 fun n =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (T.tendsto_coeff_coeffLim hcoef n))
      (Eventually.of_forall fun k => T.mem_int_iff.1 (hηint k) n)
  set Y : Γ := η 0 - ηL
  have hYint : Y ∈ T.int := sub_mem (hηint 0) hLint
  have hYg : gaussNorm (T.zcoeff Y) r ≤ B 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := hlim ε hε
    have e : Y = (η 0 - η N) + (η N - ηL) := by simp only [Y]; ring
    rw [e]
    refine (T.gaussNorm_zcoeff_add_le hr0 hr1.le (hconv _ (sub_mem (hηint _) (hηint _)))
      (hconv _ (sub_mem (hηint _) hLint))).trans (max_le ?_ ?_)
    · rw [← neg_sub, T.gaussNorm_zcoeff_neg hr0 hr1 (hconv _ (sub_mem (hηint _) (hηint _)))]
      exact (hbound 0 N (Nat.zero_le _)).trans (le_add_of_nonneg_right hε.le)
    · exact (hN N le_rfl).trans (le_add_of_nonneg_left (hB0 0))
  have hweight : ∀ m : ℕ, ‖T.coeff Y m‖ * r ^ m ≤ B 0 := fun m => by
    have := (hconv Y hYint).le_gaussNorm m
    rw [zcoeff_natCast, zpow_natCast] at this
    exact this.trans hYg
  have hpre := T.prefixLe_of_weight hr0 hr1.le hweight 1
  rw [pow_one] at hpre
  have hδ0 : 0 ≤ B 0 / r := div_nonneg (hB0 0) hr0.le
  have hδ : B 0 / r < T.ptRad (ξ 0) := by
    rw [hr 0, div_lt_iff₀ hr0]; nlinarith
  have hη0 : η 0 = (ξ 0 : Γ) := by simp [hηdef, hu0]
  obtain ⟨hηL, hradL⟩ := T.isPrimOne_sub_of_prefix (hξ 0) (Y := ⟨Y, hYint⟩) hδ0 hδ hpre
  set ηp : T.int := ξ 0 - ⟨Y, hYint⟩
  have hηp : (ηp : Γ) = ηL := by
    show (ξ 0 : Γ) - Y = ηL
    simp only [Y, hη0]; ring
  refine ⟨ηp, hηL, hradL.trans (hr 0), ?_⟩

  have hval : ∀ J, ‖T.ptE hηL ((ξ J : T.int) : Γ)‖ ≤ gaussNorm (T.zcoeff (η J - ηL)) r := by
    intro J
    have hξJ : ξ J = ⟨η J, hηint J⟩ * ((u J : (T.int)ˣ) : T.int) := Subtype.ext (by
      simp only [hηdef, Subring.coe_mul]
      rw [mul_assoc, ← Subring.coe_mul, Units.inv_mul]; simp)
    have hη : (⟨η J, hηint J⟩ : T.int) = ηp + ⟨η J - ηL, sub_mem (hηint J) hLint⟩ :=
      Subtype.ext (by simp only [Subring.coe_add, hηp]; ring)
    rw [← intEval_apply, hξJ, map_mul, norm_mul, hη, map_add, intEval_apply, intEval_apply]
    rw [show ((ηp : T.int) : Γ) = ηp from rfl, T.ptE_ξ hηL, zero_add]
    refine (mul_le_of_le_one_right (norm_nonneg _) (T.norm_intEval_le_one hηL _)).trans ?_
    refine (T.norm_ptE_le hηL ?_).trans ?_
    · rw [hradL, hr 0]; exact hconv _ (sub_mem (hηint J) hLint)
    · rw [hradL, hr 0]
  refine squeeze_zero (fun J => norm_nonneg _) hval ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hlim (ε / 2) (half_pos hε)
  refine ⟨N, fun J hJ => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (gaussNorm_nonneg hr0)]
  exact (hN J hJ).trans_lt (half_lt_self hε)

theorem mult_eq_of_approx_ann {v : T.Ann ρ0 σ0} {c c' : T.Econ ρ0}
    (hc : ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn c) < T.annNorm ρ0 σ0 s v)
    (hc' : ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn c') < T.annNorm ρ0 σ0 s v) {r : ℝ} (hr : (σ0 : ℝ) < r)
    (hrρ : r < ρ0) : T.mult (c : T.RobbaExt ρ0) r = T.mult (c' : T.RobbaExt ρ0) r := by
  have hc0 := T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hc _)
  have hc'0 := T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hc' _)
  have hr0 : 0 < r := σ0.2.1.trans hr
  have key : ∀ σ : Set.Ioc (0 : ℝ) ρ0, r ≤ σ → (σ : ℝ) ≤ ρ0 →
      gaussNorm (T.coeffB ((c' : T.B) - c)) σ < gaussNorm (T.coeffB (c : T.B)) σ := by
    intro σ h1 h2
    set s : AnnRad ρ0 σ0 := ⟨σ, hr.le.trans h1, h2⟩
    have e1 : gaussNorm (T.coeffB ((c' : T.B) - c)) σ = T.annNorm ρ0 σ0 s (T.coeAnn c' - T.coeAnn c) := by
      rw [← map_sub, annNorm_coeAnn]; rfl
    have e2 : gaussNorm (T.coeffB (c : T.B)) σ = T.annNorm ρ0 σ0 s (T.coeAnn c) := by
      rw [annNorm_coeAnn]
    rw [e1, e2, T.annNorm_eq_of_sub_lt (hc s)]
    have e3 : T.coeAnn c' - T.coeAnn c = (v - T.coeAnn c) - (v - T.coeAnn c') := by ring
    rw [e3]
    exact (T.annNorm_sub_le s _ _).trans_lt (max_lt (hc s) (hc' s))
  obtain ⟨hl, hh⟩ := T.idx_eq_of_lt (c := c) (c' := c') hr0 hrρ le_rfl key
  have h : 0 < r ∧ r < ρ0 := ⟨hr0, hrρ⟩
  rw [mult, mult, (T.idx_coe hc0 h).1, (T.idx_coe hc0 h).2, (T.idx_coe hc'0 h).1, (T.idx_coe hc'0 h).2,
    hl, hh]

theorem exists_lt_of_prod_lt {ι : Type*} (l : List ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {t : ℝ} (ht : 0 ≤ t)
    (h : (l.map f).prod < t ^ l.length) : ∃ i ∈ l, f i < t := by
  by_contra hcon
  push Not at hcon
  have : t ^ l.length ≤ (l.map f).prod := by
    clear h
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ, mul_comm]
      exact mul_le_mul (hcon a List.mem_cons_self) (ih fun i hi => hcon i (List.mem_cons_of_mem _ hi))
        (pow_nonneg ht _) (hf a)
  linarith

theorem ptEval_ptProd_eq_zero_of_mem {l : List T.Pt} {P : T.Pt} (hP : P ∈ l) (hr : T.ptRad P.1 ≤ ρ0) :
    T.ptEval P.2 hr (T.ptProd ρ0 l) = 0 := by
  rw [ptProd, map_list_prod]
  exact List.prod_eq_zero (List.mem_map.2 ⟨T.ξExt P.1 ρ0, List.mem_map.2 ⟨P, hP, rfl⟩,
    T.ptEval_ξExt P.2 hr⟩)

theorem ptEval_ξExt_eq_ptE (P : T.Pt) (hr : T.ptRad P.1 ≤ ρ0) (Q : T.int) :
    T.ptEval P.2 hr (T.ξExt Q ρ0) = T.ptE P.2 (Q : Γ) := by
  rw [T.ptEval_ξExt_eq P hr Q, T.ptE_int P.2 Q.2]

set_option maxHeartbeats 1600000 in

theorem exists_zero_ann (v : T.Ann ρ0 σ0) (hv : ∀ s, 0 < T.annNorm ρ0 σ0 s v) (r : AnnRad ρ0 σ0)
    (hr0 : (σ0 : ℝ) < r) (hr1 : (r : ℝ) < ρ0) (c0 : T.Econ ρ0)
    (hc0 : ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn c0) < T.annNorm ρ0 σ0 s v)
    (hm : 1 ≤ T.mult (c0 : T.RobbaExt ρ0) r) :
    ∃ (ξ : T.int) (hξ : T.IsPrimOne ξ) (hrad : T.ptRad ξ = r),
      T.annEval hξ (by rw [hrad]; exact r.2) v = 0 := by
  classical
  set m : ℕ := (T.mult (c0 : T.RobbaExt ρ0) r).toNat with hmdef
  have hm' : (m : ℤ) = T.mult (c0 : T.RobbaExt ρ0) r := Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ m := by omega
  set R : ℝ := (r : ℝ) with hRdef
  have hR0 : 0 < R := σ0.2.1.trans hr0
  have hR1 : R < 1 := hr1.trans ρ0.2.2
  set Nr := T.annNorm ρ0 σ0 r v with hNrdef
  have hNr : 0 < Nr := hv r
  obtain ⟨μ, hμ, hμle⟩ := T.exists_pos_le_annNorm v hv

  set t : ℕ → ℝ := fun J => R ^ 2 / 2 * (1 / 2) ^ J with htdef
  have ht0 : ∀ J, 0 < t J := fun J => by simp only [htdef]; positivity
  have htR : ∀ J, t J < R := by
    intro J
    have h1 : (1 / 2 : ℝ) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc t J ≤ R ^ 2 / 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ < R := by nlinarith
  have htanti : Antitone t := fun J K hJK => by
    simp only [htdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hJK) (by positivity)
  have htlim : Tendsto t atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (R ^ 2 / 2)
    rwa [mul_zero] at this
  set ε : ℕ → ℝ := fun J => Nr * (t J / R) ^ m with hεdef
  have hε0 : ∀ J, 0 < ε J := fun J => mul_pos hNr (pow_pos (div_pos (ht0 J) hR0) m)
  have hεanti : Antitone ε := fun J K hJK => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg (ht0 K).le hR0.le) (div_le_div_of_nonneg_right (htanti hJK) hR0.le) m)
    hNr.le
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun J => t J / R) atTop (𝓝 0) := by simpa using htlim.div_const R
    have h2 := (h1.pow m).const_mul Nr
    rwa [zero_pow (by omega), mul_zero] at h2
  have hεt : ∀ J, ε J * R ^ m / Nr = t J ^ m := fun J => by
    simp only [hεdef]; field_simp; rw [div_pow]; field_simp

  have happ : ∀ J, ∃ c : T.Econ ρ0, ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn c) < min (ε J) (μ / 2) :=
    fun J => T.exists_coeAnn_near v (lt_min (hε0 J) (half_pos hμ))
  choose c hc using happ
  have hgood : ∀ J s, T.annNorm ρ0 σ0 s (v - T.coeAnn (c J)) < T.annNorm ρ0 σ0 s v := fun J s =>
    (hc J s).trans_le ((min_le_right _ _).trans ((half_le_self hμ.le).trans (hμle s)))
  have hcε : ∀ J s, T.annNorm ρ0 σ0 s (v - T.coeAnn (c J)) < ε J := fun J s =>
    (hc J s).trans_le (min_le_left _ _)
  have hc0' : ∀ J, (c J : T.RobbaExt ρ0) ≠ 0 := fun J =>
    T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hgood J _)
  have hmJ : ∀ J, T.mult (c J : T.RobbaExt ρ0) R = m := fun J => by
    rw [hm']; exact (T.mult_eq_of_approx_ann hc0 (hgood J) hr0 hr1).symm

  have hfac : ∀ J, ∃ (l : List T.Pt) (y : T.RobbaExt ρ0),
      (∀ P ∈ l, R ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ R) ∧ (c J : T.RobbaExt ρ0) = T.ptProd ρ0 l * y ∧ y ≠ 0 ∧
        ∀ σ, R ≤ σ → σ ≤ R → T.mult y σ = 0 := fun J =>
    T.exists_factor_annulus T.rootExists hR0 le_rfl hr1 (hc0' J)
  choose l y hl hcy hy0 hym using hfac
  have hlrad : ∀ J, ∀ P ∈ l J, T.ptRad P.1 = R := fun J P hP => le_antisymm (hl J P hP).2 (hl J P hP).1
  have hlen : ∀ J, (l J).length = m := by
    intro J
    have h := hmJ J
    rw [hcy J, T.mult_mul (T.ptProd_ne_zero _) (hy0 J) ⟨hR0, hr1⟩, T.mult_ptProd _ ⟨hR0, hr1⟩ (hlrad J),
      hym J R le_rfl le_rfl, add_zero] at h
    exact_mod_cast h

  have hrIoc : ∀ {ξ : T.int} (hξ : T.IsPrimOne ξ) (hrad : T.ptRad ξ = R),
      T.ptRadIoc hξ (hrad.trans_le hr1.le) = annIoc r := fun hξ hrad => Subtype.ext hrad
  have hnc : ∀ J, T.extNorm ρ0 (annIoc r) (c J : T.RobbaExt ρ0) = Nr := by
    intro J
    rw [← annNorm_toAnn, toAnn_coe]
    exact T.annNorm_eq_of_sub_lt (hgood J r)
  have hny : ∀ J, T.extNorm ρ0 (annIoc r) (y J) = Nr / R ^ m := by
    intro J
    have h := hnc J
    rw [hcy J, extNorm_mul, T.extNorm_ptProd _ _ fun P hP => (hlrad J P hP).le, hlen J] at h
    have hRm : 0 < R ^ m := pow_pos hR0 m
    have hc : ((annIoc r : Set.Ioc (0 : ℝ) ρ0) : ℝ) = R := rfl
    rw [hc] at h
    rw [← h]; field_simp
  have hvaly : ∀ J (P : T.Pt) (hP : T.ptRad P.1 = R),
      ‖T.ptEval P.2 (hP.trans_le hr1.le) (y J)‖ = Nr / R ^ m := by
    intro J P hP
    have h := T.norm_ptEval_of_mult_eq_zero (hy0 J) P.2 (hP.trans_lt hr1)
      (by rw [hP]; exact hym J R le_rfl le_rfl)
    rw [h, hrIoc P.2 hP, hny]

  have hstep : ∀ J, ∀ P ∈ l J, ∃ Q ∈ l (J + 1), ‖T.ptE P.2 (Q.1 : Γ)‖ < t J := by
    intro J P hP
    have hPr := hlrad J P hP
    have hPle : T.ptRad P.1 ≤ ρ0 := hPr.trans_le hr1.le
    have h0 : T.ptEval P.2 hPle (c J : T.RobbaExt ρ0) = 0 := by
      rw [hcy J, map_mul, T.ptEval_ptProd_eq_zero_of_mem hP hPle, zero_mul]
    have hsmall : ‖T.ptEval P.2 hPle (c (J + 1) : T.RobbaExt ρ0)‖ < ε J := by
      have e : (c (J + 1) : T.RobbaExt ρ0) = ((c (J + 1) : T.RobbaExt ρ0) - c J) + c J := by ring
      rw [e, map_add, h0, add_zero]
      refine (T.norm_ptEval_le P.2 hPle _).trans_lt ?_
      rw [hrIoc P.2 hPr, ← annNorm_toAnn, map_sub, toAnn_coe, toAnn_coe]
      have e2 : T.coeAnn (c (J + 1)) - T.coeAnn (c J) = (v - T.coeAnn (c J)) - (v - T.coeAnn (c (J + 1))) := by
        ring
      rw [e2]
      exact (T.annNorm_sub_le r _ _).trans_lt (max_lt (hcε J r) ((hcε (J + 1) r).trans_le (hεanti (Nat.le_succ J))))
    rw [hcy (J + 1), map_mul, norm_mul, hvaly (J + 1) P hPr, ptProd, map_list_prod, List.map_map,
      List.norm_prod, List.map_map] at hsmall
    have hprod : ((l (J + 1)).map fun Q => ‖T.ptEval P.2 hPle (T.ξExt Q.1 ρ0)‖).prod < t J ^ (l (J + 1)).length := by
      rw [hlen (J + 1), ← hεt J]
      have hq : 0 < Nr / R ^ m := div_pos hNr (pow_pos hR0 m)
      rw [lt_div_iff₀ hNr]
      have := (lt_div_iff₀ hq).2 hsmall
      calc ((l (J + 1)).map fun Q => ‖T.ptEval P.2 hPle (T.ξExt Q.1 ρ0)‖).prod * Nr
          = (((l (J + 1)).map fun Q => ‖T.ptEval P.2 hPle (T.ξExt Q.1 ρ0)‖).prod * (Nr / R ^ m)) * R ^ m := by
            field_simp
        _ < ε J * R ^ m := by
            refine mul_lt_mul_of_pos_right ?_ (pow_pos hR0 m)
            simpa [Function.comp_def] using hsmall
    obtain ⟨Q, hQ, hQt⟩ := exists_lt_of_prod_lt _ _ (fun Q => norm_nonneg _) (ht0 J).le hprod
    exact ⟨Q, hQ, by rw [← T.ptEval_ξExt_eq_ptE P hPle]; exact hQt⟩

  have hne0 : (l 0) ≠ [] := by
    intro h; have := hlen 0; rw [h, List.length_nil] at this; omega
  obtain ⟨P0, hP0⟩ := List.exists_mem_of_ne_nil _ hne0
  choose nextP hnextP hnextPt using hstep
  let chain : (J : ℕ) → {P : T.Pt // P ∈ l J} := fun J =>
    Nat.rec ⟨P0, hP0⟩ (fun J P => ⟨nextP J P.1 P.2, hnextP J P.1 P.2⟩) J
  have hchain : ∀ J, (chain (J + 1)).1 = nextP J (chain J).1 (chain J).2 := fun J => rfl
  set x : ℕ → T.Pt := fun J => (chain J).1
  have hxr : ∀ J, T.ptRad (x J).1 = R := fun J => hlrad J _ (chain J).2
  have hxstep : ∀ J, ‖T.ptE (x J).2 ((x (J + 1)).1 : Γ)‖ < t J := fun J => by
    show ‖T.ptE (chain J).1.2 ((chain (J + 1)).1.1 : Γ)‖ < t J
    rw [hchain]; exact hnextPt J _ _
  have hΓ : ∀ J, ∃ (q : T.int) (z : L) (V : Γ), IsUnit q ∧ ‖z‖ ≤ t J ∧ V ∈ T.int ∧
      ((x (J + 1)).1 : Γ) = (x J).1 * q + T.teich z * V := fun J =>
    T.exists_step_pt ((hxr (J + 1)).trans (hxr J).symm) (by rw [hxr J]; exact htR J) (hxstep J).le
  choose q z V hq hz hV hrel using hΓ
  obtain ⟨η, hη, hηr, hηlim⟩ := T.exists_limit_pt (fun J => (x J).1) (fun J => (x J).2) hxr q hq z V hV hrel
    t htanti htlim hz (by simp only [htdef]; nlinarith)
  refine ⟨η, hη, hηr, ?_⟩

  have hηle : T.ptRad η ≤ ρ0 := hηr.trans_le hr1.le
  have hbound : ∀ J, ‖T.annEval hη (by rw [hηr]; exact r.2) v‖ ≤
      max (ε J) (‖T.ptE hη ((x J).1 : Γ)‖ * (Nr / R ^ m)) := by
    intro J
    have e : v = (v - T.coeAnn (c J)) + T.coeAnn (c J) := by ring
    rw [e, map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
    · refine (T.norm_annEval_le hη _ _).trans ?_
      have : T.ptAnnRad (by rw [hηr]; exact r.2 : T.ptRad η ∈ Set.Icc (σ0 : ℝ) ρ0) = r := Subtype.ext hηr
      rw [this]; exact (hcε J r).le
    · rw [← toAnn_coe, annEval_toAnn, hcy J, map_mul, norm_mul]
      have hperm := List.perm_cons_erase (chain J).2
      have hsplit : T.ptProd ρ0 (l J) = T.ξExt (x J).1 ρ0 * T.ptProd ρ0 ((l J).erase (x J)) := by
        rw [ptProd, (hperm.map _).prod_eq, List.map_cons, List.prod_cons]; rfl
      rw [hsplit, map_mul, norm_mul, T.ptEval_ξExt_eq_ptE ⟨η, hη⟩ hηle]
      have h1 : ‖T.ptEval hη hηle (T.ptProd ρ0 ((l J).erase (x J)))‖ ≤ 1 := by
        refine (T.norm_ptEval_le hη hηle _).trans ?_
        rw [T.extNorm_ptProd _ _ fun P hP => by
          rw [hlrad J P (List.mem_of_mem_erase hP)]; exact hηr.ge]
        exact pow_le_one₀ (T.ptRad_pos' hη).le (T.ptRad_lt_one' hη).le
      have h2 : ‖T.ptEval hη hηle (y J)‖ ≤ Nr / R ^ m := by
        refine (T.norm_ptEval_le hη hηle _).trans ?_
        rw [hrIoc hη hηr, hny]
      calc ‖T.ptE hη ((x J).1 : Γ)‖ * ‖T.ptEval hη hηle (T.ptProd ρ0 ((l J).erase (x J)))‖ *
            ‖T.ptEval hη hηle (y J)‖ ≤ ‖T.ptE hη ((x J).1 : Γ)‖ * 1 * (Nr / R ^ m) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) zero_le_one)
        _ = ‖T.ptE hη ((x J).1 : Γ)‖ * (Nr / R ^ m) := by ring
  have hlim : Tendsto (fun J => max (ε J) (‖T.ptE hη ((x J).1 : Γ)‖ * (Nr / R ^ m))) atTop (𝓝 0) := by
    have := hεlim.max (hηlim.mul_const (Nr / R ^ m))
    rwa [zero_mul, max_self] at this
  exact norm_eq_zero.1 (le_antisymm (ge_of_tendsto' hlim hbound) (norm_nonneg _))

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0} [CompleteSpace L] [IsAlgClosed L]

theorem annRes_ξAnn {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1} (h : (ρ1 : ℝ) ≤ ρ0)
    (hs : (σ0 : ℝ) ≤ σ1) (ξ : T.int) : T.annRes h hs (T.ξAnn ξ) = T.ξAnn ξ := by
  rw [ξAnn, annRes_coeAnn]; rfl

theorem exists_factor_ann (w : T.Ann ρ0 σ0) (hw : ∀ r, 0 < T.annNorm ρ0 σ0 r w)
    {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1} (h : (ρ1 : ℝ) < ρ0) (hs : (σ0 : ℝ) < σ1) :
    ∃ (l : List T.Pt) (u : T.Ann ρ1 σ1), (∀ P ∈ l, (σ1 : ℝ) ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ ρ1) ∧
      IsUnit u ∧ T.annRes h.le hs.le w = (l.map fun P => T.ξAnn P.1).prod * u := by
  classical
  set a : AnnRad ρ0 σ0 := annIn ρ0 σ0
  set b : AnnRad ρ0 σ0 := ⟨σ1, hs.le, σ1.2.2.trans h.le⟩
  set c : AnnRad ρ0 σ0 := ⟨ρ1, hs.le.trans σ1.2.2, h.le⟩
  set d : AnnRad ρ0 σ0 := annOut ρ0 σ0
  set M : ℝ :=
    (Real.log (T.annNorm ρ0 σ0 d w) - Real.log (T.annNorm ρ0 σ0 c w)) / (Real.log d - Real.log c) -
      (Real.log (T.annNorm ρ0 σ0 b w) - Real.log (T.annNorm ρ0 σ0 a w)) / (Real.log b - Real.log a)
  set Good : ℕ → Prop := fun n => ∃ l : List T.Pt, l.length = n ∧
    (∀ P ∈ l, (σ1 : ℝ) ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ ρ1) ∧ (l.map fun P => T.ξAnn P.1).prod ∣ w
  have hbound : ∀ n, Good n → n ≤ ⌊M⌋₊ := by
    rintro n ⟨l, rfl, hl, hdvd⟩
    have := T.length_le_of_prod_dvd w hw a b c d hs σ1.2.2 h l hl hdvd
    exact Nat.le_floor this
  have hG0 : Good 0 := ⟨[], rfl, by simp, by simp⟩
  set N := Nat.findGreatest Good ⌊M⌋₊
  have hGN : Good N := Nat.findGreatest_spec (P := Good) (Nat.zero_le _) hG0
  have hnot : ¬ Good (N + 1) := by
    intro hG
    by_cases hle : N + 1 ≤ ⌊M⌋₊
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self N) hle hG
    · exact hle (hbound _ hG)
  obtain ⟨l, hlen, hl, v, hwv⟩ := hGN
  set P := (l.map fun P => T.ξAnn P.1).prod
  have hPpos : ∀ r, 0 < T.annNorm ρ0 σ0 r P := fun r => by
    rw [T.annNorm_list_prod_ξAnn]
    exact List.prod_pos fun x hx => by
      obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
      exact lt_of_lt_of_le (T.ptRad_pos' Q.2) (le_max_left _ _)
  have hv : ∀ r, 0 < T.annNorm ρ0 σ0 r v := fun r => by
    have h1 := hw r
    rw [hwv, annNorm_mul] at h1
    exact pos_of_mul_pos_right h1 (hPpos r).le

  have hnozero : ∀ (ξ : T.int) (hξ : T.IsPrimOne ξ) (hr : T.ptRad ξ ∈ Set.Icc (σ0 : ℝ) ρ0),
      (σ1 : ℝ) ≤ T.ptRad ξ → T.ptRad ξ ≤ ρ1 → T.annEval hξ hr v ≠ 0 := by
    intro ξ hξ hr h1 h2 h0
    obtain ⟨y, hy⟩ := (T.annEval_eq_zero_iff hξ hr v).1 h0
    refine hnot ⟨⟨ξ, hξ⟩ :: l, by rw [List.length_cons, hlen], fun Q hQ => ?_, ⟨y, ?_⟩⟩
    · rcases List.mem_cons.1 hQ with rfl | hQ
      · exact ⟨h1, h2⟩
      · exact hl Q hQ
    · rw [List.map_cons, List.prod_cons, hwv, hy]; ring

  obtain ⟨μ, hμ, hμle⟩ := T.exists_pos_le_annNorm v hv
  obtain ⟨e, he⟩ := T.exists_coeAnn_near v (half_pos hμ)
  have hgood : ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn e) < T.annNorm ρ0 σ0 s v := fun s =>
    (he s).trans_le ((half_le_self hμ.le).trans (hμle s))
  have hm : ∀ s : ℝ, (σ1 : ℝ) ≤ s → s ≤ ρ1 → T.mult (e : T.RobbaExt ρ0) s = 0 := by
    intro s h1 h2
    by_contra hne
    have hpos : 1 ≤ T.mult (e : T.RobbaExt ρ0) s := by
      have := T.mult_nonneg (e : T.RobbaExt ρ0) s; omega
    set rs : AnnRad ρ0 σ0 := ⟨s, hs.le.trans h1, h2.trans h.le⟩
    obtain ⟨ξ, hξ, hrad, hz⟩ := T.exists_zero_ann v hv rs (hs.trans_le h1) (h2.trans_lt h) e hgood hpos
    exact hnozero ξ hξ _ (by rw [hrad]; exact h1) (by rw [hrad]; exact h2) hz
  have hu := T.isUnit_annRes_of_mult_eq_zero v e hgood h hs.le hm
  refine ⟨l, T.annRes h.le hs.le v, hl, hu, ?_⟩
  rw [hwv, map_mul, map_list_prod, List.map_map]
  congr 2
  exact List.map_congr_left fun Q _ => T.annRes_ξAnn h.le hs.le Q.1

end TeichLift

end GroundTheory.PAdicHodge
end
end
