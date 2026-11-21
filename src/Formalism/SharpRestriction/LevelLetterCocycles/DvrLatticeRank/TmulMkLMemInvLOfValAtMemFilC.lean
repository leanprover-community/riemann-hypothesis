import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PiNSOfPi
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB

section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.LevelExpansions

open PowerSeries Finset

section Good

variable {LL V : Type*} [Field LL] [AddCommGroup V] [Module LL V] {ι : Type*} [Fintype ι]

def Gd (F : ℤ → Submodule LL V) (h : ℤ) (A : ι → PowerSeries LL) (v : ι → V) : Prop :=
  ∀ i : ℕ, ∑ j, coeff i (A j) • v j ∈ F (h - i)

variable {F : ℤ → Submodule LL V} {h : ℤ} {A : ι → PowerSeries LL} {v : ι → V}

private theorem sum_coeff_mul_smul_eq_antidiagonal (U : PowerSeries LL) (F' : ι → PowerSeries LL) (w' : ι → V) (i : ℕ) :
    ∑ j, coeff i (U * F' j) • w' j = ∑ pq ∈ antidiagonal i, coeff pq.1 U • ∑ j, coeff pq.2 (F' j) • w' j := by
  simp only [coeff_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem Gd.mul (hF : Antitone F) (H : Gd F h A v) (u : PowerSeries LL) :
    Gd F h (fun j => u * A j) v := by
  intro i
  show ∑ j, coeff i (u * A j) • v j ∈ F (h - i)
  rw [_root_.Formalism.MainNotions.N.Ln34.LevelExpansions.sum_coeff_mul_smul_eq_antidiagonal u A v i]
  refine Submodule.sum_mem _ fun pq hpq => Submodule.smul_mem _ _ ?_
  have hpq' : pq.1 + pq.2 = i := by
    first
    | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    | simpa using hpq
  exact hF (show h - (i : ℤ) ≤ h - (pq.2 : ℤ) by omega) (H pq.2)

theorem Gd.unit (hF : Antitone F) {u : PowerSeries LL} (hu : IsUnit u)
    (H : Gd F h (fun j => u * A j) v) : Gd F h A v := by
  intro i
  have := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.mul hF H (↑hu.unit⁻¹ : PowerSeries LL) i
  simpa only [← mul_assoc, hu.val_inv_mul, one_mul] using this

theorem Gd.step (hF : Antitone F) {y u : PowerSeries LL} (hy : y = X * u) (hu : IsUnit u)
    {o : ι → LL} {A' : ι → PowerSeries LL} (hA : ∀ j, A j = C (o j) + y * A' j) (H : Gd F h A v) :
    ∑ j, o j • v j ∈ F h ∧ Gd F (h - 1) A' v := by
  subst hy
  have hc : ∀ j i, coeff (i + 1) (A j) = coeff i (u * A' j) := by
    intro j i
    rw [hA j, map_add, coeff_C, if_neg (by omega : i + 1 ≠ 0), zero_add, mul_assoc, coeff_succ_X_mul]
  refine ⟨?_, ?_⟩
  · have h0 := H 0
    have e : ∀ j, coeff 0 (A j) = o j := by
      intro j
      rw [hA j, map_add, coeff_C, if_pos rfl, mul_assoc, coeff_zero_X_mul, add_zero]
    simp only [e, Nat.cast_zero, sub_zero] at h0
    exact h0
  · apply Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.unit hF hu
    intro i
    have := H (i + 1)
    simp only [hc] at this
    have hcast : (h - ((i + 1 : ℕ) : ℤ)) = h - 1 - (i : ℤ) := by push_cast; ring
    rw [hcast] at this
    exact this

theorem Gd.peel (hF : Antitone F) {y u : PowerSeries LL} (hy : y = X * u) (hu : IsUnit u) (N : ℕ) :
    ∀ (h : ℤ) (A A' : ι → PowerSeries LL) (p : ι → ℕ → LL),
      (∀ j, A j = ∑ k ∈ range N, C (p j k) * y ^ k + y ^ N * A' j) → Gd F h A v →
      ∀ k < N, ∑ j, p j k • v j ∈ F (h - k) := by
  induction N with
  | zero => intro h A A' p _ _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ N ih =>
    intro h A A' p hA H k hk
    have hA' : ∀ j, A j = C (p j 0) + y * (∑ k ∈ range N, C (p j (k + 1)) * y ^ k + y ^ N * A' j) := by
      intro j
      rw [hA j, Finset.sum_range_succ', mul_add, Finset.mul_sum]
      have hs : ∑ k ∈ range N, C (p j (k + 1)) * y ^ (k + 1) = ∑ k ∈ range N, y * (C (p j (k + 1)) * y ^ k) :=
        Finset.sum_congr rfl fun k _ => by ring
      rw [hs]
      ring
    obtain ⟨h0, H'⟩ := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.step hF hy hu hA' H
    rcases k with _ | k
    · simp only [Nat.cast_zero, sub_zero]
      exact h0
    · have := ih (h - 1) (fun j => ∑ k ∈ range N, C (p j (k + 1)) * y ^ k + y ^ N * A' j) A'
        (fun j k => p j (k + 1)) (fun j => rfl) H' k (by omega)
      have hcast : h - 1 - (k : ℤ) = h - ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast] at this
      exact this

private theorem sum_coeff_smul_eq_sum_coeff_y_pow_mul_smul {y : PowerSeries LL} {N : ℕ} {A' : ι → PowerSeries LL}
    {p : ι → ℕ → LL} (hA : ∀ j, A j = ∑ k ∈ range N, C (p j k) * y ^ k + y ^ N * A' j)
    (h0 : ∀ k < N, ∑ j, p j k • v j = 0) (i : ℕ) :
    ∑ j, coeff i (A j) • v j = ∑ j, coeff i (y ^ N * A' j) • v j := by
  have e : ∀ j, coeff i (A j) = ∑ k ∈ range N, p j k * coeff i (y ^ k) + coeff i (y ^ N * A' j) := by
    intro j
    rw [hA j, map_add, map_sum]
    simp only [coeff_C_mul]
  have hk0 : ∀ k ∈ range N, ∑ j, (p j k * coeff i (y ^ k)) • v j = 0 := by
    intro k hk
    calc ∑ j, (p j k * coeff i (y ^ k)) • v j = coeff i (y ^ k) • ∑ j, p j k • v j := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [mul_comm, mul_smul]
      _ = 0 := by rw [h0 k (Finset.mem_range.mp hk), smul_zero]
  simp only [e, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_comm, Finset.sum_eq_zero hk0, zero_add]

theorem Gd.strip {y : PowerSeries LL} {N : ℕ} {A' : ι → PowerSeries LL} {p : ι → ℕ → LL}
    (hA : ∀ j, A j = ∑ k ∈ range N, C (p j k) * y ^ k + y ^ N * A' j)
    (h0 : ∀ k < N, ∑ j, p j k • v j = 0) (H : Gd F h A v) : Gd F h (fun j => y ^ N * A' j) v := by
  intro i
  have e := _root_.Formalism.MainNotions.N.Ln34.LevelExpansions.sum_coeff_smul_eq_sum_coeff_y_pow_mul_smul hA h0 i
  have := H i
  rw [e] at this
  exact this

def Fv (LL V : Type*) [Field LL] [AddCommGroup V] [Module LL V] (a : ℤ) : Submodule LL V :=
  if 0 < a then ⊥ else ⊤

theorem Fv_anti : Antitone (Fv LL V) := by
  intro a b hab
  unfold Fv
  split_ifs <;> first | exact bot_le | exact le_top | (exfalso; omega)

theorem Gd_Fv {N : ℕ} (H : ∀ i < N, ∑ j, coeff i (A j) • v j = 0) : Gd (Fv LL V) N A v := by
  intro i
  by_cases hi : i < N
  · rw [H i hi]
    exact Submodule.zero_mem _
  · have hn : ¬ (0 : ℤ) < (N : ℤ) - (i : ℤ) := by omega
    unfold Fv
    rw [if_neg hn]
    exact Submodule.mem_top

theorem Fv_zero {N k : ℕ} (hk : k < N) {z : V} (hz : z ∈ Fv LL V ((N : ℤ) - k)) : z = 0 := by
  have hp : (0 : ℤ) < (N : ℤ) - (k : ℤ) := by omega
  unfold Fv at hz
  rw [if_pos hp, Submodule.mem_bot] at hz
  exact hz

theorem peel1 {y u : PowerSeries LL} (hy : y = X * u) (hu : IsUnit u) {N : ℕ} {A G : PowerSeries LL}
    {c : ℕ → LL} (hA : A = ∑ k ∈ range N, C (c k) * y ^ k + y ^ N * G)
    (h0 : ∀ i < N, coeff i A = 0) : ∀ k < N, c k = 0 := by
  intro k hk
  have hFC : Gd (Fv LL LL) (N : ℤ) (fun _ : Unit => A) (fun _ => (1 : LL)) :=
    Gd_Fv (fun i hi => by simpa using h0 i hi)
  have hmem := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.peel (F := Fv LL LL) (v := fun _ : Unit => (1 : LL))
    Fv_anti hy hu N (N : ℤ) (fun _ => A) (fun _ => G) (fun _ k => c k) (fun _ => hA) hFC k hk
  have h1 := Fv_zero hk hmem
  simpa using h1

private theorem algebraMap_powerSeries_eq_C (c : LL) : algebraMap LL (PowerSeries LL) c = C c := by
  first
  | rfl
  | simp
  | exact PowerSeries.algebraMap_apply' c

theorem poly_expand (y : PowerSeries LL) (N : ℕ) : ∀ Q : Polynomial LL, ∃ G : PowerSeries LL,
    Polynomial.aeval y Q = ∑ k ∈ range N, C (Q.coeff k) * y ^ k + y ^ N * G := by
  induction N with
  | zero => intro Q; exact ⟨Polynomial.aeval y Q, by simp⟩
  | succ N ih =>
    intro Q
    obtain ⟨G, hG⟩ := ih Q.divX
    refine ⟨G, ?_⟩
    have hQ : Polynomial.aeval y Q = Polynomial.aeval y Q.divX * y + C (Q.coeff 0) := by
      have e := congrArg (Polynomial.aeval y) (Polynomial.divX_mul_X_add Q)
      rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_eq_C] at e
      exact e.symm
    rw [hQ, hG, Finset.sum_range_succ', add_mul, Finset.sum_mul]
    have hs : ∑ k ∈ range N, C (Q.divX.coeff k) * y ^ k * y = ∑ k ∈ range N, C (Q.coeff (k + 1)) * y ^ (k + 1) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.coeff_divX]
      ring
    rw [hs]
    ring

private theorem coeff_eq_zero_of_isUnit_of_coeff_mul_eq_zero {u E : PowerSeries LL} (hu : IsUnit u) {n : ℕ}
    (h : ∀ i < n, coeff i (u * E) = 0) : ∀ i < n, coeff i E = 0 := by
  intro i hi
  have hE : E = ↑hu.unit⁻¹ * (u * E) := by rw [← mul_assoc, hu.val_inv_mul, one_mul]
  rw [hE, coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = i := by
    first
    | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    | simpa using hpq
  rw [h pq.2 (by omega), mul_zero]

private theorem sum_coeff_smul_eq_of_isUnit_mul_eq {u : PowerSeries LL} (hu : IsUnit u) {G : PowerSeries LL} {w : V} {n : ℕ}
    (H : ∀ i < n, ∑ j, coeff i (u * A j) • v j = coeff i (u * G) • w) :
    ∀ i < n, ∑ j, coeff i (A j) • v j = coeff i G • w := by
  intro i hi
  have e1 := sum_coeff_mul_smul_eq_antidiagonal (↑hu.unit⁻¹ : PowerSeries LL) (fun j => u * A j) v i
  simp only [← mul_assoc, hu.val_inv_mul, one_mul] at e1
  rw [e1]
  have e2 : coeff i G = ∑ pq ∈ antidiagonal i, coeff pq.1 (↑hu.unit⁻¹ : PowerSeries LL) * coeff pq.2 (u * G) := by
    rw [← coeff_mul, ← mul_assoc, hu.val_inv_mul, one_mul]
  rw [e2, Finset.sum_smul]
  refine Finset.sum_congr rfl fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = i := by
    first
    | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    | simpa using hpq
  rw [H pq.2 (by omega), mul_smul]

private theorem sum_smul_eq_smul_of_coeff_expansion {y u : PowerSeries LL} (hy : y = X * u) (hu : IsUnit u) {N : ℕ}
    {A₀ A₀' : ι → PowerSeries LL} {p : ι → ℕ → LL} {v₀ : ι → V} {G G' : PowerSeries LL} {c : ℕ → LL} {w : V}
    (hA : ∀ j, A₀ j = ∑ k ∈ range N, C (p j k) * y ^ k + y ^ N * A₀' j)
    (hG : G = ∑ k ∈ range N, C (c k) * y ^ k + y ^ N * G')
    (H : ∀ i < N, ∑ j, coeff i (A₀ j) • v₀ j = coeff i G • w) :
    ∀ k < N, ∑ j, p j k • v₀ j = c k • w := by
  intro k hk
  have hFC : Gd (Fv LL V) (N : ℤ) (fun x : Option ι => Option.elim x G A₀)
      (fun x => Option.elim x (-w) v₀) := by
    apply Gd_Fv
    intro i hi
    rw [Fintype.sum_option]
    simp only [Option.elim]
    first
    | rw [H i hi, smul_neg, neg_add_cancel]
    | simp [H i hi]
  have hm := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.peel (F := Fv LL V) (v := fun x : Option ι => Option.elim x (-w) v₀)
    Fv_anti hy hu N (N : ℤ) (fun x => Option.elim x G A₀) (fun x => Option.elim x G' A₀')
    (fun x k => Option.elim x (c k) (fun j => p j k))
    (fun x => by cases x with | none => exact hG | some j => exact hA j) hFC k hk
  have h0 := Fv_zero hk hm
  rw [Fintype.sum_option] at h0
  simp only [Option.elim, smul_neg] at h0
  exact (neg_add_eq_zero.mp h0).symm

theorem van_of_dvd {y u G : PowerSeries LL} (hy : y = X * u) (N : ℕ) :
    ∀ i < N, coeff i (y ^ N * G) = 0 := by
  have hd : (X : PowerSeries LL) ^ N ∣ y ^ N * G := by
    rw [hy, mul_pow, mul_assoc]
    exact Dvd.intro _ rfl
  first
  | exact PowerSeries.X_pow_dvd_iff.mp hd
  | (intro i hi; rw [hy, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)])

end Good

section Div

variable {O LL : Type*} [CommRing O] [Field LL] [Algebra O LL] {A Z : Type*}
  (ev : Z → A → PowerSeries LL)

def Dv (O : Type*) [CommRing O] [Algebra O LL] (y : Z → PowerSeries LL) : Prop :=
  ∀ a : A, ∃ (o : O) (a' : A), ∀ z, ev z a = C (algebraMap O LL o) + y z * ev z a'

variable {ev}

theorem Dv.expand {y : Z → PowerSeries LL} (H : Dv ev O y) (N : ℕ) : ∀ a : A, ∃ (p : ℕ → O) (a' : A),
    ∀ z, ev z a = ∑ k ∈ range N, C (algebraMap O LL (p k)) * y z ^ k + y z ^ N * ev z a' := by
  induction N with
  | zero => intro a; exact ⟨fun _ => 0, a, fun z => by simp⟩
  | succ N ih =>
    intro a
    obtain ⟨o, a₁, ha⟩ := H a
    obtain ⟨p, a', hp⟩ := ih a₁
    refine ⟨fun k => if k = 0 then o else p (k - 1), a', fun z => ?_⟩
    have key : ∑ k ∈ range (N + 1), C (algebraMap O LL (if k = 0 then o else p (k - 1))) * y z ^ k
        = C (algebraMap O LL o) + y z * ∑ k ∈ range N, C (algebraMap O LL (p k)) * y z ^ k := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      congr 1
      · first
        | rw [if_pos rfl, pow_zero, mul_one]
        | simp
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [if_neg (show k + 1 ≠ 0 by omega), Nat.add_sub_cancel]
        ring
    rw [key, ha z, hp z]
    ring

theorem Dv.transfer {y : Z → PowerSeries LL} (H : Dv ev O y) {z z' : Z} {u u' : PowerSeries LL}
    (hy : y z = X * u) (hu : IsUnit u) (hy' : y z' = X * u') (N : ℕ) (a b : A) (x : LL)
    (h : ∀ i < N, coeff i (ev z a) = x * coeff i (ev z b)) :
    ∀ i < N, coeff i (ev z' a) = x * coeff i (ev z' b) := by
  obtain ⟨pa, a', ha⟩ := H.expand N a
  obtain ⟨pb, b', hb⟩ := H.expand N b
  have hexp : ∀ w, ev w a - C x * ev w b = ∑ k ∈ range N, C (algebraMap O LL (pa k) - x * algebraMap O LL (pb k)) * y w ^ k
      + y w ^ N * (ev w a' - C x * ev w b') := by
    intro w
    have hs : ∑ k ∈ range N, C (algebraMap O LL (pa k) - x * algebraMap O LL (pb k)) * y w ^ k
        = ∑ k ∈ range N, C (algebraMap O LL (pa k)) * y w ^ k - C x * ∑ k ∈ range N, C (algebraMap O LL (pb k)) * y w ^ k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sub, map_mul]
      ring
    rw [hs, ha w, hb w]
    ring
  have hc : ∀ k < N, algebraMap O LL (pa k) - x * algebraMap O LL (pb k) = 0 :=
    Formalism.MainNotions.N.Ln34.LevelExpansions.peel1 hy hu (hexp z) (fun i hi => by
      rw [map_sub, coeff_C_mul, h i hi, sub_self])
  intro i hi
  have hz' : ev z' a - C x * ev z' b = y z' ^ N * (ev z' a' - C x * ev z' b') := by
    rw [hexp z', Finset.sum_eq_zero (fun k hk => by rw [hc k (Finset.mem_range.mp hk), map_zero, zero_mul]), zero_add]
  have h1 := Formalism.MainNotions.N.Ln34.LevelExpansions.van_of_dvd (G := ev z' a' - C x * ev z' b') hy' N i hi
  rw [← hz', map_sub, coeff_C_mul] at h1
  exact sub_eq_zero.mp h1

theorem unit_add_C {y u : PowerSeries LL} (hy : y = X * u) {δ : LL} (hδ : δ ≠ 0) : IsUnit (y + C δ) := by
  subst hy
  first
  | (rw [PowerSeries.isUnit_iff_constantCoeff]; simpa using hδ)
  | exact isUnit_of_mul_eq_one _ _ (PowerSeries.mul_inv_cancel _ (by simpa using hδ))

theorem integ {yU yD : Z → PowerSeries LL} (HU : Dv ev O yU) (HD : Dv ev O yD) {zU zD : Z}
    {u u' : PowerSeries LL} (hyU : yU zU = X * u) (hu : IsUnit u) (hyD : yD zD = X * u')
    (hu' : IsUnit u') {δ : LL} (hδ : δ ≠ 0) (hUD : yU zD = yD zD + C δ) (a : A) (x a₂ : LL)
    (h b B : ℕ) (hb : b ≤ h) (hU : ∀ i, i + b < h → coeff i (ev zU a) = 0)
    (hD : ∀ i < h + B, coeff i (ev zD a) = x * coeff i ((C a₂ * yU zD * yD zD) ^ h)) :
    ∀ k < B, ∃ o : O, algebraMap O LL o = x * a₂ ^ h * (b.choose k : LL) * δ ^ (b - k) := by
  intro k hk
  obtain ⟨p, a₁, hp⟩ := HU.expand (h - b) a
  have hp0 : ∀ m < h - b, algebraMap O LL (p m) = 0 :=
    peel1 hyU hu (hp zU) (fun i hi => hU i (by omega))
  have hA : ∀ z, ev z a = yU z ^ (h - b) * ev z a₁ := by
    intro z
    rw [hp z, Finset.sum_eq_zero (fun m hm => by rw [hp0 m (Finset.mem_range.mp hm), map_zero, zero_mul]), zero_add]
  obtain ⟨q, a₃, hq⟩ := HD.expand (h + B) a₁
  obtain ⟨P, hP⟩ : ∃ P : Polynomial LL,
      P = Polynomial.C (x * a₂ ^ h) * (Polynomial.X + Polynomial.C δ) ^ b * Polynomial.X ^ h := ⟨_, rfl⟩
  obtain ⟨GT, hGT⟩ := poly_expand (yD zD) (h + B) P
  have hPt : Polynomial.aeval (yD zD) P = C (x * a₂ ^ h) * yU zD ^ b * yD zD ^ h := by
    rw [hP, hUD]
    first
    | (simp only [map_mul, map_pow, map_add, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_eq_C]; done)
    | (simp only [map_mul, map_pow, map_add, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_eq_C]; ring)
  have hsU : IsUnit (yU zD) := by rw [hUD]; exact unit_add_C hyD hδ
  have key : yU zD ^ (h - b) * Polynomial.aeval (yD zD) P = C x * (C a₂ * yU zD * yD zD) ^ h := by
    rw [hPt]
    have hsp : yU zD ^ (h - b) * yU zD ^ b = yU zD ^ h := by rw [← pow_add, Nat.sub_add_cancel hb]
    calc yU zD ^ (h - b) * (C (x * a₂ ^ h) * yU zD ^ b * yD zD ^ h)
        = C (x * a₂ ^ h) * (yU zD ^ (h - b) * yU zD ^ b) * yD zD ^ h := by ring
      _ = C x * (C a₂ * yU zD * yD zD) ^ h := by rw [hsp, map_mul, map_pow]; ring
  have hE0 : ∀ i < h + B, coeff i (ev zD a₁ - Polynomial.aeval (yD zD) P) = 0 :=
    coeff_eq_zero_of_isUnit_of_coeff_mul_eq_zero (hsU.pow (h - b)) (fun i hi => by
      rw [mul_sub, ← hA zD, key, map_sub, coeff_C_mul, hD i hi, sub_self])
  have hEexp : ev zD a₁ - Polynomial.aeval (yD zD) P
      = ∑ m ∈ range (h + B), C (algebraMap O LL (q m) - P.coeff m) * yD zD ^ m + yD zD ^ (h + B) * (ev zD a₃ - GT) := by
    have hs2 : ∑ m ∈ range (h + B), C (algebraMap O LL (q m) - P.coeff m) * yD zD ^ m
        = ∑ m ∈ range (h + B), C (algebraMap O LL (q m)) * yD zD ^ m - ∑ m ∈ range (h + B), C (P.coeff m) * yD zD ^ m := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by rw [map_sub, sub_mul]
    rw [hs2, hq zD, hGT]
    ring
  have hc : algebraMap O LL (q (h + k)) - P.coeff (h + k) = 0 :=
    peel1 hyD hu' hEexp hE0 (h + k) (by omega)
  refine ⟨q (h + k), ?_⟩
  rw [sub_eq_zero] at hc
  rw [hc, hP, add_comm h k, Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  ring

theorem caseB {V₁ V₂ : Type*} [AddCommGroup V₁] [Module LL V₁] [AddCommGroup V₂] [Module LL V₂]
    {ι : Type*} [Fintype ι] {yU yD : Z → PowerSeries LL} (HU : Dv ev O yU) (HD : Dv ev O yD)
    {zU zD : Z} {u u' : PowerSeries LL} (hyU : yU zU = X * u) (hu : IsUnit u) (hyD : yD zD = X * u')
    (hu' : IsUnit u') {δ : LL} (hδ : δ ≠ 0) (hDU : yD zU = yU zU + C δ)
    (a : ι → A) (v₁ : ι → V₁) (v₂ : ι → V₂) (w : V₂) {FU FD : ℤ → Submodule LL V₁}
    (hFU : Antitone FU) (hFD : Antitone FD) (h b B η : ℕ) (hb : b ≤ h) (hBb : B + 2 * η < b) (κ : LL)
    (hZ : ∀ o : ι → O, ∑ j, algebraMap O LL (o j) • v₁ j ∈ FD (η + 1) →
      ∑ j, algebraMap O LL (o j) • v₁ j = 0 ∧ ∑ j, algebraMap O LL (o j) • v₂ j = 0)
    (hD : Gd FD h (fun j => ev zD (a j)) v₁) (hU : Gd FU h (fun j => ev zU (a j)) v₁)
    (h2 : ∀ i ≤ h, ∑ j, coeff i (ev zU (a j)) • v₂ j =
      coeff i (C κ * yU zU ^ (h - b) * yD zU ^ (h + B)) • w) :
    ∃ o : ι → O, ∑ j, algebraMap O LL (o j) • v₁ j ∈ FU (η + 1) ∧
      ∑ j, algebraMap O LL (o j) • v₂ j = κ • w := by
  choose p a₁ hp using fun j => HD.expand (h - η) (a j)
  have hnull : ∀ k < h - η, ∑ j, algebraMap O LL (p j k) • v₁ j = 0 ∧ ∑ j, algebraMap O LL (p j k) • v₂ j = 0 := by
    intro k hk
    apply hZ (fun j => p j k)
    have hm := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.peel hFD hyD hu' (h - η) (h : ℤ) (fun j => ev zD (a j)) (fun j => ev zD (a₁ j))
      (fun j k => algebraMap O LL (p j k)) (fun j => hp j zD) hD k hk
    exact hFD (by omega) hm
  have hsU : IsUnit (yD zU) := by rw [hDU]; exact unit_add_C hyU hδ
  have hFC1 : Gd FU h (fun j => ev zU (a₁ j)) v₁ := by
    have hs : Gd FU h (fun j => yD zU ^ (h - η) * ev zU (a₁ j)) v₁ :=
      Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.strip (F := FU) (h := (h : ℤ)) (A := fun j => ev zU (a j)) (v := v₁) (y := yD zU)
        (N := h - η) (A' := fun j => ev zU (a₁ j)) (p := fun j k => algebraMap O LL (p j k))
        (fun j => hp j zU) (fun k hk => (hnull k hk).1) hU
    exact Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.unit hFU (hsU.pow (h - η)) hs
  have hv2 : ∀ i < h + 1, ∑ j, coeff i (yD zU ^ (h - η) * ev zU (a₁ j)) • v₂ j
      = coeff i (yD zU ^ (h - η) * (C κ * yU zU ^ (h - b) * yD zU ^ (B + η))) • w := by
    intro i hi
    have e : ∑ j, coeff i (ev zU (a j)) • v₂ j = ∑ j, coeff i (yD zU ^ (h - η) * ev zU (a₁ j)) • v₂ j :=
      sum_coeff_smul_eq_sum_coeff_y_pow_mul_smul (v := v₂) (A := fun j => ev zU (a j)) (A' := fun j => ev zU (a₁ j))
        (p := fun j k => algebraMap O LL (p j k)) (y := yD zU) (N := h - η)
        (fun j => hp j zU) (fun k hk => (hnull k hk).2) i
    have hpow : yD zU ^ (h - η) * (C κ * yU zU ^ (h - b) * yD zU ^ (B + η))
        = C κ * yU zU ^ (h - b) * yD zU ^ (h + B) := by
      rw [show h + B = (h - η) + (B + η) by omega]
      ring
    rw [← e, hpow, h2 i (by omega)]
  have hv2' : ∀ i < h + 1, ∑ j, coeff i (ev zU (a₁ j)) • v₂ j = coeff i (C κ * yU zU ^ (h - b) * yD zU ^ (B + η)) • w :=
    sum_coeff_smul_eq_of_isUnit_mul_eq (A := fun j => ev zU (a₁ j)) (v := v₂) (hsU.pow (h - η)) hv2
  choose q a₂ hq using fun j => HU.expand (B + η + (h - b) + 1) (a₁ j)
  obtain ⟨P, hP⟩ : ∃ P : Polynomial LL,
      P = Polynomial.C κ * (Polynomial.X + Polynomial.C δ) ^ (B + η) * Polynomial.X ^ (h - b) := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ := poly_expand (yU zU) (B + η + (h - b) + 1) P
  have hPt : Polynomial.aeval (yU zU) P = C κ * yU zU ^ (h - b) * yD zU ^ (B + η) := by
    rw [hP, hDU]
    simp only [map_mul, map_pow, map_add, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_eq_C]
    ring
  rw [hPt] at hG'
  have huniq : ∑ j, algebraMap O LL (q j (B + η + (h - b))) • v₂ j = P.coeff (B + η + (h - b)) • w :=
    sum_smul_eq_smul_of_coeff_expansion (v₀ := v₂) (w := w) (A₀ := fun j => ev zU (a₁ j)) (A₀' := fun j => ev zU (a₂ j))
      (p := fun j k => algebraMap O LL (q j k)) (c := fun k => P.coeff k) hyU hu (fun j => hq j zU) hG'
      (fun i hi => hv2' i (by omega)) (B + η + (h - b)) (by omega)
  have hm1 := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.peel hFU hyU hu (B + η + (h - b) + 1) (h : ℤ) (fun j => ev zU (a₁ j))
    (fun j => ev zU (a₂ j)) (fun j k => algebraMap O LL (q j k)) (fun j => hq j zU) hFC1 (B + η + (h - b)) (by omega)
  refine ⟨fun j => q j (B + η + (h - b)), hFU (by omega) hm1, ?_⟩
  show ∑ j, algebraMap O LL (q j (B + η + (h - b))) • v₂ j = κ • w
  rw [huniq, hP, Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  simp

end Div

section Num

theorem caseC {O K : Type*} [CommRing O] [Field K] [Algebra O K] (l : ℕ) [Fact l.Prime] (δ : O)
    (hδ : δ ^ 2 ∣ (l : O)) (hun : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : O)) (x : K) (b B : ℕ) (hB : 1 ≤ B)
    (hBb : B ≤ b) (o : O)
    (ho : algebraMap O K o = x * (b.choose (B - 1) : K) * (algebraMap O K δ) ^ (b - (B - 1)))
    (y : ℕ) (hy : b - B + 1 + 2 * padicValNat l (b.choose (B - 1)) ≤ 2 * y) :
    ∃ o : O, algebraMap O K o = (l : K) ^ y * x := by
  obtain ⟨c, hc⟩ : ∃ c, c = b.choose (B - 1) := ⟨_, rfl⟩
  rw [← hc] at ho hy
  have hc0 : c ≠ 0 := by rw [hc]; exact (Nat.choose_pos (by omega)).ne'
  obtain ⟨c', hc'⟩ := (pow_padicValNat_dvd : l ^ padicValNat l c ∣ c)
  have hnd : ¬ l ∣ c' := by
    rintro ⟨d, rfl⟩
    have hd : l ^ (padicValNat l c + 1) ∣ l ^ padicValNat l c * (l * d) := ⟨d, by ring⟩
    rw [← hc'] at hd
    exact pow_succ_padicValNat_not_dvd (p := l) hc0 hd
  generalize hv : padicValNat l c = v at hc' hy
  obtain ⟨r, hr⟩ := hδ
  have hu := hun c' hnd
  refine ⟨o * ↑hu.unit⁻¹ * δ ^ (2 * (y - v) - (b - (B - 1))) * r ^ (y - v), ?_⟩
  have hlK : (l : K) = algebraMap O K δ ^ 2 * algebraMap O K r := by
    rw [← map_natCast (algebraMap O K) l, hr, map_mul, map_pow]
  have hcK : (c : K) = (l : K) ^ v * (c' : K) := by rw [hc']; push_cast; ring
  have hinv : algebraMap O K (↑hu.unit⁻¹ : O) * (c' : K) = 1 := by
    rw [← map_natCast (algebraMap O K) c', ← map_mul, hu.val_inv_mul, map_one]
  have h2 : 2 * (y - v) = (b - (B - 1)) + (2 * (y - v) - (b - (B - 1))) := by omega
  have hy2 : y = v + (y - v) := by omega
  rw [map_mul, map_mul, map_mul, ho, map_pow, map_pow, hcK]
  calc _ = x * (l : K) ^ v * (algebraMap O K (↑hu.unit⁻¹ : O) * (c' : K))
        * (algebraMap O K δ ^ (b - (B - 1)) * algebraMap O K δ ^ (2 * (y - v) - (b - (B - 1))))
        * algebraMap O K r ^ (y - v) := by ring
    _ = x * (l : K) ^ v * (algebraMap O K δ ^ 2 * algebraMap O K r) ^ (y - v) := by
        rw [hinv, ← pow_add, ← h2, pow_mul, mul_pow]
        ring
    _ = (l : K) ^ y * x := by
        rw [← hlK, mul_assoc, ← pow_add, ← hy2, mul_comm]

theorem yc_bound (l : ℕ) [hl : Fact l.Prime] (b B η h : ℕ) (hb : b ≤ h)
    (hbB : b ≤ B + 2 * η) (hBb : B ≤ b) :
    b - B + 1 + 2 * padicValNat l (b.choose (B - 1)) ≤ 2 * ⌈(η : ℝ) + 1 / 2 + Real.logb l h⌉₊ := by
  obtain ⟨v, hv⟩ : ∃ v, v = padicValNat l (b.choose (B - 1)) := ⟨_, rfl⟩
  rw [← hv]
  have hvlog : v ≤ Nat.log l b := by
    rw [hv, ← Nat.factorization_def _ hl.out]
    exact Nat.factorization_choose_le_log
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hvle : (v : ℝ) ≤ Real.logb l h := by
    rcases Nat.eq_zero_or_pos v with hv0 | hv0
    · rw [hv0, Nat.cast_zero]
      rcases Nat.eq_zero_or_pos h with h0 | h0
      · rw [h0, Nat.cast_zero, Real.logb_zero]
      · exact Real.logb_nonneg hl1 (by exact_mod_cast h0)
    · have hb0 : b ≠ 0 := by
        rintro rfl
        rw [Nat.log_zero_right] at hvlog
        omega
      have hpow : l ^ v ≤ h :=
        (Nat.pow_le_pow_right hl.out.pos hvlog).trans ((Nat.pow_log_le_self l hb0).trans hb)
      have hh : (0 : ℝ) < h := by exact_mod_cast (Nat.pos_of_ne_zero hb0).trans_le hb
      rw [Real.le_logb_iff_rpow_le hl1 hh, Real.rpow_natCast]
      exact_mod_cast hpow
  have hcl := Nat.le_ceil ((η : ℝ) + 1 / 2 + Real.logb l h)
  have h1 : ((b - B : ℕ) : ℝ) ≤ 2 * η := by exact_mod_cast (by omega : b - B ≤ 2 * η)
  have key : ((b - B + 1 + 2 * v : ℕ) : ℝ) ≤ ((2 * ⌈(η : ℝ) + 1 / 2 + Real.logb l h⌉₊ : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast key

end Num

end Formalism.MainNotions.N.Ln34.LevelExpansions

end
end

section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.LevelExpansions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.DescentValuation PowerSeries

theorem ps_div {O : Type*} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (r : O) (k : ℕ)
    (hk : 0 < k) (hr : r ^ k ∈ I) (g : PowerSeries O) :
    ∃ (o : O) (g' : PowerSeries O), g = C o + (X - C r) * g' := by
  have hI : I ≠ ⊤ := by
    intro h
    have hH : IsHausdorff I O := inferInstance
    rw [h] at hH
    exact not_subsingleton O hH.subsingleton
  have H : (Polynomial.X ^ k - Polynomial.C (r ^ k) : Polynomial O).IsDistinguishedAt I := by
    refine ⟨⟨fun {i} hi => ?_⟩, Polynomial.monic_X_pow_sub_C _ hk.ne'⟩
    rw [Polynomial.natDegree_X_pow_sub_C] at hi
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hi.ne, Polynomial.coeff_C]
    split_ifs
    · simpa using hr
    · simp
  have e := ((H.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod g).eq_mul_add
  obtain ⟨q, R, e⟩ : ∃ (q : PowerSeries O) (R : Polynomial O),
      g = ((Polynomial.X ^ k - Polynomial.C (r ^ k) : Polynomial O) : PowerSeries O) * q + R := ⟨_, _, e⟩
  obtain ⟨D', hD'⟩ : (X - C r : PowerSeries O) ∣ X ^ k - C r ^ k := sub_dvd_pow_sub_pow _ _ _
  obtain ⟨R', hR'⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := r) (p := R)
  have h1 := congrArg (fun p : Polynomial O => (p : PowerSeries O)) hR'
  simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X] at h1
  rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, map_pow, hD'] at e
  exact ⟨R.eval r, D' * q + R', by rw [e]; linear_combination h1⟩

theorem dvd_zeta {O : Type*} [CommRing O] [IsDomain O] (p : ℕ) (hp : p.Prime) (z : O) (hz : z ^ p = 1)
    (hz1 : z ≠ 1) : (p : O) ∣ (z - 1) ^ (p - 1) := by
  obtain ⟨t, ht⟩ := exists_add_pow_prime_eq hp (z - 1) (1 : O)
  rw [sub_add_cancel, hz, one_pow] at ht
  have hx : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  refine ⟨-t, mul_left_cancel₀ hx ?_⟩
  have : (z - 1) ^ p = (z - 1) * (z - 1) ^ (p - 1) := by
    rw [← pow_succ']; congr 1; have := hp.pos; omega
  rw [← this]
  linear_combination -ht

section Ring

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem lev_congr (c : ZMod n) (ζ : LL) {a b : LetA O n} (h : a c = b c) : W.lev c ζ a = W.lev c ζ b := by
  have := W.lev_letter c ζ (a - b) (by rw [Pi.sub_apply, h, sub_self])
  rwa [map_sub, sub_eq_zero] at this

theorem lev_alg (c : ZMod n) (ζ : LL) (o : O) :
    W.lev c ζ (algebraMap O (LetA O n) o) = C (algebraMap O LL o) := by
  rw [AlgHom.commutes, PowerSeries.algebraMap_apply]

theorem alg_apply (o : O) (c : ZMod n) : (algebraMap O (LetA O n) o) c = C o := by
  show algebraMap O (PowerSeries O) o = C o
  rw [PowerSeries.algebraMap_apply]; rfl

theorem lev_letE (c : ZMod n) (ζ : LL) : W.lev c ζ (letE c : LetA O n) = 1 := by
  rw [lev_congr W c ζ (b := 1) (by simp [letE]), map_one]

theorem levπ01 (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    constantCoeff (W.lev c ζ letπ) = ζ - 1 ∧ coeff 1 (W.lev c ζ letπ) = ζ ∧
      (ζ - 1) * coeff 1 (W.lev c ζ W.q) = PD.p ∧ constantCoeff (W.lev c ζ W.q) = 0 := by
  obtain ⟨E, hE0, hEd, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  have h0 : constantCoeff (W.lev c ζ letπ) = ζ - 1 := by
    have h := congrArg constantCoeff hE
    rw [map_add, map_one, map_mul, constantCoeff_C, hE0, mul_one] at h
    linear_combination h
  have hE1 : coeff 1 E = 1 := by
    have h1 := congrArg (coeff 0) hEd
    rw [PowerSeries.coeff_derivative] at h1
    simp only [zero_add, Nat.cast_zero, mul_one, coeff_zero_eq_constantCoeff_apply, hE0] at h1
    simpa using h1
  obtain ⟨u, hu, -⟩ := framepf_lev_q_simple W c ζ hζ
  have hq0 : constantCoeff (W.lev c ζ W.q) = 0 := by rw [hu]; simp
  refine ⟨h0, ?_, ?_, hq0⟩
  · have h := congrArg (coeff 1) hE
    rw [map_add, coeff_C_mul, hE1, mul_one, coeff_one, if_neg one_ne_zero, zero_add] at h
    exact h
  · have hπq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
      funext i
      simp only [letπ, LocWach.q, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
      exact W.q₀_def
    have hl := congrArg (W.lev c ζ) hπq
    rw [map_mul, map_sub, map_pow, map_add, map_one] at hl
    rw [hE, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul] at hl
    obtain ⟨w, hw, hw0⟩ := framepf_exp_pow_sub_one E hE0 hEd PD.p
    rw [hw] at hl
    have h := congrArg (coeff 1) hl
    rw [coeff_one_mul, hq0, h0, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, hw0] at h
    linear_combination h

def yR (π' : LetA O n) (c : ZMod n) (r : O) (ζ : LL) : PowerSeries LL :=
  W.lev c ζ π' - C (algebraMap O LL r)

def evA (c : ZMod n) (ζ : LL) (a : ↥W.AΔ) : PowerSeries LL := W.lev c ζ (a : LetA O n)

theorem Eat_mem {π' : LetA O n} (hπ : π' ∈ W.AΔ) (E : ZMod n → Polynomial O) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ W.AΔ := by
  intro δ hδ
  funext i
  show W.γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
  rw [← Polynomial.aeval_algHom_apply]
  exact congrArg (fun p => Polynomial.aeval p (E i)) (congrFun (hπ δ hδ) i)

theorem lev_Eat (π' : LetA O n) (E : ZMod n → Polynomial O) (c : ZMod n) (ζ : LL) :
    W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = Polynomial.aeval (W.lev c ζ π') (E c) := by
  rw [Polynomial.aeval_algHom_apply]
  apply lev_congr
  exact (Polynomial.aeval_algHom_apply (Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) c) π' (E c))

theorem cc_aeval (f : PowerSeries LL) (r : O) (hf : constantCoeff f = algebraMap O LL r)
    (P : Polynomial O) : constantCoeff (Polynomial.aeval f P) = algebraMap O LL (P.eval r) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, map_mul, map_pow, hf,
      PowerSeries.algebraMap_apply, constantCoeff_C, map_mul, map_pow]

theorem aeval_lin (π' : LetA O n) (c : ZMod n) (r : O) (ζ : LL) :
    Polynomial.aeval (W.lev c ζ π') (Polynomial.X - Polynomial.C r) = yR W π' c r ζ := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, PowerSeries.algebraMap_apply]
  rfl

variable [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
  [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] {s' : ℕ} {π' : LetA O n}
  {E : ZMod n → Polynomial O} (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 2 s' π' E) (hs : 2 * s' = PD.p - 1)
  (hs1 : 1 ≤ s') (c : ZMod n)

include hinj in
theorem z_dvd {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {z : O} (hz : algebraMap O LL z = ζ) :
    (PD.p : O) ∣ (z - 1) ^ (PD.p - 1) :=
  dvd_zeta PD.p PD.hp z (hinj (by rw [map_pow, hz, map_one, hζ.pow_eq_one]))
    (fun h => hζ.ne_one PD.hp.one_lt (by rw [← hz, h, map_one]))

include hinj in

theorem expansion_low_coeffs_integral {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {z : O} (hz : algebraMap O LL z = ζ)
    (a : LetA O n) : ∃ o₀ o₁ : O, constantCoeff (W.lev c ζ a) = algebraMap O LL o₀ ∧
      coeff 1 (W.lev c ζ a) = algebraMap O LL o₁ := by
  have hx : (z - 1) ^ (PD.p - 1) ∈ Ideal.span {((PD.p : ℕ) : O)} :=
    Ideal.mem_span_singleton.2 (z_dvd hinj hζ hz)
  have hk : 0 < PD.p - 1 := by have := PD.hp.one_lt; omega
  obtain ⟨o₀, g₁, h₁⟩ := ps_div _ (z - 1) _ hk hx (a c)
  obtain ⟨o₁, g₂, h₂⟩ := ps_div _ (z - 1) _ hk hx g₁
  obtain ⟨h0, h1, -, -⟩ := levπ01 W c ζ hζ
  have e : W.lev c ζ a = W.lev c ζ (algebraMap O (LetA O n) o₀ + (letπ - algebraMap O (LetA O n) (z - 1)) *
      (algebraMap O (LetA O n) o₁ + (letπ - algebraMap O (LetA O n) (z - 1)) * fun _ => g₂)) := by
    apply lev_congr
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, alg_apply, letπ]
    rw [h₁, h₂]
  set y := W.lev c ζ letπ - C (algebraMap O LL (z - 1)) with hy
  have hy0 : constantCoeff y = 0 := by
    rw [hy, map_sub, h0, constantCoeff_C, map_sub, hz, map_one, sub_self]
  have hy1 : coeff 1 y = ζ := by
    rw [hy, map_sub, h1, coeff_C, if_neg one_ne_zero, sub_zero]
  simp only [map_add, map_mul, map_sub (W.lev c ζ), lev_alg] at e
  rw [← hy] at e
  refine ⟨o₀, o₁ * z, ?_, ?_⟩
  · rw [e, map_add, map_mul, hy0, zero_mul, add_zero, constantCoeff_C]
  · rw [e, map_add, coeff_C, if_neg one_ne_zero, zero_add, coeff_one_mul, hy0, hy1, map_add, map_mul,
      hy0, constantCoeff_C, map_mul, hz]
    ring

include hinj hp9 hs in

theorem root {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {z : O} (hz : algebraMap O LL z = ζ) :
    ∃ r : O, constantCoeff (W.lev c ζ π') = algebraMap O LL r ∧ (PD.p : O) ∣ r ^ 2 := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hp9
  obtain ⟨o₀, -, h₀, -⟩ := expansion_low_coeffs_integral W hinj c hζ hz (w : LetA O n)
  refine ⟨o₀ * (z - 1) ^ s', ?_, ?_⟩
  · rw [hw, map_mul, map_pow, map_mul, map_pow, h₀, (levπ01 W c ζ hζ).1, map_mul, map_pow, map_sub, hz,
      map_one]
  · rw [mul_pow, ← pow_mul, mul_comm s', hs]
    exact Dvd.dvd.mul_left (z_dvd hinj hζ hz) _

omit [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] in
include hp9 hs1 in
theorem cc_π' (i : ZMod n) : constantCoeff (π' i) = 0 := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hp9
  have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  rw [this, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), mul_zero]

include hp9 hs1 in

theorem dv {r : O} (hr : (PD.p : O) ∣ r ^ 2) : Dv (evA W c) O (yR W π' c r) := by
  intro a
  have hπ0 := cc_π' W hp9 hs1
  obtain ⟨hπΔ, hR, -⟩ := hp9
  obtain ⟨F, hF, -⟩ := hR a a.2
  obtain ⟨o, g', hg⟩ := ps_div _ r 2 two_pos (Ideal.mem_span_singleton.2 hr) (F c)
  have ha : (fun j => PowerSeries.subst (π' j) g') ∈ W.AΔ := by
    intro δ hδ
    funext j
    show W.γ₀ δ (PowerSeries.subst (π' j) g') = _
    rw [DualFramesAlt.EigenUniformiser.algHom_subst (W.γ₀ δ) (W.γ₀_X δ).1 (hπ0 j)]
    exact congrArg (fun p => PowerSeries.subst p g') (congrFun (hπΔ δ hδ) j)
  refine ⟨o, ⟨_, ha⟩, fun ζ => ?_⟩
  unfold evA yR
  rw [← lev_alg W c ζ, ← lev_alg W c ζ, ← map_sub, ← map_mul, ← map_add]
  apply lev_congr
  have hS : PowerSeries.HasSubst (π' c) := PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 c)
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, alg_apply]
  rw [hF c, hg, PowerSeries.subst_add hS, PowerSeries.subst_mul hS, PowerSeries.subst_sub hS,
    PowerSeries.subst_X hS, PowerSeries.subst_C, PowerSeries.subst_C]
  rfl

omit [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] in
include hinj hp9 in
theorem is_root {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {r : O}
    (hr : constantCoeff (W.lev c ζ π') = algebraMap O LL r) : (E c).eval r = 0 := by
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -⟩ := hp9
  obtain ⟨e₁, he, -⟩ := u3downPf_lev_E W c ζ hζ _ w hw
  apply hinj
  rw [← cc_aeval _ r hr, ← lev_Eat, he, map_zero]
  simp

omit [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] in
include hinj hp9 in

theorem simple {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) {r : O}
    (hr : constantCoeff (W.lev c ζ π') = algebraMap O LL r) :
    ∃ u, yR W π' c r ζ = X * u ∧ IsUnit u := by
  obtain ⟨E₁, hE₁⟩ := Polynomial.dvd_iff_isRoot.2 (is_root W hinj hp9 c hζ hr)
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -⟩ := hp9
  obtain ⟨e₁, he, he₁⟩ := u3downPf_lev_E W c ζ hζ _ w hw
  obtain ⟨u, hu⟩ : X ∣ yR W π' c r ζ := by
    rw [X_dvd_iff, yR, map_sub, hr, constantCoeff_C, sub_self]
  refine ⟨u, hu, ?_⟩
  rw [lev_Eat, hE₁, map_mul, aeval_lin, hu, mul_assoc] at he
  have h2 := mul_left_cancel₀ X_ne_zero he
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  intro h0
  apply he₁
  rw [← h2, map_mul, h0, zero_mul]

include hinj hp9 hs hs1 in

theorem fact2 {ζU ζD : LL} (hU : IsPrimitiveRoot ζU PD.p) (hD : IsPrimitiveRoot ζD PD.p) {z : O}
    (hz : algebraMap O LL z = ζU) {rU rD : O}
    (hrU : constantCoeff (W.lev c ζU π') = algebraMap O LL rU) (hpU : (PD.p : O) ∣ rU ^ 2)
    (hrD : constantCoeff (W.lev c ζD π') = algebraMap O LL rD) (hpD : (PD.p : O) ∣ rD ^ 2)
    (hne : rU ≠ rD) (hp0 : (PD.p : O) ≠ 0) :
    ∃ a₂ : O, IsUnit a₂ ∧ (∀ ζ, W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') =
      C (algebraMap O LL a₂) * yR W π' c rU ζ * yR W π' c rD ζ) ∧ (rD - rU) ^ 2 ∣ (PD.p : O) := by
  have hπ0 := cc_π' W hp9 hs1 c
  obtain ⟨E₁, hE₁⟩ := Polynomial.dvd_iff_isRoot.2 (is_root W hinj hp9 c hU hrU)
  have hD1 : E₁.IsRoot rD := by
    have := is_root W hinj hp9 c hD hrD
    rw [hE₁, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)
  obtain ⟨E₂, hE₂⟩ := Polynomial.dvd_iff_isRoot.2 hD1
  obtain ⟨-, -, ⟨w, hw⟩, hdeg, ⟨w', hw'⟩, -⟩ := hp9
  have hd := hdeg c
  have hE20 : E₂ ≠ 0 := by
    intro h; rw [hE₁, hE₂, h, mul_zero, mul_zero] at hd; simp at hd
  rw [hE₁, hE₂, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) hE20),
    Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hE20, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C] at hd
  obtain ⟨a₂, ha₂⟩ := Polynomial.natDegree_eq_zero.1 (show E₂.natDegree = 0 by omega)
  have hfac : ∀ ζ, W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') =
      C (algebraMap O LL a₂) * yR W π' c rU ζ * yR W π' c rD ζ := by
    intro ζ
    rw [lev_Eat, hE₁, hE₂, ← ha₂, map_mul, map_mul, aeval_lin, aeval_lin, Polynomial.aeval_C,
      PowerSeries.algebraMap_apply]
    ring
  refine ⟨a₂, ?_, hfac, ?_⟩
  · have h1 := congrArg constantCoeff (congrFun hw' c)
    have h2 : constantCoeff (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c) = rU * rD * a₂ := by
      show constantCoeff (Polynomial.aeval (π' c) (E c)) = _
      rw [hE₁, hE₂, ← ha₂]
      simp [hπ0, PowerSeries.algebraMap_apply]
      ring
    have h3 : constantCoeff (W.q c) = (PD.p : O) := Formalism.MainNotions.N.Ln34.CrystallineExponents.constantCoeff_q_zero_eq_p W
    rw [Pi.mul_apply, map_mul, h2, h3] at h1
    obtain ⟨tU, htU⟩ := hpU
    obtain ⟨tD, htD⟩ := hpD
    have h4 : (PD.p : O) ^ 2 * (a₂ * (a₂ * constantCoeff ((w' : LetA O n) c) ^ 2 * tU * tD)) =
        (PD.p : O) ^ 2 * 1 := by
      conv_rhs => rw [h1]
      rw [mul_pow, mul_pow, mul_pow, htU, htD]; ring
    exact IsUnit.of_mul_eq_one _ (mul_left_cancel₀ (pow_ne_zero 2 hp0) h4)
  · obtain ⟨h0, h1, hq1, -⟩ := levπ01 W c ζU hU
    obtain ⟨o₀, o₁, ho₀, ho₁⟩ := expansion_low_coeffs_integral W hinj c hU hz (w : LetA O n)
    obtain ⟨o₀', -, ho₀', -⟩ := expansion_low_coeffs_integral W hinj c hU hz (w' : LetA O n)
    have sectionFrameQuotient : constantCoeff (yR W π' c rU ζU) = 0 := by
      rw [yR, map_sub, hrU, constantCoeff_C, sub_self]
    have hyD0 : constantCoeff (yR W π' c rD ζU) = algebraMap O LL (rU - rD) := by
      rw [yR, map_sub, hrU, constantCoeff_C, map_sub]
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s' = s₀ + 1 := ⟨s' - 1, by omega⟩
    have hyU1 : coeff 1 (yR W π' c rU ζU) =
        (ζU - 1) ^ s₀ * algebraMap O LL (o₁ * (z - 1) + o₀ * ((s₀ + 1 : ℕ) : O) * z) := by
      rw [yR, map_sub, coeff_C, if_neg one_ne_zero, sub_zero, hw, map_mul, map_pow, coeff_one_mul,
        coeff_one_pow, map_pow, h0, h1, ho₀, ho₁]
      simp only [map_add, map_mul, map_sub, hz, map_one, map_natCast, Nat.add_sub_cancel]
      ring
    rw [hw', map_mul, hfac] at hq1
    simp only [coeff_one_mul, map_mul, sectionFrameQuotient, hyD0, hyU1, ho₀', constantCoeff_C, coeff_C,
      if_neg one_ne_zero] at hq1
    have h5 : (PD.p : O) = (z - 1) ^ (s₀ + 1) * (rD - rU) *
        (-(o₀' * a₂ * (o₁ * (z - 1) + o₀ * ((s₀ + 1 : ℕ) : O) * z))) := by
      apply hinj
      rw [map_natCast, ← hq1]
      simp only [map_add, map_mul, map_sub, hz, map_one, map_natCast, map_pow, map_neg]
      ring
    obtain ⟨t, ht⟩ := z_dvd hinj hU hz
    rw [← hs] at ht
    set Ω := -(o₀' * a₂ * (o₁ * (z - 1) + o₀ * ((s₀ + 1 : ℕ) : O) * z))
    refine ⟨t * Ω ^ 2, mul_left_cancel₀ hp0 ?_⟩
    have : (PD.p : O) * (PD.p : O) = ((z - 1) ^ (s₀ + 1) * (rD - rU) * Ω) ^ 2 := by
      rw [← h5]; ring
    rw [this, mul_pow, mul_pow, ← pow_mul, mul_comm (s₀ + 1), ht]
    ring

end Ring

end Formalism.MainNotions.N.Ln34.LevelExpansions

end
end

section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.LevelExpansions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.DescentValuation TensorProduct
open Formalism.MainNotions.N.Ln34.UnivLinkPf PowerSeries

theorem ser_van {LL : Type} [Field LL] (e e₁ P G A : PowerSeries LL) (u x₀ : LL) (h N : ℕ)
    (he : e = X * e₁) (he₁ : constantCoeff e₁ ≠ 0) (hP : constantCoeff P ≠ 0) (hu : u ≠ 0)
    (hrel : rescale u (e ^ h) * P * G = e ^ h * rescale u A - rescale u (e ^ h) * A)
    (hA : ∀ i < N, coeff i A = x₀ * coeff i (e ^ h)) :
    ∀ i < N, coeff i G = 0 := by
  set D := A - C x₀ * e ^ h with hD
  have hXD : X ^ N ∣ D := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [hD, map_sub, coeff_C_mul, hA i hi, sub_self]
  obtain ⟨D₁, hD₁⟩ := hXD
  have hA' : A = C x₀ * e ^ h + X ^ N * D₁ := by rw [← hD₁, hD]; ring
  have hR : rescale u (e ^ h) = X ^ h * (C (u ^ h) * (rescale u e₁) ^ h) := by
    rw [map_pow, he, map_mul, rescale_X, mul_pow, mul_pow]; simp only [map_pow]; ring
  have hRC : rescale u (C x₀) = C x₀ := by
    ext k
    rw [coeff_rescale, coeff_C]
    split_ifs with hk
    · subst hk; simp
    · simp
  have hresc : rescale u A = C x₀ * rescale u (e ^ h) + X ^ N * (C (u ^ N) * rescale u D₁) := by
    rw [hA', map_add, map_mul, map_mul, hRC, map_pow (rescale u) X N, rescale_X, mul_pow]
    simp only [map_pow]; ring
  have key : X ^ h * (C (u ^ h) * (rescale u e₁) ^ h * P * G) =
      X ^ h * (X ^ N * (e₁ ^ h * C (u ^ N) * rescale u D₁ - C (u ^ h) * (rescale u e₁) ^ h * D₁)) := by
    have h1 := hrel
    rw [hresc, hA', hR, he] at h1
    rw [mul_pow] at h1
    linear_combination h1
  have hX : (X : PowerSeries LL) ^ h ≠ 0 := pow_ne_zero _ X_ne_zero
  have key2 := mul_left_cancel₀ hX key
  have hV : IsUnit (C (u ^ h) * (rescale u e₁) ^ h * P) := by
    rw [isUnit_iff_constantCoeff]
    simp only [map_mul, map_pow, constantCoeff_C]
    have : constantCoeff (rescale u e₁) = constantCoeff e₁ := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
        coeff_zero_eq_constantCoeff_apply]
    rw [this]
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ he₁)) hP).isUnit
  have hdvd : X ^ N ∣ C (u ^ h) * (rescale u e₁) ^ h * P * G := ⟨_, key2⟩
  exact X_pow_dvd_iff.1 ((hV.dvd_mul_left).1 hdvd)

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem letE_mem (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ :=
  fun δ _ => Formalism.MainNotions.LiftingTheory.wmap_γA_letE W δ c

theorem algE_smul (o : O) (a : LetA O n) :
    algebraMap (LetA O n) W.EE (o • a) = o • algebraMap (LetA O n) W.EE a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

theorem lev_smul (c : ZMod n) (ζ : LL) (o : O) (a : LetA O n) (i : ℕ) :
    coeff i (W.lev c ζ (o • a)) = algebraMap O LL o * coeff i (W.lev c ζ a) := by
  rw [Algebra.smul_def, map_mul, lev_alg, coeff_C_mul]

theorem expS_nat (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {m : ℕ} (a : Fin m → LetA O n)
    (y : Fin m → W.DD T) (i : ℕ) :
    expS W T c ζ a y i = ∑ j, coeff i (W.lev c ζ (a j)) • valAt W T c ζ (y j) := by
  unfold expS serC
  simp

theorem tmul_mem_LamLA (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) {f : W.EE}
    {a : LetA O n} (ha : a ∈ W.AΔ) (hea : (letE c : LetA O n) * a = a)
    (hΛ : algebraMap (LetA O n) W.EE (Eπ ^ h') * f = algebraMap (LetA O n) W.EE a) (z : LcQ W T π' c) :
    f ⊗ₜ z ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [ModelFPf.mem_LamLA, ModelFPf.smulLA_tmul, hΛ]
  exact ⟨⟨a, ha⟩ ⊗ₜ ⟨z, Submodule.mem_top⟩, by rw [ModelFPf.toLA_tmul, hea]⟩

theorem memNL0 (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) {f : W.EE} {a : LetA O n} (ha : a ∈ W.AΔ) (hea : (letE c : LetA O n) * a = a)
    (hΛ : algebraMap (LetA O n) W.EE (Eπ ^ h') * f = algebraMap (LetA O n) W.EE a)
    (x : W.DD T) (hx : x ∈ NcS W T (c - 1))
    (H : ∀ τ ζ, Pt c ζ τ → ∃ m : ℕ, (∀ i < m, coeff i (W.lev c ζ a) = 0) ∧
      valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - m)) :
    f ⊗ₜ mkL W T π' c x hx ∈ NL W T Pt π' Eπ h' c := by
  apply Submodule.subset_span
  refine ⟨1, fun _ => ⟨a, ha⟩, fun _ => x, ⟨fun _ => hx, ?_⟩, ?_⟩
  · rw [Fin.sum_univ_one, ModelFPf.smulLA_tmul, hΛ, hea]
  · intro τ ζ hpt i
    obtain ⟨m, h1, h2⟩ := H τ ζ hpt
    show (∑ j : Fin 1, serC (W.lev c ζ a) (valAt W T c ζ x) i) ∈ _
    rw [Fin.sum_univ_one]
    unfold serC
    split_ifs with hi
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      simp only [Int.toNat_natCast]
      by_cases hlt : k < m
      · rw [h1 k hlt, zero_smul]
        exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (u3upPf_FilC_anti T τ (by omega) h2)
    · exact Submodule.zero_mem _

theorem tmul_mkL_mem_InvL_of_valAt_mem_filC (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n)
    (hπu : IsUnit (algebraMap (LetA O n) W.EE π')) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hP : ∀ τ ζ, Pt c ζ τ → constantCoeff (W.lev c ζ π') ≠ 0)
    (hE : ∀ τ ζ, Pt c ζ τ → ∃ e₁ : PowerSeries LL, W.lev c ζ Eπ = X * e₁ ∧ constantCoeff e₁ ≠ 0)
    (hΓ : ∀ τ ζ, Pt c ζ τ → ∃ u : LL, u ≠ 0 ∧
      ∀ a, W.lev c ζ (W.γA W.gamK a) = rescale u (W.lev c ζ a))
    (f : W.EE) (hf : IsCoord W Pt π' Eπ h' S up b c f) :
    ∃ g : ↥W.AΔ, (∀ τ ζ, Pt c ζ τ → up τ = true → ∀ i < h' - b τ, coeff i (W.lev c ζ g) = 0) ∧
      (∀ τ ζ, Pt c ζ τ → up τ = false → ∀ i < h' + b τ + S, coeff i (W.lev c ζ g) = 0) ∧
      ∀ (T : LocLat G Qp LL O) (x : W.DD T) (hx : x ∈ NcS W T (c - 1)),
        (∀ τ ζ, Pt c ζ τ → ∃ m : ℕ, (∀ i < m, coeff i (W.lev c ζ g) = 0) ∧
          valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - m)) →
        f ⊗ₜ mkL W T π' c x hx ∈ InvL W T Pt π' Eπ h' c ⊤ := by
  obtain ⟨a, ha, hea, hΛ, hup, hdn, g, hg, hγ⟩ := hf
  have hΛu : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow _
  have hef : algebraMap (LetA O n) W.EE (letE c) * f = f := by
    apply hΛu.mul_left_cancel
    rw [← mul_assoc, mul_comm (algebraMap (LetA O n) W.EE (Eπ ^ h')), mul_assoc, hΛ, ← map_mul, hea]
  have hγe : W.γE W.gamK (algebraMap (LetA O n) W.EE (letE c)) = algebraMap (LetA O n) W.EE (letE c) := by
    rw [show W.γE W.gamK (algebraMap (LetA O n) W.EE (letE c)) =
      algebraMap (LetA O n) W.EE (W.γA W.gamK (letE c)) from W.γE_ext _ _, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]
  have hegf : algebraMap (LetA O n) W.EE (letE c) * (W.γE W.gamK f - f) = W.γE W.gamK f - f := by
    rw [mul_sub, hef]
    congr 1
    conv_rhs => rw [← hef]
    rw [map_mul, hγe]
  have heg : (letE c : LetA O n) * g = g := by
    apply W.EE_inj
    apply hπu.mul_left_cancel
    calc algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE (letE c * g)
        = algebraMap (LetA O n) W.EE (letE c) * algebraMap (LetA O n) W.EE (π' * g) := by
          rw [map_mul, map_mul]; ring
      _ = algebraMap (LetA O n) W.EE (letE c) * (algebraMap (LetA O n) W.EE (Eπ ^ h') * (W.γE W.gamK f - f)) := by
          rw [hγ]
      _ = algebraMap (LetA O n) W.EE (Eπ ^ h') * (algebraMap (LetA O n) W.EE (letE c) * (W.γE W.gamK f - f)) := by
          ring
      _ = algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE g := by rw [hegf, hγ, map_mul]
  have hA : W.γA W.gamK (Eπ ^ h') * (π' * g) = Eπ ^ h' * W.γA W.gamK a - W.γA W.gamK (Eπ ^ h') * a := by
    apply W.EE_inj
    have h1 : algebraMap (LetA O n) W.EE (W.γA W.gamK a) =
        W.γE W.gamK (algebraMap (LetA O n) W.EE (Eπ ^ h')) * W.γE W.gamK f := by
      rw [← map_mul, hΛ]; exact (W.γE_ext _ _).symm
    have h2 : algebraMap (LetA O n) W.EE (W.γA W.gamK (Eπ ^ h')) =
        W.γE W.gamK (algebraMap (LetA O n) W.EE (Eπ ^ h')) := (W.γE_ext _ _).symm
    have hγ' : algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE g =
        algebraMap (LetA O n) W.EE (Eπ ^ h') * (W.γE W.gamK f - f) := by rw [← map_mul, hγ]
    simp only [map_mul, map_sub]
    rw [h1, h2, hγ', ← hΛ]
    ring
  have hG0 : ∀ τ ζ, Pt c ζ τ → ∀ (x₀ : LL) (N : ℕ),
      (∀ i < N, coeff i (W.lev c ζ a) = x₀ * coeff i (W.lev c ζ (Eπ ^ h'))) →
      ∀ k < N, coeff k (W.lev c ζ g) = 0 := by
    intro τ ζ hpt x₀ N hx₀
    obtain ⟨e₁, he, he₁⟩ := hE τ ζ hpt
    obtain ⟨u, hu, hu2⟩ := hΓ τ ζ hpt
    have hl := congrArg (W.lev c ζ) hA
    simp only [map_mul, map_sub] at hl
    rw [hu2, hu2, map_pow] at hl
    refine ser_van (W.lev c ζ Eπ) e₁ (W.lev c ζ π') (W.lev c ζ g) (W.lev c ζ a) u x₀ h' N
      he he₁ (hP τ ζ hpt) hu (by linear_combination hl) (fun i hi => ?_)
    rw [hx₀ i hi, map_pow]
  refine ⟨⟨g, hg⟩, fun τ ζ hpt hu => hG0 τ ζ hpt 0 _ fun i hi => ?_, fun τ ζ hpt hd => ?_,
    fun T x hx H => Submodule.mem_inf.2 ⟨tmul_mem_LamLA W T π' Eπ h' c ha hea hΛ _, ?_⟩⟩
  · rw [hup τ ζ hpt hu i (by omega), zero_mul]
  · obtain ⟨x₀, hx₀⟩ := hdn τ ζ hpt hd
    exact hG0 τ ζ hpt x₀ _ hx₀
  · rw [Submodule.mem_comap]
    rw [LinearMap.sub_apply, ModelFPf.γLA_tmul, LinearMap.id_apply, ← TensorProduct.sub_tmul]
    refine Submodule.mem_map.2 ⟨((↑hπu.unit⁻¹ : W.EE) * (W.γE W.gamK f - f)) ⊗ₜ mkL W T π' c x hx,
      memNL0 W T Pt π' Eπ h' c hg heg ?_ x hx H, ?_⟩
    · rw [mul_left_comm, hγ, map_mul, ← mul_assoc, hπu.val_inv_mul, one_mul]
    · rw [ModelFPf.smulLA_tmul, pow_one, ← mul_assoc, hπu.mul_val_inv, one_mul]

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M σ : ℕ} {c : ZMod n}
    {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}

theorem lifts_mono {y y' : ℕ} (h : y ≤ y') {z : W.DD T₂} (H : LiftsBy W F π' Eπ h' y c z) :
    LiftsBy W F π' Eπ h' y' c z := by
  obtain ⟨h1, w, hw, h2⟩ := H
  refine ⟨h1, ((PD.p : ℕ) : O) ^ (y' - y) • w, Submodule.smul_mem _ _ hw, ?_⟩
  rw [LinearMap.map_smul_of_tower, show y' = (y' - y) + y by omega, pow_add, mul_smul,
    Nat.add_sub_cancel, ← smul_sub]
  exact Submodule.smul_mem _ _ h2

variable (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hc1 : IsCrys PD T₁.ρ) (hc2 : IsCrys PD T₂.ρ)
    (hj1 : ∀ τ, JumpsInV PD T₁.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hj2 : ∀ τ, JumpsInV PD T₂.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hMF1 : ModelF W T₁ Pt π' Eπ h' M c α β) (hMF2 : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M)

include hfr hc1 hc2 hj1 hj2 hMF1 hMF2 hM in

theorem core (f : W.EE) (x : W.DD T₂) (hx : x ∈ NcS W T₂ (c - 1)) (x₁ : W.DD T₁)
    (hx₁ : x₁ ∈ NcS W T₁ (c - 1)) (ρ : ℕ)
    (hdiff : W.map F x₁ - ((PD.p : ℕ) : O) ^ ρ • x ∈ PiNS W T₂ π' 1)
    (hI1 : f ⊗ₜ mkL W T₁ π' c x₁ hx₁ ∈ InvL W T₁ Pt π' Eπ h' c ⊤)
    (hI2 : f ⊗ₜ mkL W T₂ π' c x hx ∈ InvL W T₂ Pt π' Eπ h' c ⊤)
    (h1 : f ⊗ₜ mkL W T₂ π' c x hx ∈ LamLA W T₂ π' Eπ h' c ⊤) (y : W.DD T₂) (hy : y ∈ LamPS W T₂ Eπ h' c)
    (hα : α T₂ ⟨_, h1⟩ = mkP W T₂ π' Eπ h' M c y hy) : LiftsBy W F π' Eπ h' ρ c y := by
  have hyI : y ∈ InvS W T₂ π' Eπ h' 1 c := hMF2.2.2.2.1 _ h1 y hy hα hI2
  have hL1 : f ⊗ₜ mkL W T₁ π' c x₁ hx₁ ∈ LamLA W T₁ π' Eπ h' c ⊤ := (Submodule.mem_inf.1 hI1).1
  obtain ⟨w₁, hw₁⟩ := Submodule.Quotient.mk_surjective _ (α T₁ ⟨_, hL1⟩)
  have hw₁I : (w₁ : W.DD T₁) ∈ InvS W T₁ π' Eπ h' 1 c := hMF1.2.2.2.1 _ hL1 w₁ w₁.2 hw₁.symm hI1
  have hmx : W.map F x₁ ∈ NcS W T₂ (c - 1) := u3downPf_map_NcS W F hc1 hc2 (c - 1) hx₁
  have heq : mkL W T₂ π' c (W.map F x₁) hmx = ((PD.p : ℕ) : O) ^ ρ • mkL W T₂ π' c x hx :=
    u3downPf_mkL_eq W T₂ π' c hx hmx _ hdiff
  have hL2 : f ⊗ₜ mkL W T₂ π' c (W.map F x₁) hmx ∈ LamLA W T₂ π' Eπ h' c ⊤ := by
    rw [heq, TensorProduct.tmul_smul]
    exact Submodule.smul_mem _ _ h1
  have hy₂ : W.map F (w₁ : W.DD T₁) ∈ LamPS W T₂ Eπ h' c := univLinkPf_map_LamPS W F hc1 hc2 Eπ h' c w₁.2
  have hnat := (hfr.2 T₁ T₂ F hc1 hc2 hj1 hj2).1 _ hL1 _ hL2 _ w₁.2 hy₂
    ⟨1, fun _ => f, fun _ => x₁, fun _ => hx₁, fun _ => hmx, by simp, by simp⟩ hw₁.symm
  have hsub : (⟨_, hL2⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) = ((PD.p : ℕ) : O) ^ ρ • ⟨_, h1⟩ :=
    Subtype.ext (by simp [heq, TensorProduct.tmul_smul])
  rw [hsub, map_smul, hα] at hnat
  have hJ : Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ ρ • (⟨y, hy⟩ : ↥(LamPS W T₂ Eπ h' c)) - ⟨_, hy₂⟩) =
      (0 : QLamP W T₂ π' Eπ h' M c) := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hnat
  have hP := univLinkPf_PiNS_anti W T₂ π' hM (univLinkPf_JP W T₂ hMF2 hM _ hJ)
  refine ⟨hyI, w₁, hw₁I, ?_⟩
  simpa using hP

include hMF2 hM in

theorem combine (ρ y : ℕ) (o : O) (X XK XN : ↥(LamLA W T₂ π' Eπ h' c ⊤))
    (hX : ((PD.p : ℕ) : O) ^ y • X = o • XK + XN)
    (hK : ∀ z hz, α T₂ XK = mkP W T₂ π' Eπ h' M c z hz → LiftsBy W F π' Eπ h' ρ c z)
    (hN : ∀ z hz, α T₂ XN = mkP W T₂ π' Eπ h' M c z hz → LiftsBy W F π' Eπ h' ρ c z)
    (z : W.DD T₂) (hz : z ∈ LamPS W T₂ Eπ h' c) (hα : α T₂ X = mkP W T₂ π' Eπ h' M c z hz)
    (hzI : z ∈ InvS W T₂ π' Eπ h' 1 c) : LiftsBy W F π' Eπ h' (ρ + y) c z := by
  obtain ⟨zK, hzK⟩ := Submodule.Quotient.mk_surjective _ (α T₂ XK)
  obtain ⟨zN, hzN⟩ := Submodule.Quotient.mk_surjective _ (α T₂ XN)
  obtain ⟨-, wK, hwK, hK'⟩ := hK zK zK.2 hzK.symm
  obtain ⟨-, wN, hwN, hN'⟩ := hN zN zN.2 hzN.symm
  have h1 := congrArg (α T₂) hX
  rw [map_smul, map_add, map_smul, hα, ← hzK, ← hzN] at h1
  have hJ : Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ y • (⟨z, hz⟩ : ↥(LamPS W T₂ Eπ h' c)) -
      (o • zK + zN)) = (0 : QLamP W T₂ π' Eπ h' M c) := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_add,
      Submodule.Quotient.mk_smul, sub_eq_zero]
    exact h1
  have hP : ((PD.p : ℕ) : O) ^ y • z - (o • (zK : W.DD T₂) + zN) ∈ PiNS W T₂ π' 1 :=
    univLinkPf_PiNS_anti W T₂ π' hM (univLinkPf_JP W T₂ hMF2 hM _ hJ)
  refine ⟨hzI, o • wK + wN, Submodule.add_mem _ (Submodule.smul_mem _ _ hwK) hwN, ?_⟩
  have h2 := Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ (((PD.p : ℕ) : O) ^ ρ) hP) (Submodule.smul_mem _ o hK')) hN'
  convert h2 using 1
  rw [map_add, LinearMap.map_smul_of_tower, pow_add]
  module

theorem NL_rep (T : LocLat G Qp LL O) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) :
    x ∈ NLset W T Pt π' Eπ h' c := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun j => j.elim0, by simp⟩, fun τ ζ _ i => ?_⟩
    simp [expS]
  | add x y _ _ hx hy =>
    obtain ⟨m, a, u, ⟨hu, hx1⟩, hx2⟩ := hx
    obtain ⟨m', a', u', ⟨hu', hy1⟩, hy2⟩ := hy
    let U : Fin (m + m') → ↥(NcS W T (c - 1)) :=
      Fin.append (fun j => ⟨u j, hu j⟩) (fun j => ⟨u' j, hu' j⟩)
    refine ⟨m + m', Fin.append a a', fun j => U j, ⟨fun j => (U j).2, ?_⟩, fun τ ζ hpt i => ?_⟩
    · rw [map_add, hx1, hy1, Fin.sum_univ_add]
      simp only [U, Fin.append_left, Fin.append_right]
    · have := Submodule.add_mem _ (hx2 τ ζ hpt i) (hy2 τ ζ hpt i)
      unfold expS at this ⊢
      rw [Fin.sum_univ_add]
      simpa only [U, Fin.append_left, Fin.append_right] using this
  | smul o x _ hx =>
    obtain ⟨m, a, u, ⟨hu, hx1⟩, hx2⟩ := hx
    refine ⟨m, fun j => o • a j, u, ⟨hu, ?_⟩, fun τ ζ hpt i => ?_⟩
    · rw [map_smul, hx1, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm, algE_smul]
    · have := Submodule.smul_mem _ (algebraMap O LL o) (hx2 τ ζ hpt i)
      convert this using 1
      unfold expS serC
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · beta_reduce
        rw [Subalgebra.coe_smul, lev_smul, smul_smul]
      · rw [smul_zero]

include hfr hc1 hc2 hj1 hj2 hMF1 hMF2 in

theorem compare {ρ : ℕ} (hW : WKill W F ρ) (hNL : NinLam W T₁ Eπ h') (V₂ : ValH W T₂ Pt π' c)
    (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hh : 1 ≤ h')
    (hE : ∀ τ ζ, Pt c ζ τ → ∃ e₁ : PowerSeries LL, W.lev c ζ Eπ = X * e₁ ∧ constantCoeff e₁ ≠ 0)
    {f₀ : W.EE} {a₀ : LetA O n} (hea : (letE c : LetA O n) * a₀ = a₀)
    (hΛ : algebraMap (LetA O n) W.EE (Eπ ^ h') * f₀ = algebraMap (LetA O n) W.EE a₀)
    (x : W.DD T₂) (hx : x ∈ NcS W T₂ (c - 1)) (hN : f₀ ⊗ₜ mkL W T₂ π' c x hx ∈ NL W T₂ Pt π' Eπ h' c) :
    ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T₁), (∀ j, y j ∈ NcS W T₁ (c - 1)) ∧
      (∀ τ ζ, Pt c ζ τ → Gd (Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₁ τ) h' (fun j => evA W c ζ (a j))
        (fun j => valAt W T₁ c ζ (y j))) ∧
      ∀ τ ζ, Pt c ζ τ → ∀ i ≤ h', ∑ j, coeff i (evA W c ζ (a j)) • valAt W T₂ c ζ (W.map F (y j)) =
        coeff i (C ((PD.p : LL) ^ (ρ + 2 * σ)) * W.lev c ζ a₀) • valAt W T₂ c ζ x := by
  have hx₀ := ModelFPf.NL_le_LamLA W T₂ π' Eπ h' c Pt hN
  obtain ⟨n₂, hn₂, hn₂N, hα⟩ := hMF2.1 _ hx₀ hN
  obtain ⟨n₁, hn₁, hF⟩ := hW c n₂ hn₂N
  obtain ⟨ν, hν, hνN, hβ⟩ := hMF1.2.1 n₁ (hNL c hn₁) hn₁
  obtain ⟨m, a, y, ⟨hy, hrep⟩, hfil⟩ := NL_rep W T₁ hνN
  have hΛu : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow _
  have hy2 : ∀ j, W.map F (y j) ∈ NcS W T₂ (c - 1) := fun j => u3downPf_map_NcS W F hc1 hc2 _ (hy j)
  set e : Fin m → W.EE := fun j =>
    (↑hΛu.unit⁻¹ : W.EE) * algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) with he
  have hΛe : ∀ (T : LocLat G Qp LL O) (z : Fin m → LcQ W T π' c),
      smulLA W T π' c (Eπ ^ h') (∑ j, e j ⊗ₜ z j) =
        ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ z j := by
    intro T z
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ModelFPf.smulLA_tmul, he, ← mul_assoc, hΛu.mul_val_inv, one_mul]
  have hinjΛ : Function.Injective (smulLA W T₁ π' c (Eπ ^ h')) := by
    have hl : ∀ z, TensorProduct.map (LinearMap.mulLeft O (↑hΛu.unit⁻¹ : W.EE)) LinearMap.id
        (smulLA W T₁ π' c (Eπ ^ h') z) = z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul u w =>
        rw [ModelFPf.smulLA_tmul, TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_apply,
          ← mul_assoc, hΛu.val_inv_mul, one_mul]
      | add u w hu hw => simp only [map_add, hu, hw]
    exact Function.LeftInverse.injective hl
  have hν1 : ν = ∑ j, e j ⊗ₜ mkL W T₁ π' c (y j) (hy j) := hinjΛ (by rw [hrep, hΛe])
  have hν₂ : ∑ j, e j ⊗ₜ mkL W T₂ π' c (W.map F (y j)) (hy2 j) ∈ LamLA W T₂ π' Eπ h' c ⊤ := by
    rw [ModelFPf.mem_LamLA, hΛe]
    exact ModelFPf.rep_mem W T₂ π' c _ (fun j => (a j).2) _ hy2
  have hy₂ : W.map F n₁ ∈ LamPS W T₂ Eπ h' c := univLinkPf_map_LamPS W F hc1 hc2 Eπ h' c (hNL c hn₁)
  have hβ₂ := (hfr.2 T₁ T₂ F hc1 hc2 hj1 hj2).2 n₁ (hNL c hn₁) hy₂ ν hν _ hν₂
    ⟨m, e, y, hy, hy2, hν1, rfl⟩ hβ
  have hβα := (hfr.1 T₂ hc2 hj2).2.2.1 _ hx₀ n₂ hn₂ hα
  have hsub : (⟨_, hy₂⟩ : ↥(LamPS W T₂ Eπ h' c)) = ((PD.p : ℕ) : O) ^ ρ • ⟨n₂, hn₂⟩ := Subtype.ext hF
  rw [hsub, map_smul, hβα] at hβ₂
  unfold mkLA at hβ₂
  rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, Submodule.mem_comap] at hβ₂
  obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 hβ₂
  obtain ⟨m', b, z, hz, rfl⟩ := ModelFPf.range_rep W T₂ π' c u hu
  have hue' := congrArg (smulLA W T₂ π' c (Eπ ^ h')) hue
  simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul] at hue'
  rw [map_sub, hΛe, ModelFPf.smulLA_smulLA, ModelFPf.smulLA_rep, map_smul, map_smul,
    ModelFPf.smulLA_tmul, hΛ] at hue'
  refine ⟨m, a, y, hy, fun τ ζ hpt i => ?_, fun τ ζ hpt i hi => ?_⟩
  · have := hfil τ ζ hpt i
    rw [expS_nat] at this
    exact this
  · let Zs : Fin (m' + 1) → ↥(NcS W T₂ (c - 1)) := Fin.cons ⟨x, hx⟩ fun k => ⟨z k, hz k⟩
    let Bs : Fin (m' + 1) → LetA O n := Fin.cons (algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ (ρ + 2 * σ)) * a₀)
      fun k => Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * b k
    have hwd := V₂.wd τ ζ hpt (fun j => (a j : LetA O n)) (fun j => W.map F (y j)) hy2 Bs
      (fun k => Zs k) (fun k => (Zs k).2) (by
        rw [Fin.sum_univ_succ]
        simp only [Zs, Bs, Fin.cons_zero, Fin.cons_succ]
        rw [hue', mul_left_comm, hea, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def,
          ← TensorProduct.smul_tmul', smul_smul, ← pow_add]
        abel)
    have h1 := congrFun hwd (i : ℤ)
    rw [expS_nat, expS_nat, Fin.sum_univ_succ] at h1
    simp only [Zs, Bs, Fin.cons_zero, Fin.cons_succ] at h1
    obtain ⟨e₁, he₁, -⟩ := hE τ ζ hpt
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun k : Fin m' => coeff i
      (W.lev c ζ (Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * b k)) • valAt W T₂ c ζ (z k)) fun k _ => by
        rw [show Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * b k = Eπ ^ (3 * h') * (Eπ ^ h' * π' ^ M * b k) by ring,
          map_mul, map_pow, van_of_dvd he₁ _ i (by omega), zero_smul], add_zero, map_mul, lev_alg, map_pow,
      map_natCast] at h1
    exact h1

end Core

end Formalism.MainNotions.N.Ln34.LevelExpansions

end
end
