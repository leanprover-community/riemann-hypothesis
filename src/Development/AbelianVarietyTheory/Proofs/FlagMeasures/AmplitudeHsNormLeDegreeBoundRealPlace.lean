import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import BuildAid.ForwardExisting
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymmStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationDegenerateSidePieceBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormDetInnerLeOfDetEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramSchmidtLengths
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairings
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalData

section
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem dyad_cauchySchwarz {X : Type} [MeasurableSpace X] (μ : Measure X) (A B : X → ℝ)
    (hA : Measurable A) (hB : Measurable B) (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (h1 : ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ ≤ ENNReal.ofReal (P ^ 2))
    (h2 : ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ ≤ ENNReal.ofReal (Q ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ ≤ ENNReal.ofReal (P * Q) := by
  have hc : 0 < Q / (2 * P) := by positivity
  have hd : 0 < P / (2 * Q) := by positivity
  have hpt : ∀ x, ENNReal.ofReal (A x * B x) ≤
      ENNReal.ofReal (Q / (2 * P)) * ENNReal.ofReal (A x ^ 2)
        + ENNReal.ofReal (P / (2 * Q)) * ENNReal.ofReal (B x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hd.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : Q / (2 * P) * A x ^ 2 + P / (2 * Q) * B x ^ 2 - A x * B x
        = (Q * A x - P * B x) ^ 2 / (2 * P * Q) := by
      field_simp; ring
    have h0 : 0 ≤ (Q * A x - P * B x) ^ 2 / (2 * P * Q) := by positivity
    linarith
  have mA : Measurable fun x => ENNReal.ofReal (A x ^ 2) := by fun_prop
  have mB : Measurable fun x => ENNReal.ofReal (B x ^ 2) := by fun_prop
  calc _ ≤ _ := lintegral_mono hpt
    _ = ENNReal.ofReal (Q / (2 * P)) * ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ
        + ENNReal.ofReal (P / (2 * Q)) * ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ := by
      rw [lintegral_add_left (mA.const_mul _), lintegral_const_mul _ mA, lintegral_const_mul _ mB]
    _ ≤ ENNReal.ofReal (Q / (2 * P)) * ENNReal.ofReal (P ^ 2)
        + ENNReal.ofReal (P / (2 * Q)) * ENNReal.ofReal (Q ^ 2) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hd.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp; ring

theorem dyad_exists_shell (H s : ℝ) (hH : 0 < H) :
    ∃ i : ℕ, s ≤ 2 ^ (i + 1) * H ∧ (i = 0 ∨ 2 ^ i * H < s) := by
  have hex : ∃ i : ℕ, s ≤ 2 ^ (i + 1) * H := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / H) (one_lt_two (α := ℝ))
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hH] at hn
    have : (0:ℝ) < 2 ^ n * H := by positivity
    rw [pow_succ]; linarith
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | k
  · exact Or.inl rfl
  · right
    have := Nat.find_min hex (m := k) (by omega)
    exact not_le.mp this

theorem dyad_exists_down (M y : ℝ) (hy : 0 < y) (hM : y ≤ M) :
    ∃ a : ℕ, M / 2 ^ (a + 1) < y ∧ y ≤ 2 * (M / 2 ^ (a + 1)) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := M / y) (y := 2)
    (by rw [le_div_iff₀ hy]; linarith) one_lt_two
  refine ⟨n, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hy] at h2; linarith
  · rw [le_div_iff₀ hy] at h1
    have : 2 * (M / 2 ^ (n + 1)) = M / 2 ^ n := by field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]; linarith

theorem dyad_piece_real (r k e n : ℕ) (H De N sg u v w : ℝ) (hr : 1 ≤ r) (hH : 0 < H)
    (hDe : 0 < De) (hN : 0 < N) (hsg : 1 ≤ sg) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hwN : w ≤ N) (hwM : w ≤ ((u * (2 * H)) ^ r * De) ^ 2 * v)
    (hNR : 1 ≤ N * (u * (2 * H)) ^ (2 * r)) (hsu : sg ≤ u ^ r) :
    (u * (2 * H)) ^ e * w ^ (k + 1) * (u ^ (e + 4 * r + 1 + n))⁻¹ ≤
      (2 * H) ^ (e + 4 * r) * De ^ 2 * N ^ (k + 1) * sg ^ (-((n : ℝ) / r)) * (u⁻¹ * v) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have h1 : (u ^ n)⁻¹ ≤ sg ^ (-((n : ℝ) / r)) := by
    rw [Real.rpow_neg (by linarith)]
    apply inv_anti₀ (by positivity)
    calc sg ^ ((n : ℝ) / r) ≤ (u ^ r) ^ ((n : ℝ) / r) := by gcongr
      _ = u ^ n := by
        rw [← Real.rpow_natCast u r, ← Real.rpow_mul hu.le, ← Real.rpow_natCast u n]
        congr 1; field_simp
  have h2 : w ^ (k + 1) ≤ N ^ (k + 1) * (u * (2 * H)) ^ (4 * r) * De ^ 2 * v := by
    calc w ^ (k + 1) = w ^ k * w * 1 := by ring
      _ ≤ N ^ k * (((u * (2 * H)) ^ r * De) ^ 2 * v) * (N * (u * (2 * H)) ^ (2 * r)) := by
        gcongr
      _ = _ := by ring
  calc _ ≤ (u * (2 * H)) ^ e * (N ^ (k + 1) * (u * (2 * H)) ^ (4 * r) * De ^ 2 * v)
        * (u ^ (e + 4 * r + 1 + n))⁻¹ := by gcongr
    _ = (2 * H) ^ (e + 4 * r) * De ^ 2 * N ^ (k + 1) * (u ^ n)⁻¹ * (u⁻¹ * v) := by
      rw [mul_pow u, mul_pow u]
      field_simp
      ring
    _ ≤ _ := by gcongr

theorem dyad_tsum_four (c : ℝ≥0∞) :
    ∑' p : ℕ × ℕ × ℕ × ℕ, c * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2)))
      = 16 * c := by
  have g : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by
    rw [ENNReal.tsum_geometric]; simp
  rw [ENNReal.tsum_mul_left]
  simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, g]
  ring

theorem dyadic_summation : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r j kk e q : ℕ) (H₁ De D K K' sg : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → e + 4 * r + 2 ≤ q → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → 1 ≤ sg → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ (i + 1) * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ < S x) ∧ S' x ≤ 2 ^ (i' + 1) * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * q))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < S' x) ∧ S x ≤ 2 ^ (i + 1) * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * q))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (16 * Real.sqrt (K * K') * (2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ kk * sg ^ (-(((q : ℝ) - e - 4 * r - 1) / r))) := by
  intro X _ ν A B S S' Y Y' r j kk e q H₁ De D K K' sg hA hB _ _ _ _ hr hkk hq hH hDe hD hK hK'
    hsg hae h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, kk = k + 1 := ⟨kk - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = e + 4 * r + 1 + n := ⟨q - (e + 4 * r + 1), by omega⟩
  have hexp : ((e + 4 * r + 1 + n : ℕ) : ℝ) - e - 4 * r - 1 = n := by push_cast; ring
  rw [hexp]
  have hH0 : 0 < H₁ := by linarith
  have hDe0 : 0 < De := by linarith
  set C : ℝ := Real.sqrt (K * K') * ((2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k + 1)
    * sg ^ (-((n : ℝ) / r))) with hC
  have hC0 : 0 ≤ C := by positivity
  let M : ℕ → ℕ → ℝ := fun i i' => (2 ^ (i + i' + 1) * H₁) ^ r * De
  have hM0 : ∀ i i', 0 < M i i' := fun i i' => by positivity
  let P : ℕ × ℕ × ℕ × ℕ → Set X := fun p => {x |
    (0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) ∧
    (S x ≤ 2 ^ (p.1 + 1) * H₁ ∧ (p.1 = 0 ∨ 2 ^ p.1 * H₁ < S x)) ∧
    (S' x ≤ 2 ^ (p.2.1 + 1) * H₁ ∧ (p.2.1 = 0 ∨ 2 ^ p.2.1 * H₁ < S' x)) ∧
    (M p.1 p.2.1 / 2 ^ (p.2.2.1 + 1) < Y x ∧ Y x ≤ 2 * (M p.1 p.2.1 / 2 ^ (p.2.2.1 + 1))) ∧
    (M p.1 p.2.1 / 2 ^ (p.2.2.2 + 1) < Y' x ∧ Y' x ≤ 2 * (M p.1 p.2.1 / 2 ^ (p.2.2.2 + 1)))}
  have hcov : ∀ᵐ x ∂ν, x ∈ ⋃ p, P p := by
    filter_upwards [hae] with x hx
    obtain ⟨i, hi⟩ := dyad_exists_shell H₁ (S x) hH0
    obtain ⟨i', hi'⟩ := dyad_exists_shell H₁ (S' x) hH0
    have hmax : max (S x) (S' x) ^ r * De ≤ M i i' := by
      have a1 : (2:ℝ) ^ (i + 1) ≤ 2 ^ (i + i' + 1) := pow_le_pow_right₀ one_le_two (by omega)
      have a2 : (2:ℝ) ^ (i' + 1) ≤ 2 ^ (i + i' + 1) := pow_le_pow_right₀ one_le_two (by omega)
      have a3 : max (S x) (S' x) ≤ 2 ^ (i + i' + 1) * H₁ :=
        max_le (hi.1.trans (by gcongr)) (hi'.1.trans (by gcongr))
      have a4 : 0 ≤ max (S x) (S' x) := le_max_of_le_left (by linarith [hx.2.2.1])
      show _ ≤ (2 ^ (i + i' + 1) * H₁) ^ r * De
      gcongr
    obtain ⟨a, ha⟩ := dyad_exists_down (M i i') (Y x) hx.2.2.2.2.1
      (hx.2.2.2.2.2.2.2.2.1.trans hmax)
    obtain ⟨b, hb⟩ := dyad_exists_down (M i i') (Y' x) hx.2.2.2.2.2.1
      (hx.2.2.2.2.2.2.2.2.2.1.trans hmax)
    exact Set.mem_iUnion.2 ⟨(i, i', a, b), hx, hi, hi', ha, hb⟩
  have hpiece : ∀ p : ℕ × ℕ × ℕ × ℕ, ∫⁻ x in P p, ENNReal.ofReal (A x * B x) ∂ν ≤
      ENNReal.ofReal C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2))) := by
    rintro ⟨i, i', a, b⟩
    rcases (P (i, i', a, b)).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he]; simp
    obtain ⟨⟨-, -, s1, s2, y1, y2, g1, g2, -, -, g3⟩, ⟨b1, -⟩, ⟨b2, -⟩, ⟨c1, -⟩, ⟨c2, -⟩⟩ := hx
    simp only at b1 b2 c1 c2 ⊢
    have hm := hM0 i i'
    set y : ℝ := M i i' / 2 ^ (a + 1) with hy
    set y' : ℝ := M i i' / 2 ^ (b + 1) with hy'
    have hy0 : 0 < y := by positivity
    have hy0' : 0 < y' := by positivity
    set R : ℝ := 2 ^ (i + i' + 1) * H₁ with hR
    have hR0 : 0 < R := by positivity
    set q := e + 4 * r + 1 + n with hqdef
    have i1 : ∫⁻ x in P (i, i', a, b), ENNReal.ofReal (A x ^ 2) ∂ν ≤
        ENNReal.ofReal ((Real.sqrt K * Real.sqrt (R ^ e) * y ^ (k + 1) * (((2:ℝ) ^ i) ^ q)⁻¹) ^ 2) := by
      refine le_trans (lintegral_mono_set ?_) ((h1 i i' y hy0).trans (le_of_eq ?_))
      · intro z hz
        exact ⟨hz.2.1.1, hz.2.1.2, hz.2.2.1.1, hz.2.2.2.1.1, hz.2.2.2.1.2⟩
      · congr 1
        rw [← hR, mul_pow _ _ 2, mul_pow _ _ 2, mul_pow _ _ 2, Real.sq_sqrt hK.le, Real.sq_sqrt (by positivity), inv_pow,
          ← pow_mul y, ← pow_mul _ q, mul_comm q 2, mul_comm (k + 1) 2]
    have i2 : ∫⁻ x in P (i, i', a, b), ENNReal.ofReal (B x ^ 2) ∂ν ≤
        ENNReal.ofReal ((Real.sqrt K' * Real.sqrt (R ^ e) * y' ^ (k + 1) * (((2:ℝ) ^ i') ^ q)⁻¹) ^ 2) := by
      refine le_trans (lintegral_mono_set ?_) ((h2 i i' y' hy0').trans (le_of_eq ?_))
      · intro z hz
        exact ⟨hz.2.2.1.1, hz.2.2.1.2, hz.2.1.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩
      · congr 1
        rw [← hR, mul_pow _ _ 2, mul_pow _ _ 2, mul_pow _ _ 2, Real.sq_sqrt hK'.le, Real.sq_sqrt (by positivity), inv_pow,
          ← pow_mul y', ← pow_mul _ q, mul_comm q 2, mul_comm (k + 1) 2]
    refine (dyad_cauchySchwarz _ A B hA hB _ _ (by positivity) (by positivity) i1 i2).trans ?_
    have hrhs : ENNReal.ofReal C * (2⁻¹ ^ i * (2⁻¹ ^ i' * (2⁻¹ ^ a * 2⁻¹ ^ b))) =
        ENNReal.ofReal (C * (((2:ℝ) ^ (i + i'))⁻¹ * ((2:ℝ) ^ (a + b))⁻¹)) := by
      have e2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (2⁻¹ : ℝ) := by
        rw [ENNReal.ofReal_inv_of_pos two_pos]; simp
      rw [ENNReal.ofReal_mul hC0, e2]
      congr 1
      simp only [← ENNReal.ofReal_pow (show (0:ℝ) ≤ 2⁻¹ by norm_num)]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_add, pow_add]; simp only [inv_pow]; field_simp
    rw [hrhs]
    apply ENNReal.ofReal_le_ofReal
    have hRu : R = 2 ^ (i + i') * (2 * H₁) := by rw [hR]; ring
    have hu1 : (1:ℝ) ≤ 2 ^ (i + i') := one_le_pow₀ one_le_two
    have hSS : S x * S' x ≤ 2 ^ (i + i') * (2 * H₁) ^ 2 := by
      calc S x * S' x ≤ (2 ^ (i + 1) * H₁) * (2 ^ (i' + 1) * H₁) := by
            apply mul_le_mul b1 b2 (by linarith) (by positivity)
        _ = _ := by ring
    have hSS0 : 0 ≤ S x * S' x := mul_nonneg (by linarith) (by linarith)
    have hSSr : (S x * S' x) ^ r ≤ (2 ^ (i + i')) ^ r * (2 * H₁) ^ (2 * r) := by
      rw [pow_mul, ← mul_pow]; gcongr
    have key := dyad_piece_real r k e n H₁ De (2 ^ j / D) sg (2 ^ (i + i')) ((2 ^ (a + b))⁻¹)
      (y * y') hr hH0 hDe0 (by positivity) hsg (by positivity) (by positivity) (by positivity)
      (by
        rw [le_div_iff₀ hD]
        refine le_trans ?_ g1
        gcongr)
      (by
        rw [← hRu]
        have : y * y' = (R ^ r * De) ^ 2 * (2 ^ (a + b))⁻¹ / 4 := by
          rw [hy, hy']
          show (R ^ r * De) / _ * ((R ^ r * De) / _) = _
          field_simp; ring
        rw [this]
        have : 0 ≤ (R ^ r * De) ^ 2 * ((2:ℝ) ^ (a + b))⁻¹ := by positivity
        linarith)
      (by
        rw [div_mul_eq_mul_div, le_div_iff₀ hD, one_mul]
        have j1 : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
        have : ((2:ℝ) ^ (i + i')) ^ r ≤ (2 ^ (i + i')) ^ (2 * r) :=
          pow_le_pow_right₀ hu1 (by omega)
        calc D ≤ (2 ^ (i + i')) ^ r * (2 * H₁) ^ (2 * r) := g2.trans hSSr
          _ ≤ (2 ^ (i + i')) ^ (2 * r) * (2 * H₁) ^ (2 * r) := by gcongr
          _ = 1 * (2 ^ (i + i') * (2 * H₁)) ^ (2 * r) := by rw [mul_pow _ (2 * H₁), one_mul]
          _ ≤ _ := by gcongr)
      (by
        refine g3.trans (max_le (one_le_pow₀ hu1) ?_)
        rw [div_le_iff₀ (by positivity)]
        exact hSSr)
    rw [← hRu, ← hqdef] at key
    have hsq : Real.sqrt (R ^ e) * Real.sqrt (R ^ e) = R ^ e := Real.mul_self_sqrt (by positivity)
    calc _ = Real.sqrt (K * K') * ((Real.sqrt (R ^ e) * Real.sqrt (R ^ e)) * (y * y') ^ (k + 1)
            * (((2:ℝ) ^ (i + i')) ^ q)⁻¹) := by
          rw [Real.sqrt_mul hK.le, mul_pow y, pow_add 2 i i', mul_pow _ _ q, mul_inv]; ring
      _ ≤ Real.sqrt (K * K') * ((2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k + 1)
            * sg ^ (-((n : ℝ) / r)) * (((2:ℝ) ^ (i + i'))⁻¹ * ((2:ℝ) ^ (a + b))⁻¹)) := by
          rw [hsq]; gcongr
      _ = _ := by rw [hC]; ring
  calc _ = ∫⁻ x in ⋃ p, P p, ENNReal.ofReal (A x * B x) ∂ν := by
        rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ _ := lintegral_iUnion_le _ _
    _ ≤ _ := ENNReal.tsum_le_tsum hpiece
    _ = 16 * ENNReal.ofReal C := dyad_tsum_four _
    _ = ENNReal.ofReal (16 * C) := by
        rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 16 by norm_num), ENNReal.ofReal_ofNat]
    _ = _ := by rw [hC]; congr 1; ring

end GlobalTheory.Amp
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dyadic_summation_with_decay : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r j kk e q : ℕ) (H₁ De D K K' sg : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → e + 4 * r + 2 ≤ q → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → 1 ≤ sg → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ (i + 1) * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ < S x) ∧ S' x ≤ 2 ^ (i' + 1) * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * q))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < S' x) ∧ S x ≤ 2 ^ (i + 1) * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * q))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (16 * Real.sqrt (K * K') * (2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ kk * sg ^ (-(((q : ℝ) - e - 4 * r - 1) / r))) := by
  atlas_forward_decl GlobalTheory.Amp.dyadic_summation
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
open ReciprocityTheory.ChartRestriction.DS.Xi.StepA (herm_add_l herm_add_r herm_sub_l herm_sub_r herm_smul_l herm_smul_r herm_zero_l herm_zero_r
  herm_UH Hpk_mulVec Hpk_conjT)

namespace GlobalTheory.Amp.ExtPow

theorem gram_core {n j : ℕ} (P P' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v v' : Fin j → Fin n → ℂ)
    (M : Matrix (Fin j) (Fin j) ℂ)
    (h : ∀ p ∈ P, ∀ p' ∈ P', ‖∑ a, ∑ b, (star (v a) ⬝ᵥ p.ofLp) * M a b * star (star (v' b) ⬝ᵥ p'.ofLp)‖ ≤ 2 * ‖p‖ * ‖p'‖) :
    gramProj P v * gramProj P' v' * ‖M.det‖ ≤ 2 ^ j := by
  have hA : ∀ (Q : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (u : Fin j → Fin n → ℂ),
      ∃ A : Matrix (Fin j) (Fin n) ℂ, (Matrix.gram ℂ fun a => Q.starProjection (WithLp.toLp 2 (u a))) = A * Aᴴ ∧
        ∀ w : Fin n → ℂ, ∑ i, ‖w i‖ ^ 2 ≤ 1 → ∃ p ∈ Q, ‖p‖ ≤ 1 ∧ ∀ a, (A *ᵥ w) a = star (u a) ⬝ᵥ p.ofLp := by
    intro Q u
    refine ⟨Matrix.of fun a i => star ((Q.starProjection (WithLp.toLp 2 (u a))).ofLp i), ?_, ?_⟩
    · ext a b
      rw [Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro l _
      simp [Matrix.conjTranspose_apply, mul_comm]
    · intro w hw
      refine ⟨Q.starProjection (WithLp.toLp 2 w), Q.starProjection_apply_mem _, ?_, fun a => ?_⟩
      · refine (Q.norm_starProjection_apply_le _).trans ?_
        rw [EuclideanSpace.norm_eq]
        simpa using Real.sqrt_le_one.2 hw
      · have e1 : ⟪Q.starProjection (WithLp.toLp 2 (u a)), WithLp.toLp 2 w⟫_ℂ =
            ⟪WithLp.toLp 2 (u a), Q.starProjection (WithLp.toLp 2 w)⟫_ℂ := Q.inner_starProjection_left_eq_right _ _
        rw [PiLp.inner_apply, PiLp.inner_apply] at e1
        simp only [Matrix.mulVec, dotProduct, Pi.star_apply]
        simpa [mul_comm] using e1
  obtain ⟨A, hA1, hA2⟩ := hA P v
  obtain ⟨A', hA1', hA2'⟩ := hA P' v'
  unfold gramProj
  rw [hA1, hA1']
  apply Formalism.HermitianLatticeCounting.P.exterior_power_bound j n A A' M
  intro w₁ w₂ h₁ h₂
  obtain ⟨p, hp, hp1, hp2⟩ := hA2 w₁ h₁
  obtain ⟨p', hp', hp1', hp2'⟩ := hA2' w₂ h₂
  simp only [hp2, hp2']
  refine (h p hp p' hp').trans ?_
  have := norm_nonneg p
  have := norm_nonneg p'
  nlinarith [mul_le_mul hp1 hp1' this zero_le_one]

theorem herm_conj {k r : ℕ} (u v : Fin (2 * r + k + 1) → ℂ) :
    star (herm (Hpk k r) u v) = herm (Hpk k r) v u := by
  unfold herm
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, Hpk_conjT, ← Matrix.dotProduct_mulVec]

theorem herm_cs {k r : ℕ} (S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ))
    (hS : ∀ v ∈ S, 0 ≤ (herm (Hpk k r) v v).re) (u v : Fin (2 * r + k + 1) → ℂ) (hu : u ∈ S) (hv : v ∈ S) :
    ‖herm (Hpk k r) u v‖ ^ 2 ≤ (herm (Hpk k r) u u).re * (herm (Hpk k r) v v).re := by
  let c : PreInnerProductSpace.Core ℂ S :=
    { inner := fun x y => herm (Hpk k r) y x
      conj_inner_symm := fun x y => herm_conj _ _
      re_inner_nonneg := fun x => hS x x.2
      add_left := fun x y z => herm_add_r _ _ _ _
      smul_left := fun x y a => herm_smul_r _ _ _ _ }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ S _ _ _ c ⟨u, hu⟩ ⟨v, hv⟩
  change ‖herm (Hpk k r) v u‖ * ‖herm (Hpk k r) u v‖ ≤ (herm (Hpk k r) u u).re * (herm (Hpk k r) v v).re at h
  rw [← herm_conj u v, norm_star] at h
  rw [sq]; exact h

def Low {n : ℕ} (m : ℕ) (v : Fin n → ℂ) : Prop := ∀ i : Fin n, m ≤ i.val → v i = 0

theorem low_of_mem {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xsp k r) : Low r v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    intro i hi
    have := a.isLt
    apply Pi.single_eq_of_ne
    intro h; rw [h] at hi; simp [eI] at hi; omega
  | zero => intro i _; rfl
  | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
  | smul a x _ hx => intro i hi; simp [hx i hi]

theorem low_eq {k r j : ℕ} (hj : j ≤ r) {v : Fin (2 * r + k + 1) → ℂ} (hv : Low j v) :
    v = ∑ a : Fin j, v (eI k r (Fin.castLE hj a)) • bvec (eI k r (Fin.castLE hj a)) := by
  ext i
  rw [Finset.sum_apply]
  by_cases hi : i.val < j
  · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · simp [bvec, eI]
    · intro b _ hb
      have : i ≠ eI k r (Fin.castLE hj b) := fun h => hb (Fin.ext (congrArg Fin.val h).symm)
      simp [bvec, Pi.single_eq_of_ne this]
    · simp
  · rw [hv i (by omega), eq_comm]
    apply Finset.sum_eq_zero
    intro b _
    have : i ≠ eI k r (Fin.castLE hj b) := fun h => hi (by rw [h]; exact b.isLt)
    simp [bvec, Pi.single_eq_of_ne this]

theorem low_N {k r j : ℕ} (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : Low j v) :
    Low j (n *ᵥ v) := by
  intro i hi
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : j ≤ l.val
  · rw [hv l hl, mul_zero]
  · have h := hn.2.1 ⟨l.val, by omega⟩ i (by simp; omega)
    have e : eI k r ⟨l.val, by omega⟩ = l := rfl
    rw [e, if_neg (fun h => by rw [h] at hi; omega)] at h
    rw [h, zero_mul]

theorem herm_low {k r : ℕ} {u v : Fin (2 * r + k + 1) → ℂ} (hu : ∀ a : Fin r, herm (Hpk k r) u (bvec (eI k r a)) = 0)
    (hv : Low r v) : herm (Hpk k r) u v = 0 := by
  rw [low_eq le_rfl hv]
  have : ∀ s : Finset (Fin r), herm (Hpk k r) u (∑ a ∈ s, v (eI k r (Fin.castLE le_rfl a)) • bvec (eI k r (Fin.castLE le_rfl a))) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [herm_zero_r]
    | insert a s ha ih => rw [Finset.sum_insert ha, herm_add_r, ih, herm_smul_r, hu]; simp
  exact this _

theorem herm_e {k r : ℕ} (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (eI k r a)) = u (esI k r a) := by
  have : star (bvec (eI k r a)) = bvec (eI k r a) := by simp [bvec]
  unfold herm
  rw [this, bvec, single_one_dotProduct, Hpk_mulVec, if_pos (Or.inl (show (eI k r a).val < r from a.isLt))]
  rfl

theorem herm_low_low {k r : ℕ} {u v : Fin (2 * r + k + 1) → ℂ} (hu : Low r u) (hv : Low r v) :
    herm (Hpk k r) u v = 0 := by
  apply herm_low _ hv
  intro a
  rw [herm_e]
  apply hu
  have := a.isLt
  simp only [esI]; omega

theorem herm_nonneg {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {v : Fin (2 * r + k + 1) → ℂ} (he : ∀ a : Fin r, herm (Hpk k r) v (bvec (eI k r a)) = 0)
    (hvz : herm (Hpk k r) v z = 0) : 0 ≤ (herm (Hpk k r) v v).re := by
  let y : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < r then v i else 0
  have hy : Low r y := fun i hi => if_neg (by omega)
  have hw : inWb k r (v - y) := by
    intro i hi
    rcases hi with hi | hi
    · simp [y, hi]
    · have := he ⟨2 * r + k - i.val, by omega⟩
      rw [herm_e] at this
      have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i := Fin.ext (by simp [esI]; omega)
      rw [e] at this
      have h2 : ¬ i.val < r := by omega
      simp [y, h2, this]
  have hvy : herm (Hpk k r) v y = 0 := herm_low he hy
  have hyv : herm (Hpk k r) y v = 0 := by rw [← herm_conj, hvy, star_zero]
  have hzy : herm (Hpk k r) z y = 0 := by
    apply herm_low _ hy
    intro a
    rw [herm_e]
    apply hz
    have := a.isLt
    simp only [esI]; omega
  have hyz : herm (Hpk k r) y z = 0 := by rw [← herm_conj, hzy, star_zero]
  have e1 : herm (Hpk k r) (v - y) (v - y) = herm (Hpk k r) v v := by
    rw [herm_sub_l, herm_sub_r, herm_sub_r, hvy, hyv, herm_low_low hy hy]; ring
  by_contra hneg
  push_neg at hneg
  have h := revCS k r z (v - y) hz hw (by unfold Tz at hT; linarith) (by rw [e1]; exact hneg)
  rw [herm_sub_l, hvz, hyz] at h
  have : 0 < Tz k r (v - y) := by unfold Tz; rw [e1]; linarith
  have := mul_pos hT this
  simp at h
  linarith

theorem low_split {k r j : ℕ} (hj : j ≤ r) {n₁ n₂ g : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (c : ℂ)
    (hg : ∀ a : Fin r, j ≤ a.val → g *ᵥ bvec (eI k r a) = c • bvec (eI k r a))
    {v : Fin (2 * r + k + 1) → ℂ} (hv : Low r v) :
    ∃ u, Low j u ∧ Low r ((n₁ * g * n₂) *ᵥ (v - u)) := by
  have hu2 : IsUnit n₂.det := ((uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.2 n₂ h₂.1).1
  have hy := low_N le_rfl h₂ hv
  set y := n₂ *ᵥ v with hyd
  let lo : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < j then y i else 0
  have hlo : Low j lo := fun i hi => if_neg (by omega)
  refine ⟨n₂⁻¹ *ᵥ lo, low_N hj ((nSubgroup k r).2.2 _ h₂) hlo, ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec lo,
    Matrix.mul_nonsing_inv _ hu2, Matrix.one_mulVec, ← hyd]
  apply low_N le_rfl h₁
  have hhi : Low r (y - lo) := fun i hi => by
    have : ¬ i.val < j := by omega
    simp [lo, this, hy i hi]
  have e : g *ᵥ (y - lo) = c • (y - lo) := by
    rw [low_eq le_rfl hhi, Matrix.mulVec_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : j ≤ a.val
    · rw [Matrix.mulVec_smul, hg (Fin.castLE le_rfl a) ha, smul_comm]
    · have : (eI k r (Fin.castLE le_rfl a)).val < j := by simp [eI]; omega
      have e0 : (y - lo) (eI k r (Fin.castLE le_rfl a)) = 0 := by
        simp only [Pi.sub_apply, lo, if_pos this, sub_self]
      rw [e0]; simp
  rw [e]
  intro i hi
  simp [hhi i hi]

theorem herm_sum_l {k r j : ℕ} (α : Fin j → ℂ) (f : Fin j → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ a, α a • f a) w = ∑ a, α a * herm (Hpk k r) (f a) w := by
  simp [herm, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul]

def Zj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (γ : Mat k r) : Matrix (Fin j) (Fin j) ℂ := fun a b =>
  herm (Hpk k r) (γ *ᵥ bvec (eI k r (Fin.castLE hj b))) (bvec (eI k r (Fin.castLE hj a)))

theorem Dj_eq {k r j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) :
    Dj k r hj z z' γ = ‖(Zj k r hj γ).det‖ := by
  unfold Dj Dmin
  congr 2
  ext a b
  have ha : a.val < r := lt_of_lt_of_le a.isLt hj
  have hb : b.val < r := lt_of_lt_of_le b.isLt hj
  simp only [Matrix.submatrix_apply, Zhat, fvec, Zj, Fin.val_castLE, ha, hb, dif_pos]
  rfl

theorem unit_det {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det ∧ g⁻¹ ∈ GG k r :=
  (uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.2 g hg

theorem mul_GG {k r : ℕ} {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.1 g hg h hh

theorem herm_adj {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u (g⁻¹ *ᵥ v) = herm (Hpk k r) (g *ᵥ u) v := by
  rw [← herm_UH _ hg, Matrix.mulVec_mulVec v, Matrix.mul_nonsing_inv _ (unit_det hg).1, Matrix.one_mulVec]

theorem herm_adj' {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g⁻¹ *ᵥ u) v = herm (Hpk k r) u (g *ᵥ v) := by
  rw [← herm_UH _ hg, Matrix.mulVec_mulVec u, Matrix.mul_nonsing_inv _ (unit_det hg).1, Matrix.one_mulVec]

theorem Zj_inv {k r j : ℕ} (hj : j ≤ r) {γ : Mat k r} (hγ : γ ∈ GG k r) : Zj k r hj γ⁻¹ = (Zj k r hj γ)ᴴ := by
  ext a b
  rw [Matrix.conjTranspose_apply, Zj, Zj, herm_conj, herm_adj' hγ]

theorem mem_Ppos {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {γ x : Mat k r} {p : EuclideanSpace ℂ (Fin (2 * r + k + 1))}
    (hp : p ∈ Ppos k r z z' γ x) :
    Hpk k r *ᵥ p.ofLp = p.ofLp ∧ ∃ h y, x *ᵥ p.ofLp = h + y ∧ Low r y ∧
      (∀ a : Fin r, herm (Hpk k r) h (bvec (eI k r a)) = 0) ∧ herm (Hpk k r) h z' = 0 ∧
      (∀ a : Fin r, herm (Hpk k r) h (γ⁻¹ *ᵥ bvec (eI k r a)) = 0) ∧ herm (Hpk k r) h (γ⁻¹ *ᵥ z) = 0 := by
  obtain ⟨h1, h2⟩ := hp
  have h1' : (Hpk k r - 1) *ᵥ p.ofLp = 0 := h1
  have h2' : x *ᵥ p.ofLp ∈ Hcom k r z z' γ ⊔ Xsp k r := h2
  obtain ⟨h, hh, y, hy, e⟩ := Submodule.mem_sup.1 h2'
  have f1 : ∀ (t : Fin (2 * r + k + 1) → ℂ) (a : Fin r), fvec k r t a.castSucc = bvec (eI k r a) := by
    intro t a; simp [fvec]
  have f2 : ∀ (t : Fin (2 * r + k + 1) → ℂ), fvec k r t (Fin.last r) = t := by
    intro t; simp [fvec]
  refine ⟨?_, h, y, e.symm, low_of_mem hy, fun a => ?_, ?_, fun a => ?_, ?_⟩
  · rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1'
  · rw [← f1 z' a]; exact (hh _).1
  · rw [← f2 z']; exact (hh _).1
  · rw [← f1 z a]; exact (hh _).2
  · rw [← f2 z]; exact (hh _).2

theorem herm_pos_eq {k r : ℕ} {p : EuclideanSpace ℂ (Fin (2 * r + k + 1))} (hp : Hpk k r *ᵥ p.ofLp = p.ofLp)
    (q : EuclideanSpace ℂ (Fin (2 * r + k + 1))) : herm (Hpk k r) p.ofLp q.ofLp = ⟪q, p⟫_ℂ := by
  unfold herm
  rw [hp, PiLp.inner_apply]
  simp [dotProduct, mul_comm]

theorem bound_of_split {k r j : ℕ} (hj : j ≤ r) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {γ : Mat k r} (hγ : γ ∈ GG k r)
    (s₁ : ∀ v, Low r v → ∃ u, Low j u ∧ Low r (γ *ᵥ (v - u)))
    (s₂ : ∀ v, Low r v → ∃ u, Low j u ∧ Low r (γ⁻¹ *ᵥ (v - u)))
    {x : Mat k r} (hx : x ∈ GG k r) :
    Yj k r hj z z' γ x * Yj k r hj z' z γ⁻¹ (γ * x) * Dj k r hj z z' γ ≤ 2 ^ j := by
  have hγγ : γ⁻¹⁻¹ = γ := Matrix.nonsing_inv_nonsing_inv _ (unit_det hγ).1
  have hγx := mul_GG hγ hx
  unfold Yj
  rw [Dj_eq, Dj_eq, Zj_inv hj hγ, Matrix.det_conjTranspose, norm_star]
  set Z := Zj k r hj γ with hZ
  by_cases hd : Z.det = 0
  · rw [hd, norm_zero, mul_zero]; positivity
  have hd' : ‖Z.det‖ ≠ 0 := norm_ne_zero_iff.2 hd
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.2 hd
  refine le_of_eq_of_le ?_ (gram_core (Ppos k r z z' γ x) (Ppos k r z' z γ⁻¹ (γ * x))
    (fun a : Fin j => x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))))
    (fun a : Fin j => (γ * x)⁻¹ *ᵥ (γ⁻¹⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) (Z⁻¹)ᵀ ?_)
  · rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv]
    field_simp
  intro p hp p' hp'
  obtain ⟨hHp, h₁, y₁, e₁, hy₁, a₀, -, a₁, b₁⟩ := mem_Ppos hp
  obtain ⟨hHp', h', y₂, e₂, hy₂, a₂, b₂, c₂, -⟩ := mem_Ppos hp'
  rw [hγγ] at c₂ ⊢
  simp only [herm_adj hγ] at a₁ b₁
  set h := γ *ᵥ h₁ with hh
  have ew : (γ * x) *ᵥ p.ofLp = h + γ *ᵥ y₁ := by rw [← Matrix.mulVec_mulVec, e₁, Matrix.mulVec_add]
  have hc : ∀ v, Low r v → herm (Hpk k r) h (γ *ᵥ v) = 0 := fun v hv => by
    rw [hh, herm_UH _ hγ]; exact herm_low a₀ hv
  have hc' : ∀ v, Low r v → herm (Hpk k r) h' (γ *ᵥ v) = 0 := fun v hv => by
    rw [← herm_adj' hγ]; exact herm_low (fun a => by rw [herm_adj' hγ]; exact c₂ a) hv
  have sw : ∀ u v, herm (Hpk k r) u v = 0 → herm (Hpk k r) v u = 0 := fun u v e => by
    rw [← herm_conj, e, star_zero]
  have n₁ : herm (Hpk k r) h h = ⟪p, p⟫_ℂ := by
    rw [← herm_pos_eq hHp, ← herm_UH _ hγx p.ofLp, ew, herm_add_l, herm_add_r, herm_add_r, hc _ hy₁, sw _ _ (hc _ hy₁),
      herm_UH _ hγ y₁, herm_low_low hy₁ hy₁]; ring
  have n₂ : herm (Hpk k r) h' h' = ⟪p', p'⟫_ℂ := by
    rw [← herm_pos_eq hHp', ← herm_UH _ hγx p'.ofLp, e₂, herm_add_l, herm_add_r, herm_add_r, herm_low a₂ hy₂,
      sw _ _ (herm_low a₂ hy₂), herm_low_low hy₂ hy₂]; ring
  have n₃ : herm (Hpk k r) (γ *ᵥ y₁) y₂ = ⟪p', p⟫_ℂ - herm (Hpk k r) h h' := by
    rw [← herm_pos_eq hHp, ← herm_UH _ hγx p.ofLp, ew, e₂, herm_add_l, herm_add_r, herm_add_r, herm_low a₁ hy₂,
      sw _ _ (hc' _ hy₁)]; ring
  let S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
    { carrier := {v | (∀ a : Fin r, herm (Hpk k r) v (bvec (eI k r a)) = 0) ∧ herm (Hpk k r) v z = 0}
      zero_mem' := ⟨fun a => herm_zero_l _ _, herm_zero_l _ _⟩
      add_mem' := fun {u v} hu hv => ⟨fun a => by rw [herm_add_l, hu.1, hv.1, add_zero],
        by rw [herm_add_l, hu.2, hv.2, add_zero]⟩
      smul_mem' := fun c v hv => ⟨fun a => by rw [herm_smul_l, hv.1, mul_zero], by rw [herm_smul_l, hv.2, mul_zero]⟩ }
  have cs := herm_cs S (fun v hv => herm_nonneg hz hT hv.1 hv.2) h h' ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  have ip : ∀ q : EuclideanSpace ℂ (Fin (2 * r + k + 1)), (⟪q, q⟫_ℂ).re = ‖q‖ ^ 2 := fun q =>
    inner_self_eq_norm_sq (𝕜 := ℂ) q
  rw [n₁, n₂, ip, ip, ← mul_pow] at cs
  have cs' : ‖herm (Hpk k r) h h'‖ ≤ ‖p‖ * ‖p'‖ := le_of_pow_le_pow_left₀ two_ne_zero (by positivity) cs
  have bd : ‖herm (Hpk k r) (γ *ᵥ y₁) y₂‖ ≤ 2 * ‖p‖ * ‖p'‖ := by
    rw [n₃]
    have := norm_inner_le_norm (𝕜 := ℂ) p' p
    have := norm_sub_le ⟪p', p⟫_ℂ (herm (Hpk k r) h h')
    linarith
  refine le_of_eq_of_le (congrArg _ ?_) bd
  obtain ⟨u₁, hu₁, hv₁⟩ := s₁ y₁ hy₁
  obtain ⟨u₂, hu₂, hv₂⟩ := s₂ y₂ hy₂
  have le : ∀ a : Fin r, Low r (bvec (eI k r a)) := fun a => low_of_mem (Submodule.subset_span ⟨a, rfl⟩)
  have lu₁ : Low r u₁ := fun i hi => hu₁ i (hj.trans hi)
  have lu₂ : Low r u₂ := fun i hi => hu₂ i (hj.trans hi)
  obtain ⟨α, hα⟩ : ∃ α : Fin j → ℂ, u₁ = ∑ a, α a • bvec (eI k r (Fin.castLE hj a)) := ⟨_, low_eq hj hu₁⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin j → ℂ, u₂ = ∑ a, β a • bvec (eI k r (Fin.castLE hj a)) := ⟨_, low_eq hj hu₂⟩
  have r₁ : ∀ v, Low r v → herm (Hpk k r) (γ *ᵥ y₁) v = herm (Hpk k r) (γ *ᵥ u₁) v := fun v hv => by
    have := herm_low_low hv₁ hv
    rwa [Matrix.mulVec_sub, herm_sub_l, sub_eq_zero] at this
  have r₂ : ∀ v, Low r v → herm (Hpk k r) y₂ (γ *ᵥ v) = herm (Hpk k r) u₂ (γ *ᵥ v) := fun v hv => by
    have := herm_low_low hv₂ hv
    rwa [herm_adj' hγ, herm_sub_l, sub_eq_zero] at this
  have g₁ : γ *ᵥ u₁ = ∑ a, α a • (γ *ᵥ bvec (eI k r (Fin.castLE hj a))) := by
    rw [hα, Matrix.mulVec_sum]; simp only [Matrix.mulVec_smul]
  have k₁ : ∀ a : Fin j, star (x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) ⬝ᵥ p.ofLp = (Z *ᵥ α) a := fun a => by
    have : star (x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) ⬝ᵥ p.ofLp =
        herm (Hpk k r) p.ofLp (x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) := by rw [herm, hHp]
    rw [this, herm_adj hx, herm_adj hγ, Matrix.mulVec_mulVec, ew, herm_add_l, a₁, zero_add, r₁ _ (le _), g₁, herm_sum_l]
    simp only [Matrix.mulVec, dotProduct, mul_comm]
    rfl
  have k₂ : ∀ b : Fin j, star (star ((γ * x)⁻¹ *ᵥ (γ *ᵥ bvec (eI k r (Fin.castLE hj b)))) ⬝ᵥ p'.ofLp) =
      (star β ᵥ* Z) b := fun b => by
    have : star ((γ * x)⁻¹ *ᵥ (γ *ᵥ bvec (eI k r (Fin.castLE hj b)))) ⬝ᵥ p'.ofLp =
        herm (Hpk k r) p'.ofLp ((γ * x)⁻¹ *ᵥ (γ *ᵥ bvec (eI k r (Fin.castLE hj b)))) := by rw [herm, hHp']
    rw [this, herm_adj hγx, e₂, herm_add_l, c₂, zero_add, r₂ _ (le _), hβ, herm_sum_l, star_sum]
    simp only [star_mul', herm_conj]
    rfl
  have k₃ : herm (Hpk k r) (γ *ᵥ y₁) y₂ = star β ⬝ᵥ (Z *ᵥ α) := by
    rw [r₁ _ hy₂, ← herm_conj, r₂ _ lu₁, hβ, herm_sum_l, star_sum]
    simp only [star_mul', herm_conj]
    simp only [g₁, herm_sum_l]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp only [k₁, k₂]
  rw [k₃]
  have : star β ⬝ᵥ (Z *ᵥ α) = (star β ᵥ* Z) ⬝ᵥ (Z⁻¹ *ᵥ (Z *ᵥ α)) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, Matrix.dotProduct_mulVec]
  rw [this]
  generalize star β ᵥ* Z = s
  generalize Z *ᵥ α = t
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem gram_mul_minor_le : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ)
    (μR : Measure (Mt k r)), IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ x ∈ GG k r,
    Yj k r hj z z' γ x * Yj k r hj z' z γ⁻¹ (γ * x) * Dj k r hj z z' γ ≤ 2 ^ j := by
  rintro k r j hj z z' γ s μR ⟨hz, -, hT, n₁, h₁, n₂, h₂, g, β, c, ⟨hg, hc, -, -, -, -, he, -⟩, rfl, -⟩ x hx
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  refine bound_of_split hj hz hT (mul_GG (mul_GG h₁.1 hg) h₂.1)
    (fun v hv => low_split hj h₁ h₂ c (fun a ha => (he a ha).1) hv) (fun v hv => ?_) hx
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc]
  refine low_split hj ((nSubgroup k r).2.2 _ h₂) ((nSubgroup k r).2.2 _ h₁) c⁻¹ (fun a ha => ?_) hv
  have e := congrArg (fun v => g⁻¹ *ᵥ v) (he a ha).1
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (unit_det hg).1, Matrix.one_mulVec, Matrix.mulVec_smul] at e
  conv_rhs => rw [e]
  rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]

end GlobalTheory.Amp.ExtPow
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagGramNumber_mul_leadingMinor_le_two_pow : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ x ∈ GG k r, Yj k r hj z z' γ x * Yj k r hj z' z γ⁻¹ (γ * x) * Dj k r hj z z' γ ≤ 2 ^ j := by
  atlas_forward_decl GlobalTheory.Amp.ExtPow.gram_mul_minor_le
end

section
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.MinorBound

open GlobalTheory.PlueckerBound GlobalTheory.Amp.GramFlag

theorem norm_det_inner_le_pow {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : ℕ} (u v : Fin l → E)
    (s t : Matrix (Fin l) (Fin l) ℂ) (hs : s.det = 1) (ht : t.det = 1) {R R' : ℝ}
    (hu : ∀ a, ‖∑ i, s i a • u i‖ ≤ R) (hv : ∀ a, ‖∑ i, t i a • v i‖ ≤ R') :
    ‖(Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det‖ ≤ R ^ l * R' ^ l := by
  have h := norm_det_inner_le (fun a => ∑ i, s i a • u i) (fun a => ∑ i, t i a • v i)
  rw [det_inner_sum_smul, ht, mul_one] at h
  have e : (Matrix.of fun a a' => ⟪∑ i, s i a • u i, v a'⟫_ℂ) = sᴴ * Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ := by
    ext a a'
    simp [Matrix.mul_apply, sum_inner, inner_smul_left, mul_comm]
  rw [e, Matrix.det_mul, Matrix.det_conjTranspose, hs, star_one, one_mul] at h
  have h1 : ∀ {f : Fin l → E} {S : ℝ}, (∀ a, ‖f a‖ ≤ S) → ∏ a, ‖f a‖ ≤ S ^ l := fun {f S} hf => by
    have := Finset.prod_le_prod (s := Finset.univ) (fun a _ => norm_nonneg (f a)) (fun a _ => hf a)
    simpa using this
  have h0 : ∀ f : Fin l → E, 0 ≤ ∏ a, ‖f a‖ := fun f => Finset.prod_nonneg fun a _ => norm_nonneg _
  exact h.trans (mul_le_mul (h1 hu) (h1 hv) (h0 _) ((h0 _).trans (h1 hu)))

theorem exists_short (k r : ℕ) {l : ℕ} (hl : l ≤ r) (z : Fin (2 * r + k + 1) → ℂ) {x : Mat k r} (hx : x ∈ GG k r) :
    ∃ t : Matrix (Fin l) (Fin l) ℂ, t.det = 1 ∧
      ∀ a, eucl (∑ b, t b a • (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl b)))) ≤ Sg k r z x := by
  obtain ⟨u, hu, -⟩ := gramSchmidt_lengths k r z x hx
  refine ⟨(upper u).submatrix (Fin.castLE hl) (Fin.castLE hl), ?_, fun a => ?_⟩
  · rw [Matrix.det_of_upperTriangular]
    · simp [upper]
    · intro a b hab
      have hab' : b < a := hab
      have h1 : ¬ a < b := not_lt.2 hab'.le
      simp [upper, h1, hab'.ne']
  · have e : ∑ b, (upper u).submatrix (Fin.castLE hl) (Fin.castLE hl) b a • (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl b))) =
        ∑ b, upper u b (Fin.castLE hl a) • (x⁻¹ *ᵥ bvec (eI k r b)) := by
      refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun b => rfl)
      intro b hb
      have hb' : l ≤ b.val := by
        by_contra h
        exact hb ⟨⟨b.val, by omega⟩, rfl⟩
      have ha := a.isLt
      have h1 : ¬ b < Fin.castLE hl a := by
        rw [Fin.lt_def, Fin.val_castLE]; omega
      have h2 : b ≠ Fin.castLE hl a := fun h => by
        rw [h, Fin.val_castLE] at hb'; omega
      simp [upper, h1, h2]
    rw [e, (hu _).1]
    exact (Finset.le_fold_max _).2 (Or.inr ⟨_, Finset.mem_univ _, le_rfl⟩)

theorem eucl_Hpk (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : eucl (Hpk k r *ᵥ v) = eucl v := by
  rw [eucl_eq, eucl_eq, @norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_toLp_toLp, Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, (hpkFacts k r).1, (hpkFacts k r).2.1, Matrix.one_mulVec, dotProduct_comm]

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem one_le_Sg (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : 1 ≤ Sg k r z x :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem norm_Dmin_le (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {γ x : Mat k r} (hγ : γ ∈ GG k r) (hx : x ∈ GG k r)
    (l : Fin (r + 1)) : ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ hH
  have hγx := hmul γ hγ x hx
  have hl : l.val ≤ r := Nat.le_of_lt_succ l.isLt
  obtain ⟨s, hs, hs'⟩ := exists_short k r hl z hγx
  obtain ⟨t, ht, ht'⟩ := exists_short k r hl z' hx
  have h := norm_det_inner_le_pow (E := EuclideanSpace ℂ (Fin (2 * r + k + 1)))
    (fun a => WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))))
    (fun a => WithLp.toLp 2 (Hpk k r *ᵥ (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))))) s t hs ht
    (R := Sg k r z (γ * x)) (R' := Sg k r z' x)
    (fun a => by
      have := hs' a
      rwa [eucl_eq, WithLp.toLp_sum] at this)
    (fun a => by
      have := ht' a
      rw [← eucl_Hpk, eucl_eq, Matrix.mulVec_sum, WithLp.toLp_sum] at this
      simpa only [Matrix.mulVec_smul, WithLp.toLp_smul] using this)
  have e : Dmin k r z z' γ l.castSucc = (Matrix.of fun a a' : Fin l.val =>
      ⟪(WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))) : EuclideanSpace ℂ (Fin (2 * r + k + 1))),
        WithLp.toLp 2 (Hpk k r *ᵥ (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a'))))⟫_ℂ).det := by
    unfold Dmin
    congr 1
    ext a b
    have ha : a.val < r := lt_of_lt_of_le a.isLt hl
    have hb : b.val < r := lt_of_lt_of_le b.isLt hl
    rw [Matrix.of_apply, EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.submatrix_apply, Zhat,
      ← herm_mulVec (hinv _ hγx).2, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (hinv _ hγ).1, Matrix.mul_one, fvec, fvec, dif_pos (by exact hb), dif_pos (by exact ha)]
    rfl
  rw [e]
  refine h.trans ?_
  rw [← mul_pow, mul_comm]
  exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (one_le_Sg ..) (one_le_Sg ..)) hl

theorem gramProj_le (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z : Fin (2 * r + k + 1) → ℂ) {x : Mat k r} (hx : x ∈ GG k r)
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1)))) :
    gramProj P (fun a : Fin j => x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))) ≤ Sg k r z x ^ r := by
  obtain ⟨s, hs, hs'⟩ := exists_short k r hj z hx
  have h1 : ∀ a, ‖∑ i, s i a • P.starProjection (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj i))))‖ ≤
      Sg k r z x := fun a => by
    have := hs' a
    rw [eucl_eq, WithLp.toLp_sum] at this
    refine le_trans (le_of_eq ?_) ((P.norm_starProjection_apply_le _).trans this)
    simp only [map_sum, WithLp.toLp_smul, map_smul]
  have h := norm_det_inner_le_pow _ _ s s hs hs h1 h1
  have h0 := one_le_Sg k r z x
  refine le_trans ?_ (pow_le_pow_right₀ h0 hj)
  unfold gramProj
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [sq]
  exact h

theorem minor_gram_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ l : Fin (r + 1), ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r) ∧ 0 ≤ Yj k r hj z z' γ x ∧ Yj k r hj z z' γ x ≤ Sg k r z (γ * x) ^ r / Dj k r hj z z' γ ∧ ∀ H₁ : ℝ, 1 ≤ H₁ → sgV k r z z' γ H₁ ≤ max 1 ((Sg k r z' x * Sg k r z (γ * x)) ^ r / (2 * H₁) ^ (2 * r)) := by
  intro k r j hj z z' γ _ _ hγ x hx
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hγx := (uHGroup _ _ hH).2.1 γ hγ x hx
  refine ⟨norm_Dmin_le k r z z' hγ hx, div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), ?_, fun H₁ hH₁ => ?_⟩
  · refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    have := gramProj_le k r hj z hγx (Ppos k r z z' γ x)
    simpa only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec] using this
  · refine (Finset.fold_max_le _).2 ⟨le_max_left _ _, fun l _ => le_max_of_le_right ?_⟩
    exact div_le_div_of_nonneg_right (norm_Dmin_le k r z z' hγ hx l) (by positivity)

end GlobalTheory.Amp.MinorBound
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_minors_gram_number_le_majorant_lengths : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ l : Fin (r + 1), ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r) ∧ 0 ≤ Yj k r hj z z' γ x ∧ Yj k r hj z z' γ x ≤ Sg k r z (γ * x) ^ r / Dj k r hj z z' γ ∧ ∀ H₁ : ℝ, 1 ≤ H₁ → sgV k r z z' γ H₁ ≤ max 1 ((Sg k r z' x * Sg k r z (γ * x)) ^ r / (2 * H₁) ^ (2 * r)) := by
  atlas_forward_decl GlobalTheory.Amp.MinorBound.minor_gram_bound
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.DegConv

variable {k r : ℕ}

theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem lmul_inv_lmul {γ : Mat k r} (hγ : γ ∈ GG k r) (x : Mt k r) : lmulM γ⁻¹ (lmulM γ x) = x :=
  Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)

def lmulEquiv {γ : Mat k r} (hγ : γ ∈ GG k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM γ
  invFun := lmulM γ⁻¹
  left_inv := lmul_inv_lmul hγ
  right_inv x := Matrix.mul_nonsing_inv_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)
  measurable_toFun := (continuous_lmul γ).measurable
  measurable_invFun := (continuous_lmul γ⁻¹).measurable

theorem quot_map {γ : Mat k r} (hγ : γ ∈ GG k r) {μG μR ν : Measure (Mt k r)} (hG : IsHaarOn (GG k r) μG)
    (h : IsQuotMeas μG μR ν) : IsQuotMeas μG (μR.map (conjM γ)) (ν.map (lmulEquiv hγ)) := by
  intro f hf
  rw [lintegral_map_equiv]
  have h1 := h (fun x => f (lmulM γ x)) (hf.comp (continuous_lmul γ).measurable)
  rw [← lintegral_map hf (continuous_lmul γ).measurable, hG.2.2.2 γ hγ] at h1
  rw [h1]
  refine lintegral_congr fun x => ?_
  have hm : Measurable fun s : Mt k r => f (rmulM (Matrix.of (lmulEquiv hγ x)) s) :=
    hf.comp (continuous_rmulM _).measurable
  refine Eq.trans ?_ (lintegral_map hm (continuous_conj γ).measurable).symm
  refine lintegral_congr fun s => ?_
  congr 1
  show γ * (Matrix.of s * Matrix.of x) = γ * Matrix.of s * γ⁻¹ * (γ * Matrix.of x)
  rw [Matrix.mul_assoc _ γ⁻¹, Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ),
    Matrix.mul_assoc]

def Gs (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ GG k r}

def ext0 (f : Mat k r → ℝ) : Mt k r → ℝ := Set.indicator (Gs k r) fun x => f (Matrix.of x)

theorem cochainExtendByZeroSubgroup_of_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∈ GG k r) : ext0 f x = f (Matrix.of x) :=
  Set.indicator_of_mem (s := Gs k r) hx _

theorem amplifierAbsConvExtendByZero_of_not_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∉ GG k r) : ext0 f x = 0 :=
  Set.indicator_of_notMem (s := Gs k r) hx _

theorem measurable_amplifierAbsConvExtendByZero {f : Mat k r → ℝ} (hf : ContinuousOn f (GG k r)) : Measurable (ext0 f) := by
  classical
  have hc : IsClosed (Gs k r) := isClosedSub_GG.2.1
  have h1 : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) (Gs k r) := hf
  have := ContinuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) h1 continuousOn_const hc.measurableSet
  convert this using 1
  exact (Set.piecewise_eq_indicator).symm

def Kc (k r j : ℕ) (De : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (4 * r ^ 2) * De ^ (8 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) *
    4 ^ (k - 1 - j) * (4 * r + 4)

theorem side {j : ℕ} {hj : j ≤ r} {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {z z' : Fin (2 * r + k + 1) → ℂ} {π' : Mat k r → (Wq →L[ℂ] Wq)} {ψ' : Mat k r → ℂ}
    {μG μW' νS' μR νR : Measure (Mt k r)} {Φ' : Mat k r → Wq} {γ : Mat k r} {c κ s H₁ De : ℝ} {q : ℕ}
    (hj1 : 1 ≤ j) (hk : j + 2 ≤ k) (hκ : 0 < κ) (hs : 0 < s) (hH : 1 ≤ H₁) (hγ : γ ∈ GG k r)
    (h1 : OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c) (h2 : TailBd z' νS' Φ' q H₁)
    (h4 : DeOK k r z z' γ De) (h5 : IsNormalFormStabilizerMeasure k r hj z z' γ s μR) (h6 : IsQuotMeas μG μR νR)
    (w : Wq) (hw : ‖w‖ = 1) (i i' : ℕ) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in {x | ext0 (Sg2 k r z') x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < ext0 (Sg2 k r z') x) ∧
        ext0 (Sg2 k r z) (lmulM γ x) ≤ 2 ^ (i + 1) * H₁ ∧ y < ext0 (Yj k r hj z z' γ) x ∧
        ext0 (Yj k r hj z z' γ) x ≤ 2 * y},
      ENNReal.ofReal (ext0 (fun g => ‖⟪w, Φ' g⟫_ℂ‖) x ^ 2) ∂νR ≤
    ENNReal.ofReal (κ / s * Kc k r j De * c * (2 ^ (i + i' + 1) * H₁) ^ (16 * r ^ 3) * y ^ (2 * (k - 1 - j)) *
      (((2 : ℝ) ^ i') ^ (2 * q))⁻¹) := by
  have hH0 : 0 ≤ H₁ := zero_le_one.trans hH
  have q1 : (2 : ℝ) ^ (i + 1) * H₁ ≤ 2 ^ (i + i' + 1) * H₁ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hH0
  have q2 : (2 : ℝ) ^ (i' + 1) * H₁ ≤ 2 ^ (i + i' + 1) * H₁ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hH0
  have hR : (1 : ℝ) ≤ 2 ^ (i + i' + 1) * H₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hH
  have key := (GlobalTheory.T.amplification_degenerate_side_piece_bound k r j hj z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hk hκ hs hH h1 h2 h4 h5 h6).2
    w hw i' _ y hR hy
  refine le_trans (lintegral_mono' (Measure.restrict_mono ?_ le_rfl) fun x => ?_) (key.trans (le_of_eq ?_))
  · rintro x ⟨a1, a2, a3, a4, a5⟩
    have hx : Matrix.of x ∈ GG k r := by
      by_contra hx
      rw [amplifierAbsConvExtendByZero_of_not_mem _ hx] at a4
      exact lt_asymm hy a4
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx
    rw [cochainExtendByZeroSubgroup_of_mem _ hx] at a1 a2 a4 a5
    rw [cochainExtendByZeroSubgroup_of_mem _ hx'] at a3
    exact ⟨⟨hx, a1.trans q2, a3.trans q1, a4, a5⟩, a2⟩
  · by_cases hx : Matrix.of x ∈ GG k r
    · simp only [cochainExtendByZeroSubgroup_of_mem _ hx, le_refl]
    · simp [amplifierAbsConvExtendByZero_of_not_mem _ hx]
  · congr 1
    unfold fibVol0 Kc
    generalize (2 : ℝ) ^ (i + i' + 1) * H₁ = R
    rw [mul_pow 2 y, pow_mul (2 : ℝ) 2, mul_pow (R ^ (2 * r)), ← pow_mul R,
      show 2 * r * (8 * r ^ 2) = 16 * r ^ 3 by ring]
    norm_num only
    ring

theorem max_bounds {r : ℕ} {M D De Y T : ℝ} (hD0 : 0 < D) (hD : D⁻¹ ≤ De) (hT : 0 ≤ T) (hT' : T ≤ M)
    (hY : Y ≤ T ^ r / D) : Y ≤ M ^ r * De := by
  have hM : 0 ≤ M := hT.trans hT'
  refine hY.trans ?_
  rw [div_eq_mul_inv]
  gcongr

theorem one_le_Sg (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : 1 ≤ Sg k r z x := by
  unfold Sg; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem one_le_sgV (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (H₁ : ℝ) : 1 ≤ sgV k r z z' γ H₁ := by
  unfold sgV; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem arith (k r j q : ℕ) {H₁ De D sg : ℝ} (hj : 1 ≤ j) (hH : 1 ≤ H₁) (hDe : 1 ≤ De) (hD : 0 < D) (hsg : 1 ≤ sg) :
    16 * Kc k r j De * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k - 1 - j) *
      sg ^ (-(((q : ℝ) - (16 * r ^ 3 : ℕ) - 4 * r - 1) / r)) ≤ degBd k r j q H₁ De D sg := by
  unfold degBd Kc
  generalize k - 1 - j = m
  have e : (((16 * r ^ 3 : ℕ) : ℝ)) = 16 * (r : ℝ) ^ 3 := by push_cast; ring
  rw [e]
  have hs0 : 0 ≤ sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r)) := Real.rpow_nonneg (zero_le_one.trans hsg) _
  generalize sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r)) = t at hs0
  have h8 : (4 : ℝ) ^ m * (2 ^ j) ^ m ≤ 8 ^ (j * m) := by
    have : (4 : ℝ) ^ m ≤ 4 ^ (j * m) := pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left m hj)
    rw [← pow_mul, show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]
    gcongr
  have hP : 0 ≤ Real.pi * Real.exp 1 / (m : ℝ) := by positivity
  rw [show 8 * Real.pi * Real.exp 1 / (m : ℝ) = 8 * (Real.pi * Real.exp 1 / m) by ring, mul_pow (8 : ℝ), div_pow _ D,
    pow_add De]
  generalize Real.pi * Real.exp 1 / (m : ℝ) = P at hP ⊢
  have hH0 : 0 ≤ H₁ := zero_le_one.trans hH
  have hDe0 : 0 ≤ De := zero_le_one.trans hDe
  have hc : 0 ≤ 16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) *
      (De ^ (8 * r ^ 2) * De ^ 2) * P ^ (j * m) * (D ^ m)⁻¹ * t := by positivity
  have := mul_le_mul_of_nonneg_left h8 hc
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · rw [div_eq_mul_inv]
    generalize (2 * H₁) ^ (16 * r ^ 3 + 4 * r) = A
    generalize (4 * r : ℝ) ^ (4 * r ^ 2) = B
    generalize ((2 : ℝ) ^ j) ^ m = C
    ring
  · generalize (2 * H₁) ^ (16 * r ^ 3 + 4 * r) = A
    generalize (4 * r : ℝ) ^ (4 * r ^ 2) = B
    ring

theorem deg_core : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 16 * r ^ 3 + 4 * r + 2 ≤ q → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z νS Φ q H₁ → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * degBd k r j q H₁ De (Dj k r hj z z' γ) (sgV k r z z' γ H₁) := by
  intro k r j hj z z' Wp _ _ _ Wq _ _ _ π π' ψ ψ' μG μW μW' νS νS' μR νR Φ Φ' γ c κ s H₁ De q hj1 hk hq hκ hs hH o1 o2
    m1 m2 de nr qm
  obtain ⟨hγ, -, -, -, nr', hD, hDD, hde⟩ := GlobalTheory.T.stabilizer_measure_normalisation_symm k r j hj z z' γ s μR hs nr
  have hr : 1 ≤ r := hj1.trans hj
  have hγ' : γ⁻¹ ∈ GG k r := isClosedSub_GG.2.2.2.2 _ hγ
  have hG : IsHaarOn (GG k r) μG := o1.2.2.2.2.2.1
  have hc : 0 < c := o1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ : ContinuousOn Φ (GG k r) := o1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ' : ContinuousOn Φ' (GG k r) := o2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have de' := hde De de
  have qm' := quot_map hγ hG qm
  have hDe : (Dj k r hj z z' γ)⁻¹ ≤ De := de.2 ⟨j, by omega⟩ hj (norm_ne_zero_iff.1 hD.ne')
  have hDe1 : 1 ≤ De := de.1
  have n1 := (GlobalTheory.T.amplification_degenerate_side_piece_bound k r j hj z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hk hκ hs hH o2 m2 de nr qm).1
  have n2 := (GlobalTheory.T.amplification_degenerate_side_piece_bound k r j hj z' z π ψ μG μW νS _ _ Φ γ⁻¹ c κ s H₁ De q hj1 hk hκ hs hH o1 m1 de' nr' qm').1
  rw [MeasurableEquiv.map_apply] at n2
  have a1 : ∀ᵐ x ∂νR, Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n1] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] using hx
  have a2 : ∀ᵐ x ∂νR, Yj k r hj z' z γ⁻¹ (γ * Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n2] with x hx
    exact fun h => hx (Or.inr h)
  have n0 : νR {x | Matrix.of x ∉ GG k r} = 0 := measure_mono_null (fun x hx => Or.inl hx) n1
  have hkk : 1 ≤ k - 1 - j := by omega
  have hK : 0 < κ / s * Kc k r j De * c := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    have : (0 : ℝ) < ((k - 1 - j : ℕ) : ℝ) := by exact_mod_cast hkk
    unfold Kc
    positivity
  have hsg := one_le_sgV z z' γ H₁
  have me : Measurable (lmulM γ : Mt k r → Mt k r) := (continuous_lmul γ).measurable
  have g1 := GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z o1.1 o1.2.1
  have g2 := GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' o2.1 o2.2.1
  have main := GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings k r νR Φ Φ' γ c (16 * (κ / s * Kc k r j De * c) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ 2 *
    (2 ^ j / Dj k r hj z z' γ) ^ (k - 1 - j) *
    sgV k r z z' γ H₁ ^ (-(((q : ℝ) - (16 * r ^ 3 : ℕ) - 4 * r - 1) / r))) hγ n0 cΦ cΦ' hc (by positivity) ?_
  · refine ⟨main.1, main.2.trans ?_⟩
    have := arith k r j q hj1 hH hDe1 hD hsg
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ κ / s))
    field_simp
  intro v w hv hw
  have mA : Measurable (ext0 fun g => ‖⟪v, Φ g⟫_ℂ‖) :=
    measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ).norm
  have mB : Measurable (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) :=
    measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ').norm
  have mS : Measurable (ext0 (Sg2 k r z)) := measurable_amplifierAbsConvExtendByZero g1.2.2.1
  have mS' : Measurable (ext0 (Sg2 k r z')) := measurable_amplifierAbsConvExtendByZero g2.2.2.1
  have mY : Measurable (ext0 (Yj k r hj z' z γ⁻¹)) :=
    (GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z' z γ⁻¹ o2.1 o1.1 o2.2.1 o1.2.1 hγ').1
  have mY' : Measurable (ext0 (Yj k r hj z z' γ)) := (GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' γ o1.1 o2.1 o1.2.1 o2.2.1 hγ).1
  have dy := GlobalTheory.T.dyadic_summation_with_decay (Mt k r) νR (fun x => ext0 (fun g => ‖⟪v, Φ g⟫_ℂ‖) (lmulM γ x))
    (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) (fun x => ext0 (Sg2 k r z) (lmulM γ x)) (ext0 (Sg2 k r z'))
    (fun x => ext0 (Yj k r hj z' z γ⁻¹) (lmulM γ x)) (ext0 (Yj k r hj z z' γ)) r j (k - 1 - j) (16 * r ^ 3) q H₁ De
    (Dj k r hj z z' γ) _ _ _
    (mA.comp me) mB (mS.comp me) mS' (mY.comp me) mY' hr hkk hq hH hDe1 hD hK hK hsg ?_ ?_
    (fun i i' y hy => side hj1 hk hκ hs hH hγ o2 m2 de nr qm w hw i i' y hy)
  · rw [Real.sqrt_mul_self hK.le] at dy
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) dy
    filter_upwards [a1] with x hx
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    rw [cochainExtendByZeroSubgroup_of_mem _ hx.1, cochainExtendByZeroSubgroup_of_mem _ hx']
    rfl
  · filter_upwards [a1, a2] with x hx hx2
    have hx' : γ * Matrix.of x ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    have e1 : ∀ f : Mat k r → ℝ, ext0 f (lmulM γ x) = f (γ * Matrix.of x) := fun f => cochainExtendByZeroSubgroup_of_mem f hx'
    simp only [e1, cochainExtendByZeroSubgroup_of_mem _ hx.1]
    obtain ⟨s1, t1, -⟩ := g1.2.2.2 (γ * Matrix.of x)
    obtain ⟨s2, t2, -⟩ := g2.2.2.2 (Matrix.of x)
    have u1 : 0 ≤ Sg k r z (γ * Matrix.of x) := zero_le_one.trans (one_le_Sg _ _)
    have u2 : 0 ≤ Sg k r z' (Matrix.of x) := zero_le_one.trans (one_le_Sg _ _)
    obtain ⟨b1, b2, b3, b4⟩ := GlobalTheory.T.leading_minors_gram_number_le_majorant_lengths k r j hj z z' γ o1.1 o2.1 hγ _ hx.1
    obtain ⟨-, b5, b6, -⟩ := GlobalTheory.T.leading_minors_gram_number_le_majorant_lengths k r j hj z' z γ⁻¹ o2.1 o1.1 hγ' _ hx'
    rw [Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ), hDD] at b6
    have pw : (Sg k r z' (Matrix.of x) * Sg k r z (γ * Matrix.of x)) ^ r ≤
        (Sg2 k r z (γ * Matrix.of x) * Sg2 k r z' (Matrix.of x)) ^ r := by
      rw [mul_comm]
      exact pow_le_pow_left₀ (mul_nonneg u1 u2) (mul_le_mul t1 t2 u2 (u1.trans t1)) _
    refine ⟨norm_nonneg _, norm_nonneg _, s1, s2, lt_of_le_of_ne b5 hx2.symm, lt_of_le_of_ne b2 hx.2.symm, ?_,
      (b1 ⟨j, by omega⟩).trans pw,
      max_bounds hD hDe u2 (t2.trans (le_max_right _ _)) b6,
      max_bounds hD hDe u1 (t1.trans (le_max_left _ _)) b3, ?_⟩
    · rw [mul_comm (Yj k r hj z' z γ⁻¹ _)]
      exact GlobalTheory.T.flagGramNumber_mul_leadingMinor_le_two_pow k r j hj z z' γ s μR nr _ hx.1
    · exact (b4 H₁ hH).trans (max_le_max le_rfl (div_le_div_of_nonneg_right pw (by positivity)))
  · intro i i' y hy
    have h := side hj1 hk hκ hs hH hγ' o1 m1 de' nr' qm' v hv i' i y hy
    rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, add_comm i' i] at h
    refine le_trans (le_of_eq ?_) h
    congr 2
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [show lmulEquiv hγ x = lmulM γ x from rfl, lmul_inv_lmul hγ]

end GlobalTheory.Amp.DegConv
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_degenerate_operatorNorm_le_realPlace : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 16 * r ^ 3 + 4 * r + 2 ≤ q → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z νS Φ q H₁ → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * degBd k r j q H₁ De (Dj k r hj z z' γ) (sgV k r z z' γ H₁) := by
  atlas_forward_decl GlobalTheory.Amp.DegConv.deg_core
end

section
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

private lemma hsNormSq_eq_sum_norm_sq {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (J : Wq →L[ℂ] Wp) :
    hsNormSq J = ∑ i, ‖J (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_le_finrank_target_mul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (J : Wq →L[ℂ] Wp) : hsNormSq J ≤ Module.finrank ℂ Wp * ‖J‖ ^ 2 := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq

  rw [hsNormSq_eq_sum_norm_sq]
  calc ∑ i, ‖J (stdOrthonormalBasis ℂ Wq i)‖ ^ 2
        = ∑ i, ∑ j, ‖⟪(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j),
            stdOrthonormalBasis ℂ Wq i⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← (stdOrthonormalBasis ℂ Wp).sum_sq_norm_inner_right (J (stdOrthonormalBasis ℂ Wq i))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (stdOrthonormalBasis ℂ Wq).sum_sq_norm_inner_left _
    _ ≤ ∑ _j : Fin (Module.finrank ℂ Wp), ‖J‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hle : ‖(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j)‖ ≤ ‖J‖ := by
          calc _ ≤ ‖ContinuousLinearMap.adjoint J‖ * ‖stdOrthonormalBasis ℂ Wp j‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ = ‖J‖ := by
                rw [LinearIsometryEquiv.norm_map, (stdOrthonormalBasis ℂ Wp).orthonormal.1 j, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = Module.finrank ℂ Wp * ‖J‖ ^ 2 := by simp

theorem sqrt_hsNormSq_amplitude_le_degBd : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → ∀ (j : ℕ) (hj : j ≤ D.R.rS) (q : ℕ) (γ : Mat D.R.k D.R.rS) (s H₁ De : ℝ) (μR νR : Measure (Mt D.R.k D.R.rS)), 1 ≤ j → j + 2 ≤ D.R.k → 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ q → 0 < s → 1 ≤ H₁ → TailBd W.z W.νS A.Φ q H₁ → TailBd W.z' W.νS' A.Φ' q H₁ → DeOK D.R.k D.R.rS W.z W.z' γ De → IsNormalFormStabilizerMeasure D.R.k D.R.rS hj W.z W.z' γ s μR → IsQuotMeas W.μG μR νR → Real.sqrt (hsNormSq (A.J νR γ)) ≤ Real.sqrt (Module.finrank ℂ W.Wp) * (((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) / s * degBd D.R.k D.R.rS j q H₁ De (Dj D.R.k D.R.rS hj W.z W.z' γ) (sgV D.R.k D.R.rS W.z W.z' γ H₁)) := by
  intro D τ w w' θ W lam A hv hθ hw hw' hW hS j hj q γ s H₁ De μR νR hj1 hjk hq hs hH hT hT' hDe hN hQ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.amplitude_one_side_of_good_local_data D τ w w' θ W lam A hv hθ hw hw' hW hS
  have hκ : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ) (by positivity)
  have hb := (GlobalTheory.T.amplitude_degenerate_operatorNorm_le_realPlace D.R.k D.R.rS j hj W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' μR νR
    A.Φ A.Φ' γ A.cN _ s H₁ De q hj1 hjk hq hκ hs hH h1 h2 hT hT' hDe hN hQ).2

  calc Real.sqrt (hsNormSq (A.J νR γ))
        ≤ Real.sqrt (Module.finrank ℂ W.Wp * ‖A.J νR γ‖ ^ 2) :=
          Real.sqrt_le_sqrt (hsNormSq_le_finrank_target_mul (A.J νR γ))
    _ = Real.sqrt (Module.finrank ℂ W.Wp) * ‖A.J νR γ‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

end GlobalTheory.Amp
end

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_hsNorm_le_degreeBound_realPlace : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → ∀ (j : ℕ) (hj : j ≤ D.R.rS) (q : ℕ) (γ : Mat D.R.k D.R.rS) (s H₁ De : ℝ) (μR νR : Measure (Mt D.R.k D.R.rS)), 1 ≤ j → j + 2 ≤ D.R.k → 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ q → 0 < s → 1 ≤ H₁ → TailBd W.z W.νS A.Φ q H₁ → TailBd W.z' W.νS' A.Φ' q H₁ → DeOK D.R.k D.R.rS W.z W.z' γ De → IsNormalFormStabilizerMeasure D.R.k D.R.rS hj W.z W.z' γ s μR → IsQuotMeas W.μG μR νR → Real.sqrt (hsNormSq (A.J νR γ)) ≤ Real.sqrt (Module.finrank ℂ W.Wp) * (((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) / s * degBd D.R.k D.R.rS j q H₁ De (Dj D.R.k D.R.rS hj W.z W.z' γ) (sgV D.R.k D.R.rS W.z W.z' γ H₁)) := by
  atlas_forward_decl GlobalTheory.Amp.sqrt_hsNormSq_amplitude_le_degBd
end
