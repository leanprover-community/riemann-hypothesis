import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate

section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

section Algebra

variable {k : Type*} [Field k]

theorem exists_norm_of_quaternary [CharZero k] {α β γ s : k} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hs : s ^ 2 = α * β * γ) {x y z t : k} (h0 : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0)
    (h : x ^ 2 - α * y ^ 2 - β * z ^ 2 + γ * t ^ 2 = 0) : ∃ X Y : k, β = X ^ 2 - α * Y ^ 2 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (mul_ne_zero hα hβ) hγ (by simpa using hs.symm)
  obtain ⟨u, hu⟩ : ∃ u, u = t * s / (α * β) := ⟨_, rfl⟩
  have hu2 : α * β * u ^ 2 = γ * t ^ 2 := by
    rw [hu, div_pow, mul_pow, hs]; field_simp
  have h1 : x ^ 2 - α * y ^ 2 = β * (z ^ 2 - α * u ^ 2) := by linear_combination h + hu2
  by_cases hD : z ^ 2 - α * u ^ 2 = 0
  · refine GlobalTheory.Published.HasseNormSt.of_isSquare hα ?_ β
    by_cases hu0 : u = 0
    · have hz : z = 0 := by simpa [hu0] using hD
      have ht : t = 0 := by
        have : γ * t ^ 2 = 0 := by rw [← hu2, hu0]; ring
        simpa [hγ] using this
      have hxy : x ^ 2 = α * y ^ 2 := by linear_combination h1 + β * hD
      have hy : y ≠ 0 := by
        rintro rfl
        have hx : x = 0 := by simpa using hxy
        simp [hx, hz, ht] at h0
      exact ⟨x / y, by field_simp; linear_combination -hxy⟩
    · exact ⟨z / u, by field_simp; linear_combination -hD⟩
  · refine ⟨(x * z + α * y * u) / (z ^ 2 - α * u ^ 2), (x * u + y * z) / (z ^ 2 - α * u ^ 2), ?_⟩
    field_simp
    linear_combination (-(z ^ 2 - α * u ^ 2)) * h1

theorem exists_quaternary_of_coordinates {α β γ : k} (hα : α ≠ 0) (hβ : β ≠ 0)
    {X₀ X₁ Y₀ Y₁ : k}
    (h1 : β = X₀ ^ 2 + α * β * γ * X₁ ^ 2 - α * (Y₀ ^ 2 + α * β * γ * Y₁ ^ 2))
    (h2 : X₀ * X₁ = α * (Y₀ * Y₁)) :
    ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - α * y ^ 2 - β * z ^ 2 + γ * t ^ 2 = 0 := by
  by_cases hw : X₁ ^ 2 - α * Y₁ ^ 2 = 0
  · exact ⟨X₀, Y₀, 1, 0, by simp, by linear_combination -h1 - α * β * γ * hw⟩
  · refine ⟨-Y₁ * (α * β), -X₁ * β, -(X₀ * Y₁ - Y₀ * X₁) * α, (X₁ ^ 2 - α * Y₁ ^ 2) * (α * β),
      Or.inr (Or.inr (Or.inr (mul_ne_zero hw (mul_ne_zero hα hβ)))), ?_⟩
    linear_combination (-(α * β * (X₁ ^ 2 - α * Y₁ ^ 2))) * h1 - α * β * (X₀ * X₁ - α * (Y₀ * Y₁)) * h2

theorem isotropic_four_iff {a : Fin 4 → k} (ha : a 0 ≠ 0) :
    (∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
        x ^ 2 - (-(a 0 * a 1)) * y ^ 2 - (-(a 0 * a 2)) * z ^ 2 + (a 0 * a 3) * t ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_four] at h
    refine ⟨a 0 * x 0, x 1, x 2, x 3, ?_, by linear_combination a 0 * h⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, h1, h2, h3⟩ := hc
    apply hx
    funext i
    fin_cases i
    · simpa [ha] using h0
    · exact h1
    · exact h2
    · exact h3
  · rintro ⟨x, y, z, t, hx, h⟩
    refine ⟨![x / a 0, y, z, t], ?_, ?_⟩
    · intro hc
      have h0 := congrFun hc 0
      have h1 := congrFun hc 1
      have h2 := congrFun hc 2
      have h3 := congrFun hc 3
      simp [ha] at h0 h1 h2 h3
      simp [h0, h1, h2, h3] at hx
    · rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp
      linear_combination h

theorem isotropic_succ_iff {n : ℕ} {a : Fin (n + 1) → k} :
    (∃ x : Fin (n + 1) → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ (t : k) (z : Fin n → k), (t ≠ 0 ∨ z ≠ 0) ∧ a 0 * t ^ 2 + ∑ i, a i.succ * z i ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_succ] at h
    refine ⟨x 0, fun i => x i.succ, ?_, h⟩
    by_contra hc
    push Not at hc
    apply hx
    funext i
    refine Fin.cases hc.1 (fun j => congrFun hc.2 j) i
  · rintro ⟨t, z, hx, h⟩
    refine ⟨Fin.cons t z, ?_, by simpa [Fin.sum_univ_succ] using h⟩
    intro hc
    rcases hx with hx | hx
    · exact hx (by simpa using congrFun hc 0)
    · exact hx (funext fun i => by simpa using congrFun hc i.succ)

theorem exists_value_isotropic [CharZero k] {n : ℕ} {a a' : k} (ha : a ≠ 0) (ha' : a' ≠ 0)
    {b : Fin (n + 1) → k} (hb : b 0 ≠ 0) {x y : k} {z : Fin (n + 1) → k}
    (h0 : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (h : a * x ^ 2 + (a' * y ^ 2 + ∑ i, b i * z i ^ 2) = 0) :
    ∃ x y : k, a * x ^ 2 + a' * y ^ 2 ≠ 0 ∧ ∀ μ : k, IsSquare (μ / (a * x ^ 2 + a' * y ^ 2)) →
      ∃ (t : k) (z : Fin (n + 1) → k), (t ≠ 0 ∨ z ≠ 0) ∧ μ * t ^ 2 + ∑ i, b i * z i ^ 2 = 0 := by
  have key : ∀ ν : k, ν ≠ 0 → ∀ z : Fin (n + 1) → k, ν + ∑ i, b i * z i ^ 2 = 0 →
      ∀ μ : k, IsSquare (μ / ν) →
      ∃ (t : k) (z : Fin (n + 1) → k), (t ≠ 0 ∨ z ≠ 0) ∧ μ * t ^ 2 + ∑ i, b i * z i ^ 2 = 0 := by
    rintro ν hν z hz μ ⟨s, hs⟩
    refine ⟨1, fun i => s * z i, Or.inl one_ne_zero, ?_⟩
    have : ∑ i, b i * (s * z i) ^ 2 = s ^ 2 * ∑ i, b i * z i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [div_eq_iff hν] at hs
    rw [this, hs]
    linear_combination s ^ 2 * hz
  by_cases hμ : a * x ^ 2 + a' * y ^ 2 = 0
  · by_cases hz : z = 0
    · have hy : y ≠ 0 := by
        rintro rfl
        have hx : x = 0 := by simpa [ha] using hμ
        simp [hx, hz] at h0
      obtain ⟨X, Y, hXY⟩ := GlobalTheory.Published.HasseNormSt.of_isSquare (δ := -a' / a) (by simp [ha, ha'])
        ⟨x / y, by field_simp; linear_combination -hμ⟩ (-b 0 / a)
      have e : a * X ^ 2 + a' * Y ^ 2 = -b 0 := by
        field_simp at hXY
        linear_combination -hXY
      refine ⟨X, Y, by rw [e]; exact neg_ne_zero.2 hb, key _ (by rw [e]; exact neg_ne_zero.2 hb)
        (Pi.single 0 1) ?_⟩
      rw [e, Fin.sum_univ_succ]
      simp
    · refine ⟨1, 0, by simpa using ha, fun μ _ => ⟨0, z, Or.inr hz, ?_⟩⟩
      linear_combination h - hμ
  · exact ⟨x, y, hμ, key _ hμ z (by linear_combination h)⟩

theorem isotropic_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ → ι)
    (he : Function.Injective e) {a : ι → k}
    (h : ∃ x : κ → k, x ≠ 0 ∧ ∑ j, a (e j) * x j ^ 2 = 0) :
    ∃ x : ι → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨x, hx, h⟩ := h
  refine ⟨Function.extend e x 0, fun hc => hx (funext fun j => ?_), ?_⟩
  · simpa [he.extend_apply] using congrFun hc (e j)
  · rw [← h]
    symm
    refine Finset.sum_of_injOn e he.injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro i _ hi
      rw [Function.extend_apply' _ _ _ (by simpa using hi)]
      simp
    · intro j _
      rw [he.extend_apply]

theorem isotropic_real {ι : Type*} [Fintype ι] {a : ι → ℝ} {i j : ι} (hi : a i < 0) (hj : 0 < a j) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  have hij : i ≠ j := by rintro rfl; linarith
  refine isotropic_of_injective ![i, j] ?_ ⟨![√(a j), √(-a i)], ?_, ?_⟩
  · intro p q h
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro hc
    have := congrFun hc 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    exact (Real.sqrt_pos.2 hj).ne' this
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Real.sq_sqrt hj.le, Real.sq_sqrt (by linarith)]
    ring

end Algebra

end GlobalTheory.LocalQuad
end

section
universe u_1

namespace GlobalTheory.NonzeroIsotropic

open MvPolynomial

theorem quadForm_totalDegree_le {k : Type u_1} [Field k] (a : Fin 3 → Fin 3 → k) :
    (∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  calc (C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree
      ≤ (C (a i j) * X i : MvPolynomial (Fin 3) k).totalDegree + (X j : MvPolynomial (Fin 3) k).totalDegree :=
        totalDegree_mul _ _
    _ ≤ ((C (a i j) : MvPolynomial (Fin 3) k).totalDegree + (X i : MvPolynomial (Fin 3) k).totalDegree)
          + (X j : MvPolynomial (Fin 3) k).totalDegree := by gcongr; exact totalDegree_mul _ _
    _ = 2 := by simp [totalDegree_C, totalDegree_X]

theorem exists_nonzero_isotropic :
    ∀ {k : Type u_1} [inst : Field k] [Finite k] (a : Fin (3 : ℕ) → Fin (3 : ℕ) → k),
      ∃ (x : Fin (3 : ℕ) → k), x ≠ (0 : Fin (3 : ℕ) → k) ∧
        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), a i j * x i * x j = (0 : k) := by
  intro k _ _ a
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI := hp
  have hpp : p.Prime := by
    rcases CharP.char_is_prime_or_zero k p with h | h
    · exact h
    · subst h
      haveI : CharZero k := CharP.charP_to_charZero k
      exact absurd (Finite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective) (by
        intro h; exact not_finite ℕ)
  set f : MvPolynomial (Fin 3) k := ∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j with hf
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have : f.totalDegree ≤ 2 := quadForm_totalDegree_le a
    simp only [Fintype.card_fin]; omega
  have hdvd := char_dvd_card_solutions p hdeg
  have heval : ∀ x : Fin 3 → k, eval x f = ∑ i : Fin 3, ∑ j : Fin 3, a i j * x i * x j := by
    intro x; simp [hf]
  let z : { x : Fin 3 → k // eval x f = 0 } := ⟨0, by rw [heval]; simp⟩
  have hcard : 1 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := by
    have hpos : 0 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := Fintype.card_pos_iff.mpr ⟨z⟩
    have := Nat.le_of_dvd hpos hdvd
    have := hpp.two_le
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcard z
  refine ⟨y.1, fun h => hy (Subtype.ext h), ?_⟩
  rw [← heval]; exact y.2

end GlobalTheory.NonzeroIsotropic
end

section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace TernaryResidue

open MvPolynomial in

theorem exists_ne_zero_sum_eq_zero {k : Type*} [Field k] [Finite k] (a : Fin 3 → Fin 3 → k) :
    ∃ x : Fin 3 → k, x ≠ 0 ∧ ∑ i, ∑ j, a i j * x i * x j = 0 := by
  first
  | exact @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | (apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic ..)

end TernaryResidue

theorem exists_unit_valued_ternary_lt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : Fin 3 → Fin 3 → v.adicCompletion F)
    (hc : ∀ i j, Valued.v (c i j) ≤ 1) :
    ∃ x : Fin 3 → v.adicCompletion F, (∀ i, Valued.v (x i) ≤ 1) ∧ (∃ i, Valued.v (x i) = 1) ∧
      Valued.v (∑ i, ∑ j, c i j * x i * x j) < 1 := by
  classical
  choose r hr using fun i j => GlobalTheory.Idele.exists_valued_sub_le v (hc i j) 1
  let ι : 𝓞 F →+* v.adicCompletion F :=
    (algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)
  have hι : ∀ y : 𝓞 F, Valued.v (ι y) = v.valuation F (algebraMap (𝓞 F) F y) := fun y =>
    GlobalTheory.Idele.valued_algebraMap v _
  have hle : ∀ y : 𝓞 F, Valued.v (ι y) ≤ 1 := fun y => by
    rw [hι]; exact v.valuation_le_one y
  have hlt : ∀ y : 𝓞 F, Valued.v (ι y) < 1 ↔ y ∈ v.asIdeal := fun y => by
    rw [hι]; exact v.valuation_lt_one_iff_mem y
  have hr' : ∀ i j, Valued.v (c i j - ι (r i j)) < 1 := fun i j => by
    refine (hr i j).trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨x, hx0, hx⟩ := TernaryResidue.exists_ne_zero_sum_eq_zero
    (k := 𝓞 F ⧸ v.asIdeal) fun i j => Ideal.Quotient.mk v.asIdeal (r i j)
  choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
  refine ⟨fun i => ι (y i), fun i => hle _, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    refine ⟨i, le_antisymm (hle _) (not_lt.1 fun h => hi ?_)⟩
    rw [← hy i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hlt _).1 h)
  · have hmem : (∑ i, ∑ j, r i j * y i * y j) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hx]
      simp only [map_sum, map_mul, hy]
    have hsplit : ∑ i, ∑ j, c i j * ι (y i) * ι (y j) =
        ι (∑ i, ∑ j, r i j * y i * y j) +
          ∑ i, ∑ j, (c i j - ι (r i j)) * ι (y i) * ι (y j) := by
      simp only [map_sum, map_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ((hlt _).2 hmem) ?_
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => Valuation.map_sum_lt _ one_ne_zero
      fun j _ => ?_
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_right' (hle _)).trans_lt
      ((mul_le_of_le_one_right' (hle _)).trans_lt (hr' i j))

end GlobalTheory.LocalQuad
end

section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace FiveVar

variable {K : Type*} [Field K] {n : Type*} [Fintype n]

def qf (a x : n → K) : K := ∑ i, a i * x i ^ 2

def bf (a x y : n → K) : K := ∑ i, 2 * a i * x i * y i

lemma qf_add (a x y : n → K) : qf a (x + y) = qf a x + bf a x y + qf a y := by
  simp only [qf, bf, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma qf_smul (a x : n → K) (s : K) : qf a (s • x) = s ^ 2 * qf a x := by
  simp only [qf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_smul_left (a x y : n → K) (s : K) : bf a (s • x) y = s * bf a x y := by
  simp only [bf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_smul_right (a x y : n → K) (s : K) : bf a x (s • y) = s * bf a x y := by
  simp only [bf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_add_left (a x y z : n → K) : bf a (x + y) z = bf a x z + bf a y z := by
  simp only [bf, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_self (a x : n → K) : bf a x x = 2 * qf a x := by
  simp only [bf, qf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma qf_three (a p q r : n → K) (x : Fin 3 → K) (w : K) :
    qf a (x 0 • p + x 1 • q + x 2 • r) / w = ∑ i, ∑ j,
      (![![qf a p / w, bf a p q / w, bf a p r / w], ![0, qf a q / w, bf a q r / w],
        ![0, 0, qf a r / w]] : Fin 3 → Fin 3 → K) i j * x i * x j := by
  rw [qf_add, qf_add, bf_add_left]
  simp [Fin.sum_univ_three, qf_smul, bf_smul_left, bf_smul_right]
  ring

lemma val_bf_sq_le (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (x y : n → K) :
    v (bf a x y) ^ 2 ≤ v (qf a x) * v (qf a y) := by
  by_contra hlt
  rw [not_le] at hlt
  have hb : bf a x y ≠ 0 := by
    intro h
    rw [h] at hlt
    simp at hlt
  have hvb : v (bf a x y) ≠ 0 := by simpa using hb
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hv4 : v 4 ≠ 0 := by simpa using h4
  have hv4' : v 4 ≤ 1 := by
    have e : (4 : K) = 1 + 1 + 1 + 1 := by norm_num
    have h1 : v 1 ≤ 1 := (map_one v).le
    rw [e]
    exact v.map_add_le (v.map_add_le (v.map_add_le h1 h1) h1) h1
  have hx : qf a x ≠ 0 := by
    intro h
    apply hb
    rw [han x h]
    simp [bf]
  obtain ⟨s, hs⟩ := hsq (1 - 4 * (qf a x * qf a y) / bf a x y ^ 2) (by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_div₀, map_mul, map_mul, map_pow,
      mul_div_assoc]
    have h1 : v (qf a x) * v (qf a y) / v (bf a x y) ^ 2 < 1 :=
      (div_lt_one₀ (pow_pos (zero_lt_iff.mpr hvb) 2)).mpr hlt
    calc v 4 * (v (qf a x) * v (qf a y) / v (bf a x y) ^ 2) < v 4 * 1 :=
          mul_lt_mul_of_pos_left h1 (zero_lt_iff.mpr hv4)
      _ = v 4 := mul_one _)
  set t := (-bf a x y + bf a x y * s) / (2 * qf a x) with ht
  have h0 : qf a (t • x + y) = 0 := by
    rw [qf_add, qf_smul, bf_smul_left, ht]
    have hs' : 4 * (qf a x * qf a y) = bf a x y ^ 2 * (1 - s * s) := by
      rw [← hs]; field_simp; ring
    have : qf a y = bf a x y ^ 2 * (1 - s * s) / (4 * qf a x) := by
      rw [← hs']; field_simp
    rw [this]
    have h4' : (4 : K) = 2 * 2 := by norm_num
    rw [h4']
    field_simp
    ring
  have hy : y = (-t) • x := by
    have := han _ h0
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right this
  clear_value t
  subst hy
  rw [bf_smul_right, bf_self, qf_smul] at hlt
  have e : ((-t) * (2 * qf a x)) ^ 2 = 4 * (qf a x * ((-t) ^ 2 * qf a x)) := by ring
  rw [← map_pow, e, ← map_mul v (qf a x), map_mul v 4] at hlt
  exact absurd hlt (not_lt.mpr (mul_le_of_le_one_left' hv4'))

variable [DecidableEq n]

lemma val_det_le (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (P : Matrix n n K) :
    v (∏ i, 2 * a i) * v P.det ^ 2 ≤ ∏ i, v (qf a (P i)) := by
  have hB : P * Matrix.diagonal (fun i => 2 * a i) * Pᵀ =
      Matrix.of fun i j => bf a (P i) (P j) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, bf]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hd := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hd
  have e : v (∏ i, 2 * a i) * v P.det ^ 2 = v (P.det * (∏ i, 2 * a i) * P.det) := by
    rw [map_mul, map_mul, sq, mul_comm (v P.det) (v (∏ i, 2 * a i)), mul_assoc]
  rw [e, hd, Matrix.det_apply']
  apply Valuation.map_sum_le
  intro σ _
  have hε : v (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [map_mul, hε, one_mul, map_prod]
  apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero zero_le'
  rw [← Finset.prod_pow]
  calc ∏ i, v (Matrix.of (fun i j => bf a (P i) (P j)) (σ i) i) ^ 2
      ≤ ∏ i, (v (qf a (P (σ i))) * v (qf a (P i))) :=
        Finset.prod_le_prod' fun i _ => val_bf_sq_le h2 v hsq a han _ _
    _ = (∏ i, v (qf a (P i))) ^ 2 := by
        rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => v (qf a (P i))), sq]

lemma exists_basis (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) :
    ∃ P : Matrix n n K, (∀ j, qf a (P j) ≠ 0) ∧
      ∀ (c : n → K) (j : n), v (c j) ^ 2 * v (qf a (P j)) ≤ v (qf a (∑ k, c k • P k)) := by
  have hrow : ∀ P : Matrix n n K, P.det ≠ 0 → ∀ j, qf a (P j) ≠ 0 := by
    intro P hP j h
    exact hP (Matrix.det_eq_zero_of_row_eq_zero j fun k => congrFun (han _ h) k)
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have := hrow 1 (by simp) i
    apply this
    unfold qf
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : i = k
    · subst hk; simp [h]
    · simp [Matrix.one_apply_ne hk]
  have hD : v (∏ i, 2 * a i) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero h2 (ha i)
  have hprod : ∀ P : Matrix n n K, P.det ≠ 0 → (∏ i, v (qf a (P i))) / v P.det ^ 2 ≠ 0 := by
    intro P hP
    refine div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (pow_ne_zero _ ?_)
    · rw [Valuation.ne_zero_iff]; exact hrow P hP i
    · rw [Valuation.ne_zero_iff]; exact hP
  obtain ⟨m, ⟨P, hP, hm⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ P : Matrix n n K, P.det ≠ 0 ∧
      WithZero.log ((∏ i, v (qf a (P i))) / v P.det ^ 2) = z)
    ⟨WithZero.log (v (∏ i, 2 * a i)), by
      rintro z ⟨P, hP, rfl⟩
      rw [WithZero.log_le_log hD (hprod P hP), le_div_iff₀
        (pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hP)) 2)]
      exact val_det_le h2 v hsq a han P⟩
    ⟨_, 1, by simp, rfl⟩
  refine ⟨P, hrow P hP, fun c j => ?_⟩
  by_cases hc : c j = 0
  · simp [hc]
  have hdet : (P.updateRow j (∑ k, c k • P k)).det = c j * P.det := by
    rw [Matrix.det_updateRow_sum, smul_eq_mul]
  have hP' : (P.updateRow j (∑ k, c k • P k)).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hc hP
  have h := hmin _ ⟨_, hP', rfl⟩
  rw [← hm, WithZero.log_le_log (hprod P hP) (hprod _ hP'), hdet,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Matrix.updateRow_self] at h
  have e : ∏ i ∈ Finset.univ.erase j, v (qf a (P.updateRow j (∑ k, c k • P k) i)) =
      ∏ i ∈ Finset.univ.erase j, v (qf a (P i)) :=
    Finset.prod_congr rfl fun i hi => by rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hi)]
  rw [e] at h
  have hR : 0 < ∏ i ∈ Finset.univ.erase j, v (qf a (P i)) :=
    zero_lt_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
      (Valuation.ne_zero_iff v).mpr (hrow P hP i))
  have hd : 0 < v P.det ^ 2 := pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hP)) 2
  have hcj : 0 < v (c j) ^ 2 := pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hc)) 2
  rw [map_mul, mul_pow, ← div_div, div_le_div_iff_of_pos_right hd, le_div_iff₀ hcj,
    mul_right_comm, mul_le_mul_iff_left₀ hR, mul_comm] at h
  exact h

lemma exists_three (f : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f j = f i ∧ f k = f i := by
  revert f
  decide

lemma exists_scale (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0)
    (h : decide (Even (WithZero.log (v y))) = decide (Even (WithZero.log (v x)))) :
    ∃ u : K, v u ^ 2 * v y = v x := by
  have he : Even (WithZero.log (v x) - WithZero.log (v y)) := by
    rw [Int.even_sub]
    simpa [eq_comm] using h
  obtain ⟨m, hm⟩ := he
  obtain ⟨u, hu⟩ := hv (WithZero.exp m)
  refine ⟨u, ?_⟩
  rw [hu, ← WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hx),
    ← WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hy), sq, ← WithZero.exp_add,
    ← WithZero.exp_add]
  congr 1
  omega

end FiveVar

open FiveVar in

theorem exists_zero_five_of_valuation {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x)
    (hcw : ∀ c : Fin 3 → Fin 3 → K, (∀ i j, v (c i j) ≤ 1) →
      ∃ x : Fin 3 → K, (∀ i, v (x i) ≤ 1) ∧ (∃ i, v (x i) = 1) ∧
        v (∑ i, ∑ j, c i j * x i * x j) < 1)
    (a : Fin 5 → K) : ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  by_contra hno
  have han : ∀ x, qf a x = 0 → x = 0 := by
    intro x hx
    by_contra h
    exact hno ⟨x, h, hx⟩
  obtain ⟨P, hP, hmin⟩ := exists_basis h2 v hsq a han
  obtain ⟨i, j, k, hij, hik, hjk, hj, hk⟩ :=
    exists_three fun i => decide (Even (WithZero.log (v (qf a (P i)))))
  obtain ⟨s, hs⟩ := exists_scale v hv (hP i) (hP j) hj
  obtain ⟨t, ht⟩ := exists_scale v hv (hP i) (hP k) hk
  set w := qf a (P i) with hw
  have hw0 : w ≠ 0 := hP i
  have hvw : 0 < v w := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hw0)
  have hq : ∀ x, v (qf a x) = v w → v (qf a x / w) ≤ 1 := by
    intro x hx
    rw [map_div₀, hx, div_self hvw.ne']
  have hb : ∀ x y, v (qf a x) = v w → v (qf a y) = v w → v (bf a x y / w) ≤ 1 := by
    intro x y hx hy
    rw [map_div₀, div_le_one₀ hvw]
    apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero zero_le'
    have := val_bf_sq_le h2 v hsq a han x y
    rwa [hx, hy, ← sq] at this
  have h0 : v (qf a (P i)) = v w := rfl
  have h1 : v (qf a (s • P j)) = v w := by rw [qf_smul, map_mul, map_pow, hs]
  have h2' : v (qf a (t • P k)) = v w := by rw [qf_smul, map_mul, map_pow, ht]
  obtain ⟨x, -, ⟨l, hl⟩, hx⟩ := hcw
    ![![qf a (P i) / w, bf a (P i) (s • P j) / w, bf a (P i) (t • P k) / w],
      ![0, qf a (s • P j) / w, bf a (s • P j) (t • P k) / w],
      ![0, 0, qf a (t • P k) / w]] (by
      intro p q
      fin_cases p <;> fin_cases q
      · exact hq _ h0
      · exact hb _ _ h0 h1
      · exact hb _ _ h0 h2'
      · simp
      · exact hq _ h1
      · exact hb _ _ h1 h2'
      · simp
      · simp
      · exact hq _ h2')
  set c : Fin 5 → K := Pi.single i (x 0) + Pi.single j (x 1 * s) + Pi.single k (x 2 * t) with hc
  have hsum : ∑ p, c p • P p = x 0 • P i + x 1 • s • P j + x 2 • t • P k := by
    simp only [hc, Pi.add_apply, add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
  have hlt : v (qf a (∑ p, c p • P p)) < v w := by
    rw [← div_lt_one₀ hvw, ← map_div₀]
    convert hx using 2
    rw [hsum]
    exact qf_three a _ _ _ x w
  fin_cases l
  · have := hmin c i
    have e : c i = x 0 := by simp [hc, hij, hik]
    have hl' : v (x 0) = 1 := hl
    rw [e, hl', one_pow, one_mul] at this
    exact absurd hlt (not_lt.mpr this)
  · have := hmin c j
    have e : c j = x 1 * s := by simp [hc, hij.symm, hjk]
    have hl' : v (x 1) = 1 := hl
    rw [e, map_mul, hl', one_mul, hs] at this
    exact absurd hlt (not_lt.mpr this)
  · have := hmin c k
    have e : c k = x 2 * t := by simp [hc, hik.symm, hjk.symm]
    have hl' : v (x 2) = 1 := hl
    rw [e, map_mul, hl', one_mul, ht] at this
    exact absurd hlt (not_lt.mpr this)

end GlobalTheory.LocalQuad
end

section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

theorem GlobalTheory.LocalQuad.exists_ringHom_adicCompletion (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (φ : v.adicCompletion K →+* w.adicCompletion L),
      ∀ x : K, φ (algebraMap K (v.adicCompletion K) x) =
        algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  let v : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L v w).continuous
  refine ⟨v, ((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
end

section
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.LocalQuad

namespace HermClass

section Congr

variable {E : Type*} [Field E] {c : E →+* E} {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

def Congr (c : E →+* E) (G G' : Matrix n n E) : Prop :=
  ∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c

theorem Congr.refl (G : Matrix n n E) : Congr c G G :=
  ⟨1, by simp, by simp [Matrix.map_one _ (map_zero c) (map_one c)]⟩

theorem Congr.trans {G G' G'' : Matrix n n E} (h : Congr c G G') (h' : Congr c G' G'') :
    Congr c G G'' := by
  obtain ⟨P, hP, rfl⟩ := h
  obtain ⟨Q, hQ, rfl⟩ := h'
  refine ⟨P * Q, by rw [Matrix.det_mul]; exact mul_ne_zero hP hQ, ?_⟩
  rw [Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem Congr.symm {G G' : Matrix n n E} (h : Congr c G G') : Congr c G' G := by
  obtain ⟨P, hP, rfl⟩ := h
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  refine ⟨P⁻¹, (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero, ?_⟩
  have e1 : P⁻¹ᵀ * Pᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
  have e2 : P.map c * P⁻¹.map c = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  calc G = (P⁻¹ᵀ * Pᵀ) * G * (P.map c * P⁻¹.map c) := by
        rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem Congr.det {G G' : Matrix n n E} (h : Congr c G G') :
    ∃ x : E, x ≠ 0 ∧ G'.det = x * c x * G.det := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.det, hP, ?_⟩
  have : (P.map c).det = c P.det := (RingHom.map_det c P).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, this]
  ring

theorem Congr.submatrix {G G' : Matrix n n E} (h : Congr c G G') (e : m ≃ n) :
    Congr c (G.submatrix e e) (G'.submatrix e e) := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.submatrix e e, by rwa [Matrix.det_submatrix_equiv_self], ?_⟩
  rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]

theorem Congr.fromBlocks {G G' : Matrix n n E} (h : Congr c G G') (D : Matrix m m E) :
    Congr c (Matrix.fromBlocks G 0 0 D) (Matrix.fromBlocks G' 0 0 D) := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨Matrix.fromBlocks P 0 0 1, by simpa using hP, ?_⟩
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_zero _ (map_zero c)]

theorem congr_diagonal_of_tail {r : ℕ} {g g' : Fin (r + 1) → E} (h0 : g 0 = g' 0)
    (h : Congr c (Matrix.diagonal fun i : Fin r => g i.succ)
      (Matrix.diagonal fun i : Fin r => g' i.succ)) :
    Congr c (Matrix.diagonal g) (Matrix.diagonal g') := by
  let e : Fin (r + 1) ≃ Fin r ⊕ PUnit.{1} := (finSuccEquiv r).trans (Equiv.optionEquivSumPUnit _)
  have key : ∀ k : Fin (r + 1) → E, Matrix.diagonal k =
      (Matrix.fromBlocks (Matrix.diagonal fun i : Fin r => k i.succ) 0 0
        (Matrix.diagonal fun _ : PUnit.{1} => k 0)).submatrix e e := by
    intro k
    rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [e]
  rw [key g, key g', h0]
  exact (h.fromBlocks _).submatrix e

end Congr

theorem exists_zero_coord_ne_zero {F : Type*} [Field F] [CharZero F] {ι : Type*} [Fintype ι]
    {a : ι → F} (ha : ∀ i, a i ≠ 0) {z : ι → F} (hz : z ≠ 0) (h : ∑ i, a i * z i ^ 2 = 0)
    (i : ι) : ∃ w : ι → F, w i ≠ 0 ∧ ∑ k, a k * w k ^ 2 = 0 := by
  classical
  by_cases hi : z i = 0
  swap
  · exact ⟨z, hi, h⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
  have hj : z j ≠ 0 := hj
  have hij : i ≠ j := by
    rintro rfl
    exact hj hi
  have haj := ha j
  set t : F := -(a i + a j) / (2 * a j * z j) with ht
  refine ⟨fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k, ?_, ?_⟩
  · simp [hij, hi]
  · have : ∀ k, a k * ((if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k) ^ 2 =
        (if k = i then a i else 0) + (if k = j then a j + 2 * t * a j * z j else 0) +
          t ^ 2 * (a k * z k ^ 2) := by
      intro k
      by_cases h1 : k = i
      · subst h1
        simp [hij, hi]
      · by_cases h2 : k = j
        · subst h2
          simp only [h1, if_false, if_true]
          ring
        · simp only [h1, h2, if_false]
          ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [ht]
    field_simp
    ring

def Isotropy : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (a : ι → F),
    5 ≤ Fintype.card ι → (∀ i, a i ≠ 0) → (∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) →
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_real {x : E} (hx : cc x = x) : x ∈ maximalRealSubfield E :=
  (IsCMField.complexConj_eq_self_iff E _).mp hx

theorem re_ne_zero (τ : E →+* ℂ) {x : E} (hx : cc x = x) (h0 : x ≠ 0) : (τ x).re ≠ 0 := by
  intro h
  have h1 := GlobalTheory.Published.embedding_cc τ x
  rw [hx] at h1
  have h2 : (τ x).im = 0 := Complex.conj_eq_iff_im.mp h1.symm
  exact (map_ne_zero τ).mpr h0 (Complex.ext h h2)

theorem exists_represent (H : Isotropy) {r : ℕ} (hr : 2 ≤ r) {g : Fin r → E}
    (hg : ∀ i, cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0) {c : E} (hc : cc c = c) (hc0 : c ≠ 0)
    (hs : ∀ τ : E →+* ℂ, ∃ i, (0 < (τ (g i)).re ↔ 0 < (τ c).re)) :
    ∃ z : Fin r → E, herm (Matrix.diagonal g) z z = c := by
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  obtain ⟨d, hd⟩ := GlobalTheory.Published.exists_sq_real hθ
  let γ : Fin r → maximalRealSubfield E := fun i => ⟨g i, mem_real (hg i)⟩
  let κ : maximalRealSubfield E := ⟨c, mem_real hc⟩
  have hγ : ∀ i, γ i ≠ 0 := fun i h => hg0 i (congrArg Subtype.val h)
  have hκ : κ ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (hd.symm.trans (congrArg Subtype.val h))
  let a : Option (Fin r ⊕ Fin r) → maximalRealSubfield E :=
    fun o => o.elim (-κ) (Sum.elim γ fun i => -d * γ i)
  have ha : ∀ o, a o ≠ 0 := by
    rintro (_ | i | i)
    · exact neg_ne_zero.mpr hκ
    · exact hγ i
    · exact mul_ne_zero (neg_ne_zero.mpr hd0) (hγ i)
  obtain ⟨x, hx, hx0⟩ := H (maximalRealSubfield E) (Option (Fin r ⊕ Fin r)) a
    (by simp; omega) ha (by
      intro σ
      let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp σ)
      have hτ : ∀ y : maximalRealSubfield E, (τ (y : E)).re = σ y := fun y => by
        have : τ (y : E) = (Complex.ofRealHom.comp σ) y :=
          ComplexEmbedding.lift_algebraMap_apply E _ y
        rw [this]
        simp
      obtain ⟨i, hi⟩ := hs τ
      have e1 : (τ (g i)).re = σ (γ i) := hτ (γ i)
      have e2 : (τ c).re = σ κ := hτ κ
      rw [e1, e2] at hi
      have n1 : σ (γ i) ≠ 0 := (map_ne_zero σ).mpr (hγ i)
      have n2 : σ κ ≠ 0 := (map_ne_zero σ).mpr hκ
      rcases lt_or_gt_of_ne n2 with h | h
      · refine ⟨some (Sum.inl i), none, ?_, ?_⟩
        · exact lt_of_le_of_ne (not_lt.mp fun h' => absurd (hi.mp h') h.not_gt) n1
        · simpa [a] using h
      · refine ⟨none, some (Sum.inl i), ?_, hi.mpr h⟩
        simpa [a] using h)
  obtain ⟨w, hw, hw0⟩ := exists_zero_coord_ne_zero ha hx hx0 none
  rw [Fintype.sum_option, Fintype.sum_sum_type] at hw0
  have hw1 := congrArg (Subtype.val : maximalRealSubfield E → E) hw0
  have hw2 : (w none : E) ≠ 0 := fun h => hw (Subtype.ext h)
  simp [a, γ, κ, hd] at hw1
  refine ⟨fun i => ((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none, ?_⟩
  have hcc : ∀ i, cc (((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none) =
      ((w (some (Sum.inl i)) : E) - w (some (Sum.inr i)) * θ) / w none := by
    intro i
    have : IsCMField.complexConj E θ = -θ := hθ
    simp [cc, this, sub_eq_add_neg]
  simp only [herm, hcc, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have : ∀ i, ((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none * g i *
      (((w (some (Sum.inl i)) : E) - w (some (Sum.inr i)) * θ) / w none) =
      (g i * (w (some (Sum.inl i)) : E) ^ 2 -
        θ * θ * g i * (w (some (Sum.inr i)) : E) ^ 2) / (w none : E) ^ 2 := by
    intro i
    field_simp
    ring
  simp only [this, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [div_eq_iff (pow_ne_zero 2 hw2)]
  linear_combination hw1

noncomputable def posCount (τ : E →+* ℂ) {r : ℕ} (g : Fin r → E) : ℕ :=
  (Finset.univ.filter fun k => 0 < (τ (g k)).re).card

omit [NumberField E] [IsCMField E] in
theorem posCount_succ (τ : E →+* ℂ) {r : ℕ} (g : Fin (r + 1) → E) :
    posCount τ g = (if 0 < (τ (g 0)).re then 1 else 0) + posCount τ fun i : Fin r => g i.succ := by
  simp only [posCount, Finset.card_filter, Fin.sum_univ_succ]

omit [NumberField E] [IsCMField E] in
theorem posIndex_diagonal_map (τ : E →+* ℂ) {r : ℕ} (g : Fin r → E) :
    GlobalTheory.Inertia.posIndex ((Matrix.diagonal g).map τ) = posCount τ g := by
  rw [Matrix.diagonal_map (map_zero τ), GlobalTheory.Inertia.posIndex_diagonal]
  rfl

theorem posIndex_of_congr (τ : E →+* ℂ) {r : ℕ} {G G' : Matrix (Fin r) (Fin r) E}
    (h : Congr (IsCMField.complexConj E : E →+* E) G G') :
    GlobalTheory.Inertia.posIndex (G'.map τ) = GlobalTheory.Inertia.posIndex (G.map τ) := by
  obtain ⟨P, hP, rfl⟩ := h
  exact GlobalTheory.Inertia.posIndex_map_congr τ G hP

omit [NumberField E] [IsCMField E] in
theorem exists_sign_iff (τ : E →+* ℂ) {r : ℕ} {g g' : Fin r → E}
    (h : posCount τ g = posCount τ g') (j : Fin r) :
    ∃ i, (0 < (τ (g i)).re ↔ 0 < (τ (g' j)).re) := by
  by_contra hne
  push Not at hne
  by_cases hj : 0 < (τ (g' j)).re
  · have h1 : posCount τ g = 0 := by
      rw [posCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      rcases hne i with h | h
      · exact absurd hj (not_lt.mpr h.2)
      · exact absurd hi (not_lt.mpr h.1)
    rw [h, posCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    exact h1 (Finset.mem_univ j) hj
  · have h1 : posCount τ g = Fintype.card (Fin r) := by
      rw [posCount, Finset.card_eq_iff_eq_univ, Finset.filter_eq_self]
      intro i _
      rcases hne i with h | h
      · exact h.1
      · exact absurd h.2 hj
    rw [h, posCount, Finset.card_eq_iff_eq_univ, Finset.filter_eq_self] at h1
    exact hj (h1 j (Finset.mem_univ j))

theorem congr_diagonal (H : Isotropy) (r : ℕ) : ∀ g g' : Fin r → E,
    (∀ i, cc (g i) = g i) → (∀ i, cc (g' i) = g' i) → (∀ i, g i ≠ 0) → (∀ i, g' i ≠ 0) →
    (∀ τ : E →+* ℂ, posCount τ g = posCount τ g') →
    (∃ x : E, ∏ i, g i = x * cc x * ∏ i, g' i) →
    Congr (IsCMField.complexConj E : E →+* E) (Matrix.diagonal g) (Matrix.diagonal g') := by
  induction r with
  | zero =>
    intro g g' _ _ _ _ _ _
    exact GlobalTheory.Published.Landherr.size_zero _ _
  | succ r ih =>
    intro g g' hg hg' h0 h0' hs ⟨x, hx⟩
    have hp : ∏ i, g i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h0 i
    have hp' : ∏ i, g' i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h0' i
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · refine GlobalTheory.Published.Landherr.size_one _ _ (by rwa [Matrix.det_diagonal])
        (by rwa [Matrix.det_diagonal]) ⟨x, ?_⟩
      rw [Matrix.det_diagonal, Matrix.det_diagonal, hx, mul_div_cancel_right₀ _ hp']
    obtain ⟨z, hz⟩ := exists_represent H (by omega) hg h0 (hg' 0) (h0' 0)
      fun τ => exists_sign_iff τ (hs τ) 0
    have hG : ∀ a b, cc (Matrix.diagonal g a b) = Matrix.diagonal g b a := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simpa using hg a
      · simp [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), cc]
    obtain ⟨P, k, hP, hPk, hk, hk0, -, hk1⟩ :=
      GlobalTheory.HermDiag.exists_congr_diagonal_herm_col_eq hG (x := z) (hz ▸ h0' 0) 0
    have hk0 := hk0 (by rwa [Matrix.det_diagonal])
    have hc : Congr (IsCMField.complexConj E : E →+* E) (Matrix.diagonal g) (Matrix.diagonal k) :=
      ⟨P, hP, hPk.symm⟩
    have hk2 : k 0 = g' 0 := hk1.trans hz
    refine hc.trans (congr_diagonal_of_tail hk2 (ih _ _ (fun i => hk _) (fun i => hg' _)
      (fun i => hk0 _) (fun i => h0' _) (fun τ => ?_) ?_))
    · have h1 := posIndex_of_congr τ hc
      rw [posIndex_diagonal_map, posIndex_diagonal_map, hs τ, posCount_succ, posCount_succ τ g',
        hk2] at h1
      exact Nat.add_left_cancel h1
    · obtain ⟨y, -, hy⟩ := hc.det
      rw [Matrix.det_diagonal, Matrix.det_diagonal, hx, Fin.prod_univ_succ, Fin.prod_univ_succ,
        hk2] at hy
      refine ⟨y * x, mul_left_cancel₀ (h0' 0) ?_⟩
      rw [hy]
      simp only [cc, map_mul, RingHom.coe_coe]
      ring

end HermClass

open HermClass in

theorem landherr_of_isotropy
    (H : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (a : ι → F),
      5 ≤ Fintype.card ι → (∀ i, a i ≠ 0) → (∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) →
      ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) :
    GlobalTheory.Published.Landherr := by
  intro E _ _ _ r G G' hG hG' hd hd' hs ⟨x, hx⟩
  obtain ⟨P, g, hP, hPg, hg, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  obtain ⟨P', g', hP', hPg', hg', hg0'⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG'
  have hc : Congr (IsCMField.complexConj E : E →+* E) G (Matrix.diagonal g) := ⟨P, hP, hPg.symm⟩
  have hc' : Congr (IsCMField.complexConj E : E →+* E) G' (Matrix.diagonal g') :=
    ⟨P', hP', hPg'.symm⟩
  refine (hc.trans (congr_diagonal H r g g' hg hg' (hg0 hd) (hg0' hd') (fun τ => ?_) ?_)).trans
    hc'.symm
  · obtain ⟨Q, hQ, h⟩ := hs τ
    rw [← posIndex_diagonal_map, ← posIndex_diagonal_map, posIndex_of_congr τ hc,
      posIndex_of_congr τ hc', h, GlobalTheory.Inertia.posIndex_congr _ hQ]
  · obtain ⟨y, -, hy⟩ := hc.det
    obtain ⟨y', -, hy'⟩ := hc'.symm.det
    rw [div_eq_iff hd'] at hx
    rw [Matrix.det_diagonal] at hy hy'
    refine ⟨y * x * y', ?_⟩
    rw [hy, hx, hy']
    simp only [cc, map_mul, RingHom.coe_coe]
    ring

end GlobalTheory.LocalQuad
end

section
open scoped Matrix

namespace GlobalTheory.LocalQuad.TraceIsometry

open Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {c : E →+* E}

theorem finiteDimensional_of_involution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) : FiniteDimensional F E := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ : E, ∀ x : E, ∃ s t : F, x = s • (1 : E) + t • δ := by
    by_cases h : ∀ t, c t = t
    · refine ⟨0, fun x => ?_⟩
      obtain ⟨s, hs⟩ := (hF x).1 (h x)
      exact ⟨s, 0, by simp [Algebra.smul_def, hs]⟩
    · push Not at h
      obtain ⟨u, hu⟩ := h
      have hne : u - c u ≠ 0 := sub_ne_zero.2 hu.symm
      have hne' : c u - u ≠ 0 := sub_ne_zero.2 hu
      refine ⟨u - c u, fun x => ?_⟩
      obtain ⟨s, hs⟩ := (hF ((x + c x) / 2)).1 (by
        rw [map_div₀, map_add, hc, map_ofNat, add_comm])
      obtain ⟨t, ht⟩ := (hF ((x - c x) / (2 * (u - c u)))).1 (by
        rw [map_div₀, map_sub, hc, map_mul, map_ofNat, map_sub, hc]
        field_simp
        ring)
      refine ⟨s, t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, hs, ht]
      field_simp
      ring
  refine Module.finite_def.2 ⟨{1, δ}, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, t, rfl⟩ := hδ x
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem exists_traceForm (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {V : Type*} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x) :
    ∃ b : V →ₗ[F] V →ₗ[F] F, ∀ x y, algebraMap F E (b x y) = B x y + B y x := by
  have h : ∀ x y, ∃ s : F, algebraMap F E s = B x y + B y x := fun x y =>
    (hF _).1 (by rw [map_add, hB, hB, add_comm])
  choose b hb using h
  have hi := (algebraMap F E).injective
  have hs : ∀ s : F, c (algebraMap F E s) = algebraMap F E s := fun s => (hF _).2 ⟨s, rfl⟩
  refine ⟨LinearMap.mk₂ F b (fun x x' y => hi ?_) (fun s x y => hi ?_) (fun x y y' => hi ?_)
    (fun s x y => hi ?_), hb⟩
  · simp only [map_add, hb, LinearMap.add_apply]
    ring
  · rw [smul_eq_mul, map_mul, hb, hb, ← algebraMap_smul E s x]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, hs, smul_eq_mul]
    ring
  · simp only [map_add, hb, LinearMap.add_apply]
    ring
  · rw [smul_eq_mul, map_mul, hb, hb, ← algebraMap_smul E s y]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, hs, smul_eq_mul]
    ring

theorem trace_eq_of_apply_self_eq {V W : Type*} [AddCommGroup V] [Module E V] [AddCommGroup W]
    [Module E W] {B : V →ₗ[E] V →ₛₗ[c] E} {B' : W →ₗ[E] W →ₛₗ[c] E} {φ : V → W}
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hφ : ∀ x, B' (φ x) (φ x) = B x x) (x y : V) :
    B' (φ x) (φ y) + B' (φ y) (φ x) = B x y + B y x := by
  have h := hφ (x + y)
  rw [hadd] at h
  simp only [map_add, LinearMap.add_apply, hφ] at h
  linear_combination h

theorem exists_map_smul_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {V W : Type*} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
    {B : V →ₗ[E] V →ₛₗ[c] E} {B' : W →ₗ[E] W →ₛₗ[c] E} (hB' : ∀ x y, c (B' x y) = B' y x)
    (φ : V →ₗ[F] W) (hφ : ∀ x, B' (φ x) (φ x) = B x x) {e : V} (he : B e e ≠ 0) :
    ∃ φ' : V →ₗ[F] W, (∀ x, B' (φ' x) (φ' x) = B x x) ∧ ∀ t : E, φ' (t • e) = t • φ e := by
  have := finiteDimensional_of_involution h2 hc hF
  obtain ⟨b, hb⟩ := exists_traceForm hF hB'
  have hi := (algebraMap F E).injective
  have h2F : (2 : F) ≠ 0 := fun h => h2 (by
    rw [← map_ofNat (algebraMap F E) 2, h, map_zero])
  have hp := trace_eq_of_apply_self_eq (map_add φ) hφ
  obtain ⟨γ, hγ, hγe⟩ := GlobalTheory.HermWitt.exists_isometry_comp_eq_of_nondegenerate
    (c := RingHom.id F) h2F (B := b)
    (fun x y => hi (by rw [RingHom.id_apply, hb, hb, add_comm]))
    (g := φ ∘ₗ (LinearMap.toSpanSingleton E V e).restrictScalars F)
    (f := (LinearMap.toSpanSingleton E W (φ e)).restrictScalars F)
    (fun s t => hi (by
      simp only [hb, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply, hp, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hφ]))
    (fun s hs => by
      have h := congrArg (algebraMap F E) (hs s)
      simp only [hb, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply, hφ, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        map_zero, smul_eq_mul, RingHom.id_apply] at h
      by_contra hne
      exact mul_ne_zero h2 (mul_ne_zero ((map_ne_zero c).2 hne) (mul_ne_zero hne he))
        (by linear_combination h))
  refine ⟨γ.toLinearMap ∘ₗ φ, fun x => ?_, fun t => hγe t⟩
  have h := congrArg (algebraMap F E) (hγ (φ x) (φ x))
  rw [hb, hb, hφ] at h
  apply mul_left_cancel₀ h2
  change 2 * B' (γ (φ x)) (γ (φ x)) = _
  linear_combination h

universe u v in

theorem exists_linearMap_isometry (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) (d : ℕ) :
    ∀ {V : Type u} {W : Type v} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
      [FiniteDimensional E V] [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
      (B : V →ₗ[E] V →ₛₗ[c] E) (B' : W →ₗ[E] W →ₛₗ[c] E),
      (∀ x y, c (B x y) = B y x) → (∀ x y, c (B' x y) = B' y x) → finrank E V = d →
      ∀ φ : V →ₗ[F] W, (∀ x, B' (φ x) (φ x) = B x x) →
      ∃ ψ : V →ₗ[E] W, ∀ x y, B' (ψ x) (ψ y) = B x y := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V W _ _ _ _ _ _ _ _ _ B B' hB hB' hd φ₀ hφ₀
  obtain rfl | hne := eq_or_ne B 0
  · exact ⟨0, fun x y => by simp⟩
  obtain ⟨e, he⟩ := GlobalTheory.HermDiag.exists_apply_self_ne_zero h2 hB hne
  have hk := GlobalTheory.HermDiag.finrank_ker_flip_add_one he
  obtain ⟨φ, hφ, hφe⟩ := exists_map_smul_eq h2 hc hF hB' φ₀ hφ₀ he
  have hf : B' (φ₀ e) (φ₀ e) = B e e := hφ₀ e
  generalize φ₀ e = f at hφe hf
  have hp := trace_eq_of_apply_self_eq (map_add φ) hφ
  have hker : ∀ x : LinearMap.ker (B.flip e), φ x ∈ LinearMap.ker (B'.flip f) := by
    intro x
    have hx : B x e = 0 := x.2
    have hx' : B e x = 0 := by rw [← hB, hx, map_zero]
    have h := hp x (B' (φ x) f • e)
    rw [hφe] at h
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, hx', smul_eq_mul,
      RingHom.id_apply, ← hB' (φ x) f] at h
    change B' (φ x) f = 0
    by_contra hne
    exact mul_ne_zero h2 (mul_ne_zero ((map_ne_zero c).2 hne) hne) (by linear_combination h)
  obtain ⟨ψ, hψ⟩ := ih _ (by omega)
    (B.domRestrict₁₂ (LinearMap.ker (B.flip e)) (LinearMap.ker (B.flip e)))
    (B'.domRestrict₁₂ (LinearMap.ker (B'.flip f)) (LinearMap.ker (B'.flip f)))
    (fun y z => hB y z) (fun y z => hB' y z) rfl
    { toFun := fun x => ⟨φ x, hker x⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun s x => Subtype.ext (by simp) }
    (fun x => hφ x)
  replace hψ : ∀ x y : LinearMap.ker (B.flip e), B' (ψ x) (ψ y) = B x y := hψ
  let p : V →ₗ[E] LinearMap.ker (B.flip e) :=
    (LinearMap.id - ((B e e)⁻¹ • B.flip e).smulRight e).codRestrict _ (fun x => by
      have h : (B e e)⁻¹ * B x e * B e e = B x e := by field_simp
      simp [h])
  have hpx : ∀ x, (p x : V) = x - ((B e e)⁻¹ * B x e) • e := fun x => rfl
  refine ⟨(LinearMap.ker (B'.flip f)).subtype ∘ₗ ψ ∘ₗ p + ((B e e)⁻¹ • B.flip e).smulRight f,
    fun x y => ?_⟩
  have h1 : ∀ z, B' (ψ z) f = 0 := fun z => (ψ z).2
  have h3 : ∀ z, B' f (ψ z) = 0 := fun z => by rw [← hB', h1, map_zero]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.flip_apply, map_add,
    LinearMap.map_smulₛₗ, h1, h3, hψ, hpx, hf, map_sub, LinearMap.sub_apply, smul_eq_mul,
    RingHom.id_apply, map_mul, map_inv₀, hB]
  field_simp
  ring

end GlobalTheory.LocalQuad.TraceIsometry

theorem GlobalTheory.LocalQuad.exists_congr_iff_trace_forms_isometric {F E : Type*} [Field F] [Field E]
    [Algebra F E] (h2 : (2 : E) ≠ 0) (c : E →+* E) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {n : Type*} [Fintype n] [DecidableEq n] {G G' : Matrix n n E}
    (hG : ∀ a b, c (G a b) = G b a) (hG' : ∀ a b, c (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c) ↔
      ∃ φ : (n → E) ≃ₗ[F] (n → E),
        ∀ x, x ⬝ᵥ G' *ᵥ (c ∘ x) = φ x ⬝ᵥ G *ᵥ (c ∘ φ x) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨(Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP.isUnit)).restrictScalars F,
      fun x => ?_⟩
    rw [GlobalTheory.HermWitt.dotProduct_congr_mulVec]
    rfl
  · rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ⟩ := TraceIsometry.exists_linearMap_isometry h2 hc hF _
      (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G')
      (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
      (fun x y => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
          GlobalTheory.HermDiag.map_dotProduct_mulVec_comp hc hG'])
      (fun x y => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
          GlobalTheory.HermDiag.map_dotProduct_mulVec_comp hc hG])
      rfl φ.toLinearMap
      (fun x => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct]
        exact (hφ x).symm)
    have h : G' = (LinearMap.toMatrix' ψ)ᵀ * G * (LinearMap.toMatrix' ψ).map c := by
      apply (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c).injective
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      rw [← hψ, GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
        GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct, GlobalTheory.HermWitt.dotProduct_congr_mulVec,
        LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    refine ⟨_, fun h0 => hd' ?_, h⟩
    rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]
end

section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

theorem isotropic_ternary_of_units (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (a : Fin 3 → v.adicCompletion F) (ha : ∀ i, Valued.v (a i) = 1) :
    ∃ x : Fin 3 → v.adicCompletion F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨x, -, ⟨k, hk⟩, hx⟩ := exists_unit_valued_ternary_lt_one F v (Matrix.diagonal a) (by
    intro i j
    by_cases h : i = j
    · subst h; simp [ha]
    · simp [Matrix.diagonal_apply_ne _ h])
  have e : ∑ i, ∑ j, Matrix.diagonal a i j * x i * x j = ∑ i, a i * x i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.diagonal_apply_ne _ hj.symm]) (by simp)]
    simp [sq, mul_assoc]
  rw [e] at hx
  set q := ∑ i, a i * x i ^ 2 with hq
  have hu : Valued.v (a k * x k ^ 2) = 1 := by simp [ha, hk]
  have hu0 : a k * x k ^ 2 ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, mul_one]
  have hlt : Valued.v (1 - q / (a k * x k ^ 2) - 1) < 1 := by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_div₀, hu, div_one]; exact hx
  obtain ⟨s, hs⟩ := isSquare_of_valued_sub_one_lt F v (1 - q / (a k * x k ^ 2)) (by rwa [h4])
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [hs] at hlt
    simp at hlt
  have hxk : x k ≠ 0 := by
    intro h; rw [h] at hk; simp at hk
  refine ⟨Function.update x k (x k * s), fun hc => ?_, ?_⟩
  · have := congrFun hc k
    simp [hs0, hxk] at this
  · have h1 : a k * x k ^ 2 * (s * s) = a k * x k ^ 2 - q := by
      rw [← hs, mul_sub, mul_one, mul_div_cancel₀ _ hu0]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hq ⊢
    rw [Finset.sum_congr rfl (g := fun i => a i * x i ^ 2)
      (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]), Function.update_self]
    linear_combination h1 - hq

theorem isotropic_adicCompletion_of_five_le (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {ι : Type*} [Fintype ι] (hι : 5 ≤ Fintype.card ι)
    (a : ι → v.adicCompletion F) :
    ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hι)
  exact isotropic_of_injective e e.injective
    (exists_zero_five_of_valuation two_ne_zero Valued.v (v.valuedAdicCompletion_surjective F)
      (isSquare_of_valued_sub_one_lt F v) (exists_unit_valued_ternary_lt_one F v) _)

theorem exists_norm_over_extension (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [NumberField L] [Algebra F L] {α β γ : F} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) {s : L} (hs : s ^ 2 = algebraMap F L (α * β * γ))
    (hr : ∀ σ : F →+* ℝ, ∃ x y z t : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - σ α * y ^ 2 - σ β * z ^ 2 + σ γ * t ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x y z t : v.adicCompletion F,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - algebraMap F _ α * y ^ 2 - algebraMap F _ β * z ^ 2 + algebraMap F _ γ * t ^ 2 = 0) :
    ∃ X Y : L, algebraMap F L β = X ^ 2 - algebraMap F L α * Y ^ 2 := by
  refine H L _ _ (by simpa using hα) (by simpa using hβ) (fun σ => ?_) (fun w => ?_)
  · obtain ⟨x, y, z, t, h0, h⟩ := hr (σ.comp (algebraMap F L))
    exact exists_norm_of_quaternary (s := σ s) (γ := σ (algebraMap F L γ)) (by simpa using hα)
      (by simpa using hβ) (by simpa using hγ) (by rw [← map_pow, hs]; simp) h0 h
  · haveI : CharZero (w.adicCompletion L) :=
      charZero_of_injective_algebraMap (algebraMap L (w.adicCompletion L)).injective
    obtain ⟨v, φ, hφ⟩ := exists_ringHom_adicCompletion F L w
    obtain ⟨x, y, z, t, h0, h⟩ := hf v
    refine exists_norm_of_quaternary (s := algebraMap L _ s)
      (γ := algebraMap L _ (algebraMap F L γ)) (x := φ x) (y := φ y) (z := φ z) (t := φ t)
      (by simpa using hα) (by simpa using hβ) (by simpa using hγ)
      (by rw [← map_pow, hs]; simp only [map_mul]) (by simpa using h0) ?_
    have := congrArg φ h
    simpa only [map_add, map_sub, map_mul, map_pow, hφ, map_zero] using this

theorem isotropic_four (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin 4 → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : Fin 4 → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  rw [isotropic_four_iff (ha 0)]
  have hα : -(a 0 * a 1) ≠ 0 := by simp [ha]
  have hβ : -(a 0 * a 2) ≠ 0 := by simp [ha]
  have hγ : a 0 * a 3 ≠ 0 := by simp [ha]
  have hr' := fun σ : F →+* ℝ =>
    (isotropic_four_iff (a := fun i => σ (a i)) (by simpa using ha 0)).1 (hr σ)
  have hf' := fun v : HeightOneSpectrum (𝓞 F) =>
    (isotropic_four_iff (a := fun i => algebraMap F (v.adicCompletion F) (a i))
      (by simpa using ha 0)).1 (hf v)
  simp only [← map_mul, ← map_neg] at hr' hf'
  generalize -(a 0 * a 1) = α at *
  generalize -(a 0 * a 2) = β at *
  generalize a 0 * a 3 = γ at *
  by_cases hs : IsSquare (α * β * γ)
  · obtain ⟨s, hs⟩ := hs
    obtain ⟨X, Y, h⟩ := exists_norm_over_extension H F F hα hβ hγ (s := s)
      (by rw [hs, sq]; rfl) hr' hf'
    refine ⟨X, Y, 1, 0, by simp, ?_⟩
    change β = X ^ 2 - α * Y ^ 2 at h
    linear_combination -h
  · have : Fact (∀ r : F, r ^ 2 ≠ α * β * γ + 0 * r) :=
      ⟨fun r h => hs ⟨r, by linear_combination -h⟩⟩
    let L := QuadraticAlgebra F (α * β * γ) 0
    have : NumberField L := NumberField.of_module_finite F L
    obtain ⟨X, Y, h⟩ := exists_norm_over_extension H F L hα hβ hγ (s := ⟨0, 1⟩)
      (by ext <;> simp [sq, L]) hr' hf'
    have h1 := congrArg QuadraticAlgebra.re h
    have h2 := congrArg QuadraticAlgebra.im h
    simp [sq, L] at h1 h2
    refine exists_quaternary_of_coordinates hα hβ (X₀ := X.re) (X₁ := X.im) (Y₀ := Y.re)
      (Y₁ := Y.im) (by linear_combination h1) ?_
    linear_combination (-1 / 2 : F) * h2

end GlobalTheory.LocalQuad

namespace GlobalTheory.LocalQuad

theorem exists_value_isSquare_div (F : Type) [Field F] [NumberField F] {a a' : F} (ha : a ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (p q : (v : T) → v.1.adicCompletion F)
    (hpq : ∀ v, algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2 ≠ 0)
    (p' q' : (F →+* ℝ) → ℝ) (hpq' : ∀ σ, σ a * p' σ ^ 2 + σ a' * q' σ ^ 2 ≠ 0) :
    ∃ x y : F, a * x ^ 2 + a' * y ^ 2 ≠ 0 ∧
      (∀ v : T, IsSquare (algebraMap F (v.1.adicCompletion F) (a * x ^ 2 + a' * y ^ 2) /
        (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2))) ∧
      ∀ σ : F →+* ℝ, IsSquare (σ (a * x ^ 2 + a' * y ^ 2) / (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2)) := by
  have hd := (denseRange_finite_real F T).prodMap (denseRange_finite_real F T)
  have h4 : ∀ v : T, Valued.v (4 : v.1.adicCompletion F) ≠ 0 := by
    intro v
    haveI : CharZero (v.1.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.1.adicCompletion F)).injective
    simp
  have h41 : ∀ v : T, Valued.v (4 : v.1.adicCompletion F) ≤ 1 := by
    intro v
    have h2 : Valued.v (1 + 1 : v.1.adicCompletion F) ≤ 1 :=
      Valuation.map_add_le _ (by simp) (by simp)
    rw [show (4 : v.1.adicCompletion F) = (1 + 1) * (1 + 1) by norm_num, map_mul]
    exact mul_le_one' h2 h2
  let U : Set ((((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) ×
      (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ))) := (⋂ v : T, {z | Valued.v ((algebraMap F _ a * z.1.1 v ^ 2 +
      algebraMap F _ a' * z.2.1 v ^ 2) / (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1)
        < Valued.v (4 : v.1.adicCompletion F)}) ∩
    ⋂ σ : F →+* ℝ, {z | 0 < (σ a * z.1.2 σ ^ 2 + σ a' * z.2.2 σ ^ 2) /
      (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2)}
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun v => ?_) (isOpen_iInter_of_finite fun σ => ?_)
    · have ho : IsOpen {u : v.1.adicCompletion F | Valued.v u < Valued.v (4 : v.1.adicCompletion F)} := by
        have := Valued.isOpen_ball (v.1.adicCompletion F) (Valued.v.restrict (4 : v.1.adicCompletion F))
        simpa only [Valuation.restrict_lt_iff] using this
      exact ho.preimage (f := fun z : (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) ×
      (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) => (algebraMap F _ a * z.1.1 v ^ 2 +
        algebraMap F _ a' * z.2.1 v ^ 2) /
          (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1) (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  obtain ⟨⟨x, y⟩, hT, hR⟩ := hd.exists_mem_open hU ⟨((p, p'), (q, q')), by
    refine ⟨Set.mem_iInter.2 fun v => ?_, Set.mem_iInter.2 fun σ => ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [div_self (hpq v), sub_self, map_zero]
      exact zero_lt_iff.2 (h4 v)
    · simp only [Set.mem_setOf_eq]
      rw [div_self (hpq' σ)]
      exact one_pos⟩
  replace hT : ∀ v : T, Valued.v (algebraMap F (v.1.adicCompletion F) (a * x ^ 2 + a' * y ^ 2) /
      (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1) <
        Valued.v (4 : v.1.adicCompletion F) := by
    intro v
    simp only [map_add, map_mul, map_pow]
    exact Set.mem_iInter.1 hT v
  replace hR : ∀ σ : F →+* ℝ,
      0 < σ (a * x ^ 2 + a' * y ^ 2) / (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2) := by
    intro σ
    simp only [map_add, map_mul, map_pow]
    exact Set.mem_iInter.1 hR σ
  by_cases h0 : a * x ^ 2 + a' * y ^ 2 = 0
  · refine ⟨1, 0, by simpa using ha, fun v => ?_, fun σ => ?_⟩
    · have := (hT v).trans_le (h41 v)
      simp [h0] at this
    · have := hR σ
      simp [h0] at this
  · exact ⟨x, y, h0, fun v => isSquare_of_valued_sub_one_lt F v _ (hT v),
      fun σ => Real.isSquare_iff.2 (hR σ).le⟩

theorem finite_setOf_valued_ne_one (F : Type) [Field F] [NumberField F] {c : F} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) |
      Valued.v (algebraMap F (v.adicCompletion F) c) ≠ 1}.Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hc).preimage
    (f := FinitePlace.equivHeightOneSpectrum.symm)
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
  refine h.subset fun v hv => ?_
  simp only [Set.mem_preimage, Function.mem_mulSupport,
    FinitePlace.equivHeightOneSpectrum_symm_apply]
  intro h1
  exact hv (le_antisymm (Valued.toNormedField.norm_le_one_iff.1 h1.le)
    (Valued.toNormedField.one_le_norm_iff.1 h1.ge))

theorem isotropic_add_four (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F] (n : ℕ)
    (a : Fin (n + 4) → F) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : Fin (n + 4) → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin (n + 4) → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : Fin (n + 4) → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  induction n with
  | zero => exact isotropic_four H F a ha hr hf
  | succ n ih =>
    classical
    have split : ∀ (k : Type) [Field k] (φ : F →+* k),
        (∃ x : Fin (n + 1 + 4) → k, x ≠ 0 ∧ ∑ i, φ (a i) * x i ^ 2 = 0) →
        ∃ x y : k, φ (a 0) * x ^ 2 + φ (a 1) * y ^ 2 ≠ 0 ∧
          ∀ μ : F, IsSquare (φ μ / (φ (a 0) * x ^ 2 + φ (a 1) * y ^ 2)) →
          ∃ x : Fin (n + 4) → k, x ≠ 0 ∧
            ∑ i, φ ((Fin.cons μ fun j : Fin (n + 3) => a j.succ.succ : Fin (n + 4) → F) i) * x i ^ 2
              = 0 := by
      rintro k _ φ ⟨x, hx, h⟩
      haveI : CharZero k := (RingHom.charZero_iff φ.injective).1 inferInstance
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
      obtain ⟨X, Y, hXY, H⟩ := exists_value_isotropic (a := φ (a 0)) (a' := φ (a 1))
        (b := fun j : Fin (n + 2 + 1) => φ (a j.succ.succ)) (by simpa using ha 0)
        (by simpa using ha 1) (by simpa using ha _) (x := x 0) (y := x 1)
        (z := fun j => x j.succ.succ) (by
          by_contra hc
          push Not at hc
          apply hx
          funext i
          refine Fin.cases hc.1 (fun j => Fin.cases hc.2.1 (fun l => congrFun hc.2.2 l) j) i) h
      refine ⟨X, Y, hXY, fun μ hμ => ?_⟩
      refine (isotropic_succ_iff (n := n + 3)).2 ?_
      simpa using H _ hμ
    let e : Fin 3 → Fin (n + 3) := Fin.natAdd n
    have hT := (finite_setOf_valued_ne_one F (two_ne_zero (α := F))).union
      (Set.finite_iUnion fun i : Fin 3 => finite_setOf_valued_ne_one F (ha (e i).succ.succ))
    choose p q hpq hp using fun v : hT.toFinset => split _ _ (hf v.1)
    choose p' q' hpq' hp' using fun σ : F →+* ℝ => split _ _ (hr σ)
    obtain ⟨x, y, h0, h1, h2⟩ := exists_value_isSquare_div F (a' := a 1) (ha 0) _ p q hpq p' q' hpq'
    obtain ⟨t, z, hz0, hz⟩ := (isotropic_succ_iff (n := n + 3)).1 (ih
      (Fin.cons (a 0 * x ^ 2 + a 1 * y ^ 2) fun j : Fin (n + 3) => a j.succ.succ)
      (fun i => Fin.cases h0 (fun j => ha _) i) (fun σ => hp' σ _ (h2 σ)) (fun v => by
        by_cases hv : v ∈ hT.toFinset
        · exact hp ⟨v, hv⟩ _ (h1 ⟨v, hv⟩)
        · simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion,
            not_or, not_exists, not_not] at hv
          refine isotropic_of_injective (fun i => (e i).succ)
            ((Fin.succ_injective _).comp (Fin.natAdd_injective _ _)) ?_
          exact isotropic_ternary_of_units F v (by simpa only [map_ofNat] using hv.1) _ hv.2))
    simp only [Fin.cons_zero, Fin.cons_succ] at hz
    refine (isotropic_succ_iff (n := n + 4)).2 ⟨x * t, Fin.cons (y * t) z, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      obtain ⟨hx, hy⟩ := hc
      have hy0 : y * t = 0 := by simpa using congrFun hy 0
      rcases hz0 with ht | hz0
      · rw [mul_eq_zero_iff_right ht] at hx hy0
        simp [hx, hy0] at h0
      · exact hz0 (funext fun i => by simpa using congrFun hy i.succ)
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
      linear_combination hz

theorem isotropic_of_locally_isotropic (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F]
    [NumberField F] {ι : Type*} [Fintype ι] (hι : 4 ≤ Fintype.card ι) (a : ι → F)
    (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hι
  let e : ι ≃ Fin (n + 4) := Fintype.equivFinOfCardEq hn
  refine isotropic_of_injective e.symm e.symm.injective
    (isotropic_add_four H F n _ (fun i => ha _) (fun σ => ?_) (fun v => ?_))
  · exact isotropic_of_injective e e.injective (by simpa using hr σ)
  · exact isotropic_of_injective e e.injective (by simpa only [e.symm_apply_apply] using hf v)

theorem isotropic_of_indefinite (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    {ι : Type*} [Fintype ι] (a : ι → F) (hι : 5 ≤ Fintype.card ι) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) :
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 :=
  isotropic_of_locally_isotropic H F (by omega) a ha
    (fun σ => by
      obtain ⟨i, j, hi, hj⟩ := hr σ
      exact isotropic_real (a := fun i => σ (a i)) hi hj)
    (fun v => isotropic_adicCompletion_of_five_le F v hι _)

theorem landherr_of_hasseNormSt (H : GlobalTheory.Published.HasseNormSt) : GlobalTheory.Published.Landherr :=
  landherr_of_isotropy fun F _ _ _ _ a hι ha hr => isotropic_of_indefinite H F a hι ha hr

universe u v w in

theorem trace_forms_and_landherr :
    (∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E], (2 : E) ≠ 0 →
      ∀ c : E →+* E, (∀ t, c (c t) = t) → (∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) →
      ∀ {n : Type w} [Fintype n] [DecidableEq n] {G G' : Matrix n n E},
      (∀ a b, c (G a b) = G b a) → (∀ a b, c (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
      ((∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c) ↔
        ∃ φ : (n → E) ≃ₗ[F] (n → E),
          ∀ x, x ⬝ᵥ G' *ᵥ (c ∘ x) = φ x ⬝ᵥ G *ᵥ (c ∘ φ x))) ∧
    (GlobalTheory.Published.HasseNormSt → ∀ (F : Type) [Field F] [NumberField F] {ι : Type w} [Fintype ι],
      4 ≤ Fintype.card ι → ∀ a : ι → F, (∀ i, a i ≠ 0) →
      (∀ σ : F →+* ℝ, ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0) →
      (∀ v : HeightOneSpectrum (𝓞 F), ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧
        ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) →
      ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ∧
    (GlobalTheory.Published.HasseNormSt → GlobalTheory.Published.Landherr) :=
  ⟨fun h2 c hc hF _ _ _ _ _ hG hG' hd hd' =>
      exists_congr_iff_trace_forms_isometric h2 c hc hF hG hG' hd hd',
    fun H F _ _ _ _ hι a ha hr hf => isotropic_of_locally_isotropic H F hι a ha hr hf,
    landherr_of_hasseNormSt⟩

end GlobalTheory.LocalQuad
end
