module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob.Inhab

variable {E : Type} [Field E] [NumberField E]

abbrev Int' (E : Type) [Field E] : Subring E := (algebraMap (𝓞 E) E).range

omit [NumberField E] in
theorem mem_int_iff (x : E) : x ∈ Int' E ↔ IsIntegral ℤ x :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

omit [NumberField E] in
theorem map_mem_int (σ : E →+* E) {x : E} (h : x ∈ Int' E) : σ x ∈ Int' E := by
  rw [mem_int_iff] at h ⊢
  exact h.map σ.toIntAlgHom

omit [NumberField E] in
theorem smul_eq (c : 𝓞 E) (x : E) : c • x = algebraMap (𝓞 E) E c * x := Algebra.smul_def c x

theorem mem_dInv_zero (x : E) : x ∈ dInv E 0 ↔ x ∈ Int' E := by
  simp only [dInv, pow_zero, FractionalIdeal.mem_one_iff]
  rfl

def std (E : Type) [Field E] : Submodule (𝓞 E) (Fin 2 → E) :=
  Submodule.span (𝓞 E) {![0, 1], ![1, 1]}

omit [NumberField E] in
theorem mem_std (v : Fin 2 → E) : v ∈ std E ↔ v 0 ∈ Int' E ∧ v 1 ∈ Int' E := by
  rw [std, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    constructor
    · exact ⟨b, by simp [smul_eq]⟩
    · exact ⟨a + b, by simp [smul_eq]⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨b - a, a, ?_⟩
    ext i
    fin_cases i <;> simp [smul_eq, ← ha, ← hb]

omit [NumberField E] in
theorem form_two (σ : E →+* E) (v w : Fin 2 → E) :
    form σ !![1, 0; 0, -1] v w = σ (w 0) * v 0 - σ (w 1) * v 1 := by
  simp [form, dotProduct, Matrix.mulVec, Fin.sum_univ_two, sub_eq_add_neg]

theorem selfDual_std (σ : E →+* E) : SelfDual σ !![1, 0; 0, -1] (std E) := by
  refine ⟨Submodule.fg_span (Set.toFinite _), fun v => ⟨fun hv w hw => ?_, fun h => ?_⟩⟩
  · rw [mem_std] at hv hw
    rw [form_two]
    exact sub_mem (mul_mem (map_mem_int σ hw.1) hv.1) (mul_mem (map_mem_int σ hw.2) hv.2)
  · have h0 := h ![1, 0] ((mem_std _).2 ⟨one_mem _, zero_mem _⟩)
    have h1 := h ![0, -1] ((mem_std _).2 ⟨zero_mem _, neg_mem (one_mem _)⟩)
    rw [form_two] at h0 h1
    exact (mem_std v).2 ⟨by simpa using h0, by simpa using h1⟩

theorem frameLat_zero {n : ℕ} (P : Matrix (Fin n) (Fin (0 + 1)) E) :
    frameLat P = Submodule.span (𝓞 E) {fun i => P i 0} := by
  apply le_antisymm
  · rw [frameLat, Submodule.span_le]
    rintro v ⟨b, a, ha, rfl⟩
    obtain rfl : b = 0 := Subsingleton.elim (α := Fin 1) _ _
    obtain ⟨c, rfl⟩ := (mem_dInv_zero a).1 ha
    exact Submodule.mem_span_singleton.2 ⟨c, by ext i; simp [smul_eq]⟩
  · rw [Submodule.span_le]
    rintro v rfl
    exact Submodule.subset_span ⟨0, 1, (mem_dInv_zero 1).2 (one_mem _), by simp⟩

theorem pairLat_std {g : ℕ} (hg : g ≠ 0) :
    pairLat (r := 0) g (!![0; 1] : Matrix (Fin 2) (Fin (0 + 1)) E) !![(g : E); 1 + g] = std E := by
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  rw [pairLat, frameLat_zero, frameLat_zero, std, Submodule.span_insert]
  congr 3
  · ext i; fin_cases i <;> simp
  · ext i; fin_cases i <;> simp [hg']

theorem mem_genConf_zero (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    ((std E, !![0; 1], !![(g : E); 1 + g]) : Tri E 2 0) ∈
      GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] := by
  refine ⟨selfDual_std σ, ⟨⟨⟨!![0, 1], ?_⟩, ?_⟩, ⟨⟨!![-1, 1], ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, TF, Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, TF, Matrix.mul_apply]; ring
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, Matrix.mul_apply]; ring
  · dsimp only
    rw [pairLat_std hg]
    exact ⟨le_rfl, fun v hv _ => hv⟩

omit [NumberField E] in
theorem gq_zero (σ : E →+* E) (g : ℕ) :
    Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] = (g : E) ^ 2 := by
  simp [Gq, lead]
  ring

end GlobalTheory.SgGlob.Inhab
