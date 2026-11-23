module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValuesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImageStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataTowerUnionAdjoinStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

section Klc

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_eq_pow (T : Tower p Ω) (k j : ℕ) : zS T k = zS T (k + j) ^ (p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, pow_succ' p j, pow_mul]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact (T.ζpow (k + j)).symm

theorem qS_eq_pow (T : Tower p Ω) (k j : ℕ) : qS T k = qS T (k + j) ^ (p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, pow_succ' p j, pow_mul]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact (T.qpow (k + j)).symm

theorem D_zS_mem_span (T : Tower p Ω) {k m : ℕ} (h : k ≤ m) :
    KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T k) ∈
      Submodule.span (integralClosure (O0 p) Ω)
        {KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m),
          KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m)} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [zS_eq_pow T k j, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem D_qS_mem_span (T : Tower p Ω) {k m : ℕ} (h : k ≤ m) :
    KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T k) ∈
      Submodule.span (integralClosure (O0 p) Ω)
        {KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m),
          KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m)} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [qS_eq_pow T k j, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end Klc


theorem p_sq_smul_kaehler_mem_span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (η : KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω))
    (n : ℕ), ∃ m, n ≤ m ∧ ∃ x y : (integralClosure (O0 p) Ω), (p : (integralClosure (O0 p) Ω)) ^ 2 • η =
      x • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m) +
        y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m) := by
  intro p _ Ω _ _ hp2 hclo T η n
  let 𝒮 := integralClosure (O0 p) Ω
  let 𝒟 := KaehlerDifferential.D (O0 p) 𝒮
  let N : ℕ → Submodule 𝒮 (KaehlerDifferential (O0 p) 𝒮) :=
    fun m => Submodule.span 𝒮 {𝒟 (zS T m), 𝒟 (qS T m)}
  have hmono : Monotone N := fun k m h => Submodule.span_le.2 (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [D_zS_mem_span T h, D_qS_mem_span T h])
  have hder : ∀ B : Subalgebra (O0 p) 𝒮, IsDerOn B (fun x => 𝒟 x) := fun B =>
    ⟨fun x _ y _ => map_add 𝒟 x y, fun x _ y _ => Derivation.leibniz 𝒟 x y,
      fun a => (𝒟).map_algebraMap a⟩
  have hgen : ∀ t : 𝒮, (p : 𝒮) ^ 2 • 𝒟 t ∈ ⨆ m, N m := by
    intro t
    obtain ⟨C, tr, k, a, b, hF, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_towerUnionAdjoin p Ω hp2 hclo T {t}
    have h1 := GlobalTheory.T.almostDualTrace_derivation_mem_span_values (O0 p) 𝒮 _ (towerAlg T) C tr k a b _ htr (fun x => 𝒟 x) (hder C) t
      (hF (by simp))
    have h2 : Submodule.span 𝒮 ((fun x => 𝒟 x) '' (towerAlg T : Set 𝒮)) ≤ ⨆ m, N m := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h3 := GlobalTheory.T.derivationOn_adjoin_mem_span_image (O0 p) 𝒮 _ (Set.range (zS T) ∪ Set.range (qS T)) (fun x => 𝒟 x)
        (hder _) x hx
      refine Submodule.span_le.2 ?_ h3
      rintro _ ⟨y, (⟨k, rfl⟩ | ⟨k, rfl⟩), rfl⟩
      · exact Submodule.mem_iSup_of_mem k (Submodule.subset_span (by simp))
      · exact Submodule.mem_iSup_of_mem k (Submodule.subset_span (by simp))
    rw [pow_two]
    exact h2 h1
  have hall : ∀ ω ∈ Submodule.span 𝒮 (Set.range 𝒟), (p : 𝒮) ^ 2 • ω ∈ ⨆ m, N m := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hgen t
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have hη : (p : 𝒮) ^ 2 • η ∈ ⨆ m, N m :=
    hall η (by rw [KaehlerDifferential.span_range_derivation]; trivial)
  obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed N hmono.directed_le).1 hη
  refine ⟨max m n, le_max_right _ _, ?_⟩
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.1 (hmono (le_max_left m n) hm)
  exact ⟨x, y, hxy.symm⟩

end GlobalTheory.AlmostEt
