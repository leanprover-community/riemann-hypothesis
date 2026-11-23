module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCF

theorem fold_replicate_cap {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (c : Module.End ℂ (Sm E a)) (χ : Module.End ℂ (Sm E a) → ℂ) (φ : Sm E a) (n : ℕ) :
    (List.replicate n c).foldr (fun z f => z f - χ z • f) φ = ((c - algebraMap ℂ _ (χ c)) ^ n) φ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]

theorem rt_translate_kill : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (S : Finset (Module.End ℂ (Sm E a) → ℂ)), X ⊆ ↑S → ∀ (N : ℕ), ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), (∀ γ g, (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 (ratGL E a γ * g) = (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 g) ∧ IsOpen {k | finRep E a k (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ} ∧ ∀ (τ : E →+* ℂ) (u : ℂ), Polynomial.aeval (cap τ u) (∏ χ ∈ S, (Polynomial.X - Polynomial.C (χ (cap τ u))) ^ N) (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = 0 := by
  intro E _ _ _ a L W X S hXS N φ hφ t κ
  obtain ⟨hA, -, -, χ₀, hχ₀, hnil⟩ := hφ
  set h := finGL E a t * infGL E a (Unitary.toUnits κ) with hh
  refine ⟨fun γ g => ?_, ?_, fun τ u => ?_⟩
  · rw [rt_apply, rt_apply, mul_assoc, hA.left]
  · refine isOpen_stab_of_mem_nhds (finRep E a) _ ?_
    have hc : Continuous fun k : GL (Fin a) (Af E) => t⁻¹ * k * t := by fun_prop
    have ho := hA.level.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds (by simp)) fun k hk => ?_
    have hk' : rt E a (finGL E a (t⁻¹ * k * t)) φ = φ := hk
    change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ
    have e : finGL E a k * h = h * finGL E a (t⁻¹ * k * t) := by
      rw [hh, mul_assoc (finGL E a t), infGL_comm, ← mul_assoc (finGL E a t), ← map_mul,
        show t * (t⁻¹ * k * t) = k * t by group, map_mul]
      simp only [mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']
  · classical
    have hcap : cap τ u ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, u, rfl⟩
    have hc : Commute (cap (a := a) τ u) (rt E a h) := by
      have h1 : Commute (cap τ u) (rt E a (finGL E a t)) := commute_cap_finRep (a := a) τ u t
      have h2 := GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u (Unitary.toUnits κ)
      rw [hh, map_mul]
      exact h1.mul_right h2
    have hP : ∀ p : Polynomial ℂ, Commute (Polynomial.aeval (cap (a := a) τ u) p) (rt E a h) := by
      intro p
      have hle : Algebra.adjoin ℂ {cap (a := a) τ u} ≤ Subalgebra.centralizer ℂ {rt E a h} := by
        refine Algebra.adjoin_le ?_
        rintro _ rfl
        rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact hc.eq.symm
      exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle (Polynomial.aeval_mem_adjoin_singleton ℂ _)) _ rfl).symm
    rw [← Module.End.mul_apply, (hP _).eq, Module.End.mul_apply]
    have h0 : Polynomial.aeval (cap (a := a) τ u) ((Polynomial.X - Polynomial.C (χ₀ (cap τ u))) ^ N) φ = 0 := by
      have := hnil (List.replicate N (cap τ u)) (List.length_replicate ..) fun z hz => by
        rw [List.eq_of_mem_replicate hz]; exact hcap
      rw [fold_replicate_cap] at this
      simpa [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] using this
    rw [← Finset.prod_erase_mul S _ (hXS hχ₀), Polynomial.aeval_mul, Module.End.mul_apply, h0]
    simp only [map_zero]

end GlobalTheory.HCF
