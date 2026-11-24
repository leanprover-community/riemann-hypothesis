module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem kummer_root_mem : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 0 < m → ∀ (f : X.Kˣ) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → ∃ g : X.Kˣ, f = g ^ m := by
  intro Ω _ _ _ ε X _ _ m hm f a b M hM ha hb hb0 hfab hinv
  have hHs_open : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hHs_conn : IsPreconnected Hs :=
    (convex_halfSpace_gt Complex.imLm.isLinear (0 : ℝ)).isPreconnected
  have hbne : ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
    rcases (hb.analyticOnNhd hHs_open).eqOn_zero_or_eventually_ne_zero_of_preconnected hHs_conn with h | h
    · exfalso; apply hb0
      exact Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) (fun z hz => h hz))
    · exact h
  have hrep : ∀ x : Mero, ∃ φ : ℂ → ℂ, x = (φ : Mero) := fun x =>
    Filter.Germ.inductionOn x (fun φ => ⟨φ, rfl⟩)
  obtain ⟨φ, hφ⟩ := hrep (X.an (f : X.K))
  rw [hφ, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul] at hfab
  have h1 : ∀ᶠ z in Filter.codiscreteWithin Hs, φ z * b z ^ m = a z ^ m :=
    (Filter.Germ.coe_eq.1 hfab).mono fun z hz => by simpa using hz
  have h2 : ∀ᶠ z in Filter.codiscreteWithin Hs, (a z / b z) ^ m = φ z := by
    filter_upwards [h1, hbne] with z hz hbz
    rw [div_pow, div_eq_iff (pow_ne_zero _ hbz), hz]
  have hpoly : ∃ P : Polynomial X.K, P ≠ 0 ∧ P.eval₂ X.an (((a / b : ℂ → ℂ)) : Mero) = 0 := by
    refine ⟨Polynomial.X ^ m - Polynomial.C (f : X.K), Polynomial.X_pow_sub_C_ne_zero hm _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hφ, ← Filter.Germ.coe_pow, sub_eq_zero]
    exact Filter.Germ.coe_eq.2 (h2.mono fun z hz => by simpa using hz)
  obtain ⟨g0, hg0⟩ := X.sat a b M hM ha hb hb0 hinv hpoly
  obtain ⟨ψ, hψ⟩ := hrep (X.an g0)
  rw [hψ, ← Filter.Germ.coe_mul] at hg0
  have h3 : ∀ᶠ z in Filter.codiscreteWithin Hs, ψ z * b z = a z :=
    (Filter.Germ.coe_eq.1 hg0).mono fun z hz => by simpa using hz
  haveI : Nontrivial Mero := ⟨⟨_, _, hb0⟩⟩
  have hpow : g0 ^ m = (f : X.K) := by
    apply X.an.injective
    rw [map_pow, hψ, hφ, ← Filter.Germ.coe_pow]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [h2, h3, hbne] with z hz2 hz3 hbz
    have : ψ z = a z / b z := by rw [eq_div_iff hbz, hz3]
    simp only [Pi.pow_apply]
    rw [this, hz2]
  have hg0ne : g0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hpow
    exact f.ne_zero hpow.symm
  refine ⟨Units.mk0 g0 hg0ne, ?_⟩
  ext
  simp [hpow]

end GlobalTheory.KZ
