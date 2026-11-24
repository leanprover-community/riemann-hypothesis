module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

theorem UpperTheory.trace_eq_sum_re_cm_type :
    ∀ {E : Type} [Field E] [NumberField E] {Ψ : Type} [Fintype Ψ] (φ : Ψ → (E →+* ℂ)),
        Function.Injective φ →
        (∀ s : E →+* ℂ, (∃ τ, φ τ = s) ↔ ¬ ∃ τ, φ τ = (starRingEnd ℂ).comp s) →
        ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ, 2 * (φ τ x).re := by
  intro E _ _ Ψ _ φ hinj h x
  classical
  have hcc : ∀ s : E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
    intro s
    ext y
    simp
  let g : Ψ ⊕ Ψ → (E →+* ℂ) := Sum.elim φ (fun τ => (starRingEnd ℂ).comp (φ τ))
  have hg : Function.Bijective g := by
    constructor
    · rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (hinj hab)
      · exact absurd ⟨a, hab⟩ ((h (φ b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, hab.symm⟩ ((h (φ a)).1 ⟨a, rfl⟩)
      · have h2 := congrArg (fun s => (starRingEnd ℂ).comp s) hab
        simp only [g, Sum.elim_inr, hcc] at h2
        exact congrArg Sum.inr (hinj h2)
    · intro s
      by_cases hs : ∃ τ, φ τ = s
      · obtain ⟨τ, hτ⟩ := hs
        exact ⟨Sum.inl τ, hτ⟩
      · obtain ⟨τ, hτ⟩ := not_not.1 (fun hn => hs ((h s).2 hn))
        refine ⟨Sum.inr τ, ?_⟩
        simp only [g, Sum.elim_inr, hτ, hcc]
  have h1 : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ s : E →+* ℂ, s x := by
    have h0 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := x)
    rw [eq_ratCast] at h0
    rw [h0]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun s => rfl)).symm
  rw [← Fintype.sum_bijective g hg (fun t => g t x) (fun s => s x) (fun _ => rfl),
    Fintype.sum_sum_type, ← Finset.sum_add_distrib] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.ratCast_re, Complex.re_sum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [g, two_mul]
