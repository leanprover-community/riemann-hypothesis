module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

universe u

namespace DiagPull

section Ring

variable {R : Type*} [CommRing R]

theorem mem_minimalPrimes_of_cross {V W : Ideal R} {f g u v : R} (hrel : f * v - g * u ∈ V)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hu : u ∉ W) (hv : v ∉ W) :
    W ∈ (V ⊔ Ideal.span {g}).minimalPrimes := by
  have hWp := hW.1.1
  have hVW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hgW : g ∈ W := by
    have h : g * u ∈ W := by
      have e : g * u = f * v - (f * v - g * u) := by ring
      rw [e]
      exact W.sub_mem (W.mul_mem_right v hfW) (hVW hrel)
    exact (hWp.mem_or_mem h).resolve_right hu
  refine ⟨⟨hWp, sup_le hVW ((Ideal.span_singleton_le_iff_mem _).mpr hgW)⟩, fun Q hQ hQW => ?_⟩
  have hVQ : V ≤ Q := le_sup_left.trans hQ.2
  have hgQ : g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hfQ : f ∈ Q := by
    have h : f * v ∈ Q := by
      have e : f * v = (f * v - g * u) + g * u := by ring
      rw [e]
      exact Q.add_mem (hVQ hrel) (Q.mul_mem_right u hgQ)
    exact (hQ.1.mem_or_mem h).resolve_right fun h' => hv (hQW h')
  exact hW.2 ⟨hQ.1, sup_le hVQ ((Ideal.span_singleton_le_iff_mem _).mpr hfQ)⟩ hQW

theorem locLen_cross {V : Ideal R} (hV : V.IsPrime) {f g u v : R} (hrel : f * v - g * u ∈ V)
    (p : PrimeSpectrum R) (hVp : V ≤ p.asIdeal) (hu : u ∉ p.asIdeal) (hv : v ∉ p.asIdeal) :
    locLen (R ⧸ (V ⊔ Ideal.span {f})) p = locLen (R ⧸ (V ⊔ Ideal.span {g})) p := by
  have e : V ⊔ Ideal.span {v * f} = V ⊔ Ideal.span {u * g} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e' : v * f = (f * v - g * u) + u * g := by ring
      rw [e']
      exact Ideal.add_mem _ (Ideal.mem_sup_left hrel)
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e' : u * g = v * f - (f * v - g * u) := by ring
      rw [e']
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_left hrel)
  have h1 := I1.locLen_mul hV (fun h => hv (hVp h)) f p
  have h2 := I1.locLen_mul hV (fun h => hu (hVp h)) g p
  rw [e, h2, I1.locLen_quot_eq_zero p hu, I1.locLen_quot_eq_zero p hv, add_zero, add_zero] at h1
  exact h1.symm

end Ring

section Homog

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

end Homog

section Models

variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
  (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)



end Models

end DiagPull

end

end GroundTheory.Heights₂.Heights.Inter
