module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFHS
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  rw [mem_perp, hs.sub_right, hs.smul_right, mul_right_comm, inv_mul_cancel₀ he, one_mul, sub_self]

theorem card_decomp {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  classical
  let T : V → K := fun x => (h e e)⁻¹ * h e x
  have hTe : ∀ (t : K) (w : perp hs e), T ((t • e) + (w : V)) = t := by
    intro t w
    simp only [T]
    rw [hs.add_right, hs.smul_right, (mem_perp hs e w).1 w.2, add_zero, ← mul_assoc,
      mul_comm ((h e e)⁻¹) t, mul_assoc, inv_mul_cancel₀ he, mul_one]
  let eqv : {x : V // h x x = c} ≃ Σ t : K, {w : perp hs e // h w w = c - σ t * t * h e e} :=
    { toFun := fun x => ⟨T x.1, ⟨⟨x.1 - T x.1 • e, perp_sub_mem hs e x.1 he⟩, by
        have h1 := decomp_val hs e (x.1 - T x.1 • e)
          ((mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)) (T x.1)
        have hx : T x.1 • e + (x.1 - T x.1 • e) = x.1 := by abel
        rw [hx, x.2] at h1
        show h (x.1 - T x.1 • e) (x.1 - T x.1 • e) = c - σ (T x.1) * T x.1 * h e e
        rw [eq_sub_iff_add_eq, add_comm]
        exact h1.symm⟩⟩
      invFun := fun p => ⟨p.1 • e + (p.2.1 : V), by
        rw [decomp_val hs e p.2.1 ((mem_perp hs e _).1 p.2.1.2) p.1]
        have h2 : h (p.2.1 : V) (p.2.1 : V) = c - σ p.1 * p.1 * h e e := p.2.2
        rw [h2]
        ring⟩
      left_inv := fun x => Subtype.ext (by
        show T x.1 • e + (x.1 - T x.1 • e) = x.1
        abel)
      right_inv := fun p => by
        refine Sigma.subtype_ext (hTe p.1 p.2.1) (Subtype.ext ?_)
        show p.1 • e + (p.2.1 : V) - T (p.1 • e + (p.2.1 : V)) • e = (p.2.1 : V)
        rw [hTe]
        abel }
  rw [Nat.card_congr eqv, Nat.card_sigma]

end PI.VolStabSW.FFHS
