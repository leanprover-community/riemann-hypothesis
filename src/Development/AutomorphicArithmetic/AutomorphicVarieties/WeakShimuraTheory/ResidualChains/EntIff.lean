module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Chain.entIff :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k)
      (c : PD Φ.ι Γ k), Φ.IsRes a c →
      (Supp nP c.r → (Ent c.r (-wPs) ↔ ∃ g, c.r g 2 0 ≠ 0)) ∧ (Supp nM c.r → (Ent c.r (-wAl) ↔ ∃ g, c.r g 1 0 ≠ 0)) := by
  intro O Γ _ _ _ Φ k _ a c hc
  have hadj : ∀ g, adj (c.r g⁻¹) = a ↑(Φ.ν g⁻¹) • c.r g := by
    intro g
    have hm : adj (c.r g⁻¹) * c.r g⁻¹ = a ↑(Φ.ν g⁻¹) • 1 := hc.pair.mult g⁻¹
    calc adj (c.r g⁻¹) = adj (c.r g⁻¹) * (c.r g⁻¹ * c.r g) := by
          rw [← map_mul, inv_mul_cancel, map_one, mul_one]
      _ = a ↑(Φ.ν g⁻¹) • c.r g := by rw [← mul_assoc, hm, smul_mul_assoc, one_mul]
  have hν : ∀ g, a ↑(Φ.ν g) ≠ 0 := fun g => ((Φ.ν g).isUnit.map a).ne_zero
  have ent : ∀ {R : Type} [CommRing R] (X : M4 R), adj X 3 1 = - X 2 0 ∧ adj X 3 2 = X 1 0 := by
    intro R _ X
    simp [adj_apply, sgn]
  have e31 : ∀ g, c.r g 3 1 ≠ 0 → c.r g⁻¹ 2 0 ≠ 0 := by
    intro g hg h0
    have := (ent (c.r g⁻¹)).1
    rw [hadj, h0, neg_zero, Matrix.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero (hν _) hg this
  have e32 : ∀ g, c.r g 3 2 ≠ 0 → c.r g⁻¹ 1 0 ≠ 0 := by
    intro g hg h0
    have := (ent (c.r g⁻¹)).2
    rw [hadj, h0, Matrix.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero (hν _) hg this
  have wP : ∀ i j : Fin 4, wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wPs, Prod.ext_iff]
  have wA : ∀ i j : Fin 4, wt i j = -wAl → (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wAl, Prod.ext_iff]
  have w20 : wt 2 0 = -wPs := by simp [wt, lamW, muW, wPs]
  have w10 : wt 1 0 = -wAl := by simp [wt, lamW, muW, wAl]
  refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, ?_⟩⟩
  · rintro ⟨g, i, j, hw, hne⟩
    rcases wP i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨g, hne⟩
    · exact ⟨g⁻¹, e31 g hne⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, 2, 0, w20, hg⟩
  · rintro ⟨g, i, j, hw, hne⟩
    rcases wA i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨g, hne⟩
    · exact ⟨g⁻¹, e32 g hne⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, 1, 0, w10, hg⟩
