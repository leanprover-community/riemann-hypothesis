module

public import ReciprocityTheory.Automorphisms.Unitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct

namespace GlobalTheory.SplitComp

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

theorem exists_imag : ∃ θ : L, θ ≠ 0 ∧ IsCMField.complexConj L θ = -θ := by
  have h := IsCMField.complexConj_ne_one L
  obtain ⟨x, hx⟩ : ∃ x : L, IsCMField.complexConj L x ≠ x := by
    by_contra hc
    push Not at hc
    exact h (AlgEquiv.ext hc)
  refine ⟨x - IsCMField.complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, IsCMField.complexConj_apply_apply]; ring

theorem exists_real_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (x : L) :
    ∃ a b : maximalRealSubfield L, x = a • (1 : L) + b • θ := by
  have h2 : IsCMField.complexConj L (2 : L) = 2 := map_ofNat _ 2
  have ha : (x + IsCMField.complexConj L x) / 2 ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, h2]
    ring
  have hb : (x - IsCMField.complexConj L x) / (2 * θ) ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul,
      IsCMField.complexConj_apply_apply, h2, hθ]
    field_simp
    ring
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
  change x = (x + IsCMField.complexConj L x) / 2 * 1 + (x - IsCMField.complexConj L x) / (2 * θ) * θ
  field_simp
  ring

theorem exists_tmul_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (z : AL L) :
    ∃ a b : AFplus L, z = (1 : L) ⊗ₜ[maximalRealSubfield L] a + θ ⊗ₜ[maximalRealSubfield L] b := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x c =>
    obtain ⟨a, b, rfl⟩ := exists_real_add L θ h0 hθ x
    exact ⟨a • c, b • c, by rw [add_tmul, smul_tmul, smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [tmul_add, tmul_add]; abel⟩

theorem compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L),
    s.proj z = 0 → s.proj (conjAL L z) = 0 → compAt L s.v z = 0 := by
  intro L _ _ _ s z h1 h2
  obtain ⟨θ, h0, hθ⟩ := exists_imag L
  obtain ⟨a, b, rfl⟩ := exists_tmul_add L θ h0 hθ z
  have e1 : evalAt L s.v a + s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj] using h1
  have e2 : evalAt L s.v a - s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj, conjAL, hθ, neg_tmul, sub_eq_add_neg] using h2
  have hi : s.i θ ≠ 0 := (map_ne_zero s.i).mpr h0
  have : CharZero (s.v.adicCompletion (maximalRealSubfield L)) :=
    algebraRat.charZero _
  have ha : evalAt L s.v a = 0 := by linear_combination (e1 + e2) / 2
  have hb : evalAt L s.v b = 0 := by
    rw [ha, zero_add] at e1
    exact (mul_eq_zero.mp e1).resolve_left hi
  simp [compAt, ha, hb]

end GlobalTheory.SplitComp
