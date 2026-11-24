module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem card_hermitian_dvd_sq {A : Type} [CommRing A] [Finite A] (c : A →+* A)
    (hc : ∀ u, c (c u) = u) (ω : A) (hω : IsUnit (ω - c ω)) (p : A) (hp : c p = p) (m : ℕ) :
    Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2
      = Nat.card {u : A // p ∣ u} ^ (m * m) := by
  have hmem : ∀ u : A, u ∈ Ideal.span {p} → c u ∈ Ideal.span {p} := by
    intro u hu
    rw [Ideal.mem_span_singleton] at hu ⊢
    have := map_dvd c hu
    rwa [hp] at this
  let σ : (Fin m → Fin m → Ideal.span {p}) →+ (Fin m → Fin m → Ideal.span {p}) :=
    { toFun := fun H a b => ⟨c (H b a).1, hmem _ (H b a).2⟩
      map_zero' := by
        funext a b
        exact Subtype.ext (by simp)
      map_add' := fun H K => by
        funext a b
        exact Subtype.ext (by simp) }
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    funext a b
    exact Subtype.ext (hc _)
  have hs : ∀ (r : A) x, σ (r • x) = c r • σ x := fun r x => by
    funext a b
    exact Subtype.ext (map_mul c r _)
  have h := (card_fixed_sq c hc hω σ hσ hs).1
  let e : {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ≃
      {x : Fin m → Fin m → Ideal.span {p} // σ x = x} :=
    { toFun := fun H => ⟨fun a b => ⟨H.1 a b, Ideal.mem_span_singleton.2 (H.2.2 a b)⟩, by
        funext a b
        exact Subtype.ext (H.2.1 a b)⟩
      invFun := fun x => ⟨fun a b => (x.1 a b).1,
        fun a b => congrArg Subtype.val (congrFun (congrFun x.2 a) b),
        fun a b => Ideal.mem_span_singleton.1 (x.1 a b).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : {u : A // p ∣ u} ≃ Ideal.span {p} :=
    Equiv.subtypeEquivRight fun u => Ideal.mem_span_singleton.symm
  rw [Nat.card_congr e, h, Nat.card_congr e2, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp

end GlobalTheory.GramCount
