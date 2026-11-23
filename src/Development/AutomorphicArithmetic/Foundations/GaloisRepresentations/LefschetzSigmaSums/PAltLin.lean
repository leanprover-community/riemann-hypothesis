module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.HodgeCoh

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem trace_comb {M : Type*} [AddCommGroup M] [Module ℂ M] {m : ℕ} {A : Type*}
    (u : Fin m → Module.End ℂ M) (c : Fin m → ℂ) (w : A →₀ ℂ) (e : A → Module.End ℂ M) :
    LinearMap.trace ℂ M ((∑ i, c i • u i) ∘ₗ w.sum fun α r => r • e α) =
      ∑ i, c i * w.sum fun α r => r * LinearMap.trace ℂ M (u i ∘ₗ e α) := by

  simp only [Finsupp.sum, ← Module.End.mul_eq_comp, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
  mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => ?_
  ring

private theorem sum_rearrange {m : ℕ} {A : Type*} (R : Finset ℕ) (S : Finset A) (c : Fin m → ℂ) (w : A → ℂ)
    (x z : ℕ → ℂ) (t : Fin m → A → ℕ → ℕ → ℂ) :
    ∑ a ∈ R, x a * ∑ b ∈ R, z b * ∑ i, c i * ∑ α ∈ S, w α * t i α a b =
      ∑ i, c i * ∑ α ∈ S, w α * ∑ a ∈ R, x a * ∑ b ∈ R, z b * t i α a b := by
  simp only [Finset.mul_sum]
  calc _ = ∑ a ∈ R, ∑ i, ∑ b ∈ R, ∑ α ∈ S, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a ∈ R, ∑ b ∈ R, ∑ α ∈ S, x a * (z b * (c i * (w α * t i α a b))) := Finset.sum_comm
    _ = ∑ i, ∑ a ∈ R, ∑ α ∈ S, ∑ b ∈ R, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ α ∈ S, ∑ a ∈ R, ∑ b ∈ R, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring

private theorem alt_family {M : ℕ → ℕ → Type*} [∀ a b, AddCommGroup (M a b)] [∀ a b, Module ℂ (M a b)]
    (d m : ℕ) {A : Type*} (u : Fin m → ∀ a b : ℕ, Module.End ℂ (M a b)) (c : Fin m → ℂ) (w : A →₀ ℂ)
    (e : A → ∀ a b : ℕ, Module.End ℂ (M a b)) (y : ℂ) :
    ∑ a ∈ Finset.range (d + 1), (-y) ^ a * ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b *
        LinearMap.trace ℂ (M a b) ((∑ i, c i • u i a b) ∘ₗ w.sum fun α r => r • e α a b) =
      ∑ i, c i * w.sum fun α r => r * ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ (M a b) (u i a b ∘ₗ e α a b) := by
  simp only [trace_comb]
  simp only [Finsupp.sum]
  exact sum_rearrange (Finset.range (d + 1)) w.support c (fun α => w α) (fun a => (-y) ^ a) (fun b => (-1 : ℂ) ^ b)
    fun i α a b => LinearMap.trace ℂ (M a b) (u i a b ∘ₗ e α a b)

theorem altLin_of : AltLin := fun Z s d m A u c w e y =>
  alt_family (M := fun a b => hodgeH s a b) d m u c w e y

end UpperTheory.Gal.LocalSmoothExtension
