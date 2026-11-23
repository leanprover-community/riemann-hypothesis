module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
public import Mathlib.LinearAlgebra.Basis.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobFac

theorem T_fac : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {B : Type} [Field B] (ι : C₀ →+* B) (i : A →+* B), (∀ a, ι (c a) = i a) → ∀ (h : L →+ B), (∀ (w : W) y, h (w • y) = i (algebraMap W A w) * h y) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)), ∃ E : K₀ ⊗[W] L →+ B, (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) ∧ ∀ G : A ⊗[W] L →+ B, (∀ a y, G (a ⊗ₜ y) = i a * h y) → ∀ z, G z = ∑ s, ι (T c k hk (b.coord s) z) * E (b s) := by
  intro W A C₀ _ _ _ _ K₀ _ _ L _ _ c k hk B _ ι i hi h hh m b
  let E : K₀ ⊗[W] L →+ B := TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun y => ι (k x) * h y
          map_zero' := by simp
          map_add' := fun y y' => by simp [mul_add] }
      map_zero' := by
        ext y
        simp
      map_add' := fun x x' => by
        ext y
        simp [add_mul] }
    (fun r x y => by
      show ι (k (r • x)) * h y = ι (k x) * h (r • y)
      rw [hh, Algebra.smul_def, map_mul, hk, map_mul, hi]
      ring)
  have hE : ∀ x y, E (x ⊗ₜ y) = ι (k x) * h y := by
    intro x y
    first
    | rfl
    | simp [E, TensorProduct.liftAddHom_tmul]
  have hEs : ∀ (x : K₀) (t : K₀ ⊗[W] L), E (x • t) = ι (k x) * E t := by
    intro x t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y =>
      rw [TensorProduct.smul_tmul', hE, hE, smul_eq_mul, map_mul, map_mul, mul_assoc]
    | add t t' ht ht' =>
      rw [smul_add, map_add (f := _), map_add (f := _), ht, ht', mul_add]
  refine ⟨E, hE, fun G hG z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    have hsum : ∑ s, ι (T c k hk (b.coord s) (a ⊗ₜ y)) * E (b s) =
        ι (c a) * E ((1 : K₀) ⊗ₜ y) := by
      conv_rhs => rw [← b.sum_repr ((1 : K₀) ⊗ₜ y)]

      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      have hT : T c k hk (b.coord s) (a ⊗ₜ y) = c a * k (b.repr ((1 : K₀) ⊗ₜ y) s) := by
        first
        | rfl
        | simp [T, TensorProduct.liftAddHom_tmul, Module.Basis.coord_apply]
      rw [hEs, hT, map_mul, mul_assoc]
    rw [hG, hsum, hE, map_one, map_one, one_mul, hi]
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy, add_mul, Finset.sum_add_distrib]

end GlobalTheory.CompanionTheory.FrobFac
