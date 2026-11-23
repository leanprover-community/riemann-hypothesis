module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfC

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix
open scoped Matrix ComplexOrder ENNReal

noncomputable section

theorem SumBoundStatement_holds : SumBoundStatement := by
  intro f p q s hs Γ hd hU
  obtain ⟨c, hc, hsepΓ⟩ := sumBd_sep Γ hd hU
  obtain ⟨C, hC, hbound⟩ := sumBd_sum (p := p) (q := q) (f := f) hs hc
  refine ⟨C, hC, fun v hv => ?_⟩
  choose G hG hGw using fun k => sumBd_frame (hv k)
  let x : Γ → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fun γ k =>
    ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * G k
  have hxU : ∀ a k, IsUpq (x a k) := fun a k => sumBd_isUpq_mul (hU a.1 a.2 k) (hG k)
  have hxsep : ∀ a b : Γ, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
    intro a b hab
    have hmem : b.1 * a.1⁻¹ ∈ Γ := Γ.mul_mem b.2 (Γ.inv_mem a.2)
    have hne : b.1 * a.1⁻¹ ≠ 1 := fun h => hab (Subtype.ext (mul_inv_eq_one.mp h).symm)
    obtain ⟨k, i, j, hk⟩ := hsepΓ _ hmem hne
    refine ⟨k, i, j, le_of_le_of_eq hk ?_⟩
    have : x b k * (x a k)⁻¹ = (((b.1 * a.1⁻¹) k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
      simp only [x, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv]
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (G k), sumBd_mul_inv (hG k), Matrix.one_mul]
    rw [this]
  calc ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s)
      = ∑' γ : Γ, ENNReal.ofReal (∏ k, (Complex.normSq (det (x γ k).toBlocks₂₂))⁻¹ ^ s) := by
        congr 1; funext γ
        rw [Finset.prod_congr rfl fun k _ => hGw k _ (hU γ.1 γ.2 k) s]
    _ ≤ C := hbound Γ x hxU hxsep

end
end ReciprocityTheory.ChartRestriction.G.AR.Up
