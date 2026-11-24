module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k]

theorem thetaA_eq_of_unip (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (x : MirUin k n)
    (w : Multiplicative (Fin n → k))
    (hx : ((x : Mir k n) : GL (Fin (n + 1)) k) = unip k n w) :
    thetaA k ψ a x = Circle.toUnits (ψ (a ⬝ᵥ w.toAdd)) := by
  have key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hx
  show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x)).toAdd)) = _
  rw [key]

theorem thetaConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : ThetaConj k := by
  intro ψ n a m u
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  have e : glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ =
      unip k n (Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v.toAdd)) := by
    rw [hv', glEmb_mul_unip', mul_inv_cancel_right]
  have h : levi k n m * (u : Mir k n) * (levi k n m)⁻¹ ∈ MirUin k n := by
    show glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ ∈ MirU k n
    rw [e]
    exact ⟨_, rfl⟩
  refine ⟨h, ?_⟩
  rw [thetaA_eq_of_unip ψ _ u v hv', thetaA_eq_of_unip ψ a ⟨_, h⟩ _ e]
  simp only [toAdd_ofAdd]
  rw [dotProduct_mulVec]

end GlobalTheory.CompanionTheory.BZMirabolic

end
