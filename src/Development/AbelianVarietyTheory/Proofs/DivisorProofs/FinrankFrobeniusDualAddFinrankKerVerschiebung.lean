module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
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

@[expose] public section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem finrank_range_relFrob_dual_add_finrank_ker_verschiebung (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (h : (p : k) = 0) (G : PDivGroup p k) : Module.finrank k (LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap) + Module.finrank k (LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap) = Module.finrank k (G.A 1) := by
  let e : G.dual.A 1 ≃ₗ[k] Module.Dual k (G.A 1) := CartierDual.toDual k (G.A 1)
  set W := LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap with hW
  have hker : LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap
      = (W.map e.toLinearMap).dualCoannihilator := by
    ext a
    rw [Submodule.mem_dualCoannihilator, LinearMap.mem_ker]
    change (verschiebung h G).app 1 a = 0 ↔ _
    constructor
    · rintro ha _ ⟨_, ⟨x, rfl⟩, rfl⟩
      change e ((relFrob h G.dual).app 1 x) a = 0
      induction x using frobTwist_induction h (G := G.dual) 1 with
      | h0 => simp
      | h2 x y hx hy => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
      | h1 r χ =>
        rw [map_smul, map_smul, LinearMap.smul_apply, relFrob_app_frobProj]
        have := frobTwistDual_verschiebung h 1 χ a
        rw [ha, map_zero] at this
        exact (congrArg (r • ·) this.symm).trans (smul_zero r)
    · intro ha
      refine frobTwist_ext_dual h 1 fun χ => ?_
      rw [frobTwistDual_verschiebung, map_zero]
      refine ha _ ⟨_, ⟨(frobProj h G.dual).app 1 χ, rfl⟩, ?_⟩
      exact congrArg e (relFrob_app_frobProj h (G := G.dual) 1 χ)
  rw [hker, ← e.finrank_map_eq W]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq _

end GlobalTheory.PDivGroup
