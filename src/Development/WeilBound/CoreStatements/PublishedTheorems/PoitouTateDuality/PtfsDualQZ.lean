module

public import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dual.Defs
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

noncomputable section

open GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

def dualQZ {N : ℕ} [NeZero N] {X Y : Type} [AddCommGroup X] [Module (ZMod N) X] [AddCommGroup Y]
    (E : X ≃+ Y) : Module.Dual (ZMod N) X ≃+ (Y →+ QZ) where
  toFun φ := (zmodToQZ N).comp (φ.toAddMonoidHom.comp E.symm.toAddMonoidHom)
  invFun ψ := (zmodOfQZ (ψ.comp E.toAddMonoidHom) (fun a => by
      rw [← map_nsmul, ZModModule.char_nsmul_eq_zero, map_zero])).toZModLinearMap N
  left_inv φ := LinearMap.ext fun a => zmodToQZ_injective (by
    simp [zmodToQZ_zmodOfQZ])
  right_inv ψ := AddMonoidHom.ext fun y => by
    simp [zmodToQZ_zmodOfQZ]
  map_add' φ φ' := AddMonoidHom.ext fun y => by simp

theorem dualQZ_apply {N : ℕ} [NeZero N] {X Y : Type} [AddCommGroup X] [Module (ZMod N) X]
    [AddCommGroup Y] (E : X ≃+ Y) (φ : Module.Dual (ZMod N) X) (y : Y) :
    dualQZ E φ y = zmodToQZ N (φ (E.symm y)) := rfl

end PositivityTheory.Lit1.PTN
