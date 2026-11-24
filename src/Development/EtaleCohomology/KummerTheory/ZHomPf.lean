module

public import Development.EtaleCohomology.KummerTheory.BockCut
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section
open CategoryTheory Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ZHomPf

def linOf {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} ℤ) M] [Module (ULift.{1} ℤ) N]
    (f : M →+ N) : M →ₗ[ULift.{1} ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    have h : ((r.down : ℤ) : ULift.{1} ℤ) = r := by ext; simp
    simp only [RingHom.id_apply]
    rw [← h, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

theorem ZHom_of : LateralTheory.KummerTheory.BockCut.ZHom := by
  intro F G f hf
  refine ⟨⟨{ app := fun U => ModuleCat.ofHom (linOf (f U.unop)), naturality := ?_ }⟩, ?_⟩
  · intro X Y g
    ext a
    exact (hf Y.unop X.unop g.unop a).symm
  · intro U a
    rfl

end LateralTheory.KummerTheory.ZHomPf
