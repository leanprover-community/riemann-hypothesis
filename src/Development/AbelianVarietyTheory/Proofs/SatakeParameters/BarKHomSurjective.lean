module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.IdemAdj

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
def barKHom : Kinf E a →* Kinf E a where
  toFun := barK
  map_one' := Subtype.ext (by ext i j : 1; simp [barK, Matrix.one_apply])
  map_mul' k k' := Subtype.ext (by
    change Matrix.transpose (star (k.1 * k'.1)) = Matrix.transpose (star k.1) * Matrix.transpose (star k'.1)
    ext i j
    simp [Matrix.mul_apply, Matrix.star_apply, mul_comm])



omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem barK_barK (k : Kinf E a) : barK (barK k) = k := Subtype.ext (by
  ext i j
  simp [barK, Matrix.star_apply])


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem barKHom_surjective : Function.Surjective (barKHom E a) := fun k => ⟨barK k, barK_barK k⟩

def cptOn (π : CuspSub E a) : Representation ℂ (Kinf E a) π.V where
  toFun k := π.op (.cpt k)
  map_one' := by
    ext φ
    simp [CuspSub.op, act]
  map_mul' k k' := by
    ext φ
    simp [CuspSub.op, act, map_mul]

@[simp] theorem cptOn_val (π : CuspSub E a) (k : Kinf E a) (φ : π.V) :
    (cptOn π k φ).1 = cptRep E a k φ.1 := rfl

end GlobalTheory.IdemAdj

end
