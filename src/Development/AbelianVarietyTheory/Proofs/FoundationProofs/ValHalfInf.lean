module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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

namespace GlobalTheory.Eis.Conv

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def halfInf (F : Type) [Field F] [NumberField F] : (AF F)ˣ where
  val := (algebraMap F (Ainf F) 2⁻¹, 1)
  inv := (algebraMap F (Ainf F) 2, 1)
  val_inv := Prod.ext (by
    change algebraMap F (Ainf F) 2⁻¹ * algebraMap F (Ainf F) 2 = 1
    rw [← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]) (mul_one _)
  inv_val := Prod.ext (by
    change algebraMap F (Ainf F) 2 * algebraMap F (Ainf F) 2⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]) (mul_one _)

def halfE (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : (AF F ⊗[F] E)ˣ :=
  Units.map (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom (halfInf F)

open scoped TensorProduct in
open NumberField in
theorem _root_.GlobalTheory.Eis.Conv.sigR_halfE {F E : Type} [Field F] [NumberField F] [Field E]
    [Algebra F E] (σ : E →ₐ[F] E) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ (_root_.GlobalTheory.Eis.Conv.halfE F E).1 =
      (_root_.GlobalTheory.Eis.Conv.halfE F E).1 := by
  simp [_root_.GlobalTheory.Eis.Conv.halfE, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]

end GlobalTheory.Eis.Conv

end
