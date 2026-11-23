module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CrisHomExtUnit
section
universe u

theorem Bridge.CrisLoc.bcris_hom_ext_u : ∀ (l : ℕ) [Fact l.Prime] {R : Type u} [CommRing R] {f g : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* R} (h : ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), f (algebraMap _ _ x) = g (algebraMap _ _ x)), f = g := by
  intro l _ R _ f g h
  refine Reformulated.AutPerF.Bcris.hom_ext fun y => ?_
  refine RingHom.congr_fun (Reformulated.AutPerF.BcrisPlus.hom_ext
    (f := f.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l ↥(PadicComplexInt l)) _))
    (g := g.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l ↥(PadicComplexInt l)) _)) fun x => ?_) y
  rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact h x

end
end CrisHomExtUnit
namespace CrisExtensionUnit
section
universe u

namespace Bridge.CrisLoc.CrisExtensionUnitLemmas

open Ideal Reformulated.AutPerF

variable {p : ℕ} [Fact p.Prime]
variable {R : Type*} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

end Bridge.CrisLoc.CrisExtensionUnitLemmas

end
end CrisExtensionUnit
namespace DeRhamHomExtUnit
section
universe u

theorem Bridge.CrisLoc.bdR_hom_ext_u : ∀ (l : ℕ) [Fact l.Prime] {R : Type u} [CommRing R] {f g : (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l)) →+* R} (h : ∀ x : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)), f (algebraMap _ _ x) = g (algebraMap _ _ x)), f = g := by
  intro l _ R _ f g h
  exact IsLocalization.ringHom_ext
    (nonZeroDivisors (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (RingHom.ext h)

end
end DeRhamHomExtUnit
