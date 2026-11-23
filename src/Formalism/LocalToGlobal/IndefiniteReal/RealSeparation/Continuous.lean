module

public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FrameMatEqGlobal
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.BesPerSt
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi



attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {D : D7} {A T : HSp D} {ι : A.V →ₗ[D.host.E] T.V} {s : GA D A →* GA D T}



theorem map_formula_one {R : Type*} [CommRing R] (φ : AE D →+* R) (hι : HSpace.IsIsomEmb A T ι) (h : GA D A)
    (hh : (mt A h).map φ = 1) :
    ((frameMat T A ι).map (incA D) * mt A h * (embP' A T ι).map (incA D) +
      (1 - (frameMat T A ι * embP' A T ι).map (incA D))).map φ = 1 := by
  have e : ((frameMat T A ι).map (incA D) * mt A h * (embP' A T ι).map (incA D)).map φ =
      ((frameMat T A ι * embP' A T ι).map (incA D)).map φ := by
    rw [Matrix.map_mul, Matrix.map_mul, hh, Matrix.mul_one, Matrix.map_mul (f := incA D), Matrix.map_mul]
  rw [Matrix.map_add _ (map_add φ), e, Matrix.map_sub _ (map_sub φ), Matrix.map_one _ (map_zero φ) (map_one φ),
    add_sub_cancel]

theorem s_mem_GinfC (hι : HSpace.IsIsomEmb A T ι) (hemb : IsEmbHom ι s) {a : GA D A} (ha : a ∈ GinfC A) :
    s a ∈ GinfC T := by
  have key : ∀ (V : HSp D) (g : GA D V), ((finHom V g : GL (Fin V.rank) _) : Matrix _ _ _) =
      (mt V g).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom :=
    fun V g => rfl
  have ha' : finHom A a = 1 := ha
  have hh : (mt A a).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
      = 1 := by
    rw [← key, ha', Units.val_one]
  show finHom T (s a) = 1
  apply Units.ext
  rw [key, Units.val_one, mt_of_embRel hι (hemb a)]
  exact map_formula_one _ hι a hh

end Formalism.IndefR.Mi

end
