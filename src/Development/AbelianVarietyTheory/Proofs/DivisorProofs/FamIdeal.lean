module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

noncomputable section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

abbrev genPt {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) : Z := π (genericPoint Y)

abbrev fieldK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z)
    (hK : IsField (Z.presheaf.stalk (genPt π))) : Field (Z.presheaf.stalk (genPt π)) :=
  hK.toField

abbrev algKL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) :
    Algebra (Z.presheaf.stalk (genPt π)) Y.functionField :=
  (π.stalkMap (genericPoint Y)).hom.toAlgebra

abbrev algAK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Z, U) (Z.presheaf.stalk (genPt π)) :=
  (Z.presheaf.germ U (genPt π) h).hom.toAlgebra

abbrev algBL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
  (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) h).hom.toAlgebra


open scoped Classical in
def famIdeal {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) [IsAffineHom π]
    (hK : IsField (Z.presheaf.stalk (genPt π)))
    (hfd : letI := fieldK π hK; letI := algKL π
      FiniteDimensional (Z.presheaf.stalk (genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) : Ideal Γ(Z, U) := by
  classical
  exact if h : genPt π ∈ U.1 then
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    GlobalTheory.NormSheaf.normIdeal Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField Γ(Y, π ⁻¹ᵁ U.1)
      (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
  else ⊤

end GlobalTheory.NormSheafDescent
