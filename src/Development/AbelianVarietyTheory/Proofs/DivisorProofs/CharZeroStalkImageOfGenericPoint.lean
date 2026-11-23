module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem charZero_stalk_genPt : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    (letI := GlobalTheory.NormSheafDescent.fieldK π hK
     CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  intro Y Z π _ hY hK
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hL : CharZero Y.functionField :=
    charZero_of_injective_ringHom (f := (Y.germToFunctionField ⊤).hom) (Y.germToFunctionField_injective ⊤)
  have h0 : CharZero (Z.presheaf.stalk (genPt π)) := (π.stalkMap (genericPoint Y)).hom.charZero
  exact h0

end GlobalTheory.NormSheafDescent
