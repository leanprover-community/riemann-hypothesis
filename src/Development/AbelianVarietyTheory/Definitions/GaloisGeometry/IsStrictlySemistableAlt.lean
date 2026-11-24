module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def alongS (F : Shv R) (n : ℕ) {Z X : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : HS R F n Z →+ HS R F n X where
  toFun x := (Abelian.Ext.mk₀ t).comp x (zero_add n)
  map_zero' := Abelian.Ext.comp_zero _ _ _ _ _
  map_add' _ _ := Abelian.Ext.comp_add _ _ _ _

def push (n : ℕ) {Z X : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : H R n Z →ₗ[R] H R n X where
  toFun x := (Abelian.Ext.mk₀ t).comp (x : HS R (coef R) n Z) (zero_add n)
  map_add' _ _ := Abelian.Ext.comp_add _ _ _ _
  map_smul' r _ := Abelian.Ext.comp_smul _ _ _ (ULift.up r : ULift.{1} R)

end Transfer

section Mu

variable (n : ℕ) [NeZero n]

def Mu (A : Type) [CommRing A] : Type := Additive (rootsOfUnity n A)


end Mu

def IsStrictlySemistable {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ))) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.Et

end
