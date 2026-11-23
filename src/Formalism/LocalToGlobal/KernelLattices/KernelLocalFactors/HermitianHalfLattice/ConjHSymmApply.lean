module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.TI

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

variable {E : Type} [Field E] {a b : ℕ}

def conjH (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b ≃ₗ[E] HomE E a b where
  toFun y := γ'.toLinearMap ∘ₗ y ∘ₗ γ.symm.toLinearMap
  invFun y := γ'.symm.toLinearMap ∘ₗ y ∘ₗ γ.toLinearMap
  map_add' y y' := by ext v i; simp
  map_smul' r y := by ext v i; simp
  left_inv y := by ext v i; simp
  right_inv y := by ext v i; simp

theorem conjH_symm_apply (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (y : HomE E a b) :
    (conjH γ γ').symm y = γ'.symm.toLinearMap ∘ₗ y ∘ₗ γ.toLinearMap := rfl

end Formalism.L2.Ker.TI
