module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import GroundTheory.AutomorphicForms.StableConjCyclic
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

private theorem UpperTheory.commute_of_commute_of_charpoly_separable {E : Type} [Field E] [CharZero E] {n : ℕ}
    (γ a b : Matrix (Fin n) (Fin n) E) (h : γ.charpoly.Separable)
    (ha : a * γ = γ * a) (hb : b * γ = γ * b) : a * b = b * a := by
  haveI : Infinite E := Infinite.of_injective _ (Nat.cast_injective (R := E))
  have hsep : (LinearMap.charpoly (Matrix.toLinAlgEquiv' γ : Module.End E (Fin n → E))).Separable := by
    have : (Matrix.toLinAlgEquiv' γ : Module.End E (Fin n → E)) = Matrix.toLin' γ := rfl
    rw [this, Matrix.charpoly_toLin']
    exact h
  have ha' : Commute γ a := ha.symm
  have hb' : Commute γ b := hb.symm
  have hc := GroundTheory.Automorphic.commute_of_commute_of_separable hsep
    (ha'.map (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)))
    (hb'.map (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)))
  apply (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)).injective
  rw [map_mul, map_mul]
  exact hc

theorem UpperTheory.generalLinearPi_centralizer_comm_of_charpoly_separable :
    ∀ (W : Type) (K : W → Type) [∀ w, Field (K w)] [∀ w, CharZero (K w)] (n : ℕ) (γ : GL (Fin n) (∀ w, K w)), (γ : Matrix (Fin n) (Fin n) (∀ w, K w)).charpoly.Separable → ∀ a b : GL (Fin n) (∀ w, K w), a * γ = γ * a → b * γ = γ * b → a * b = b * a := by
  intro W K _ _ n γ hγ a b ha hb
  apply Units.ext
  ext i j w
  have key := UpperTheory.commute_of_commute_of_charpoly_separable
    ((Pi.evalRingHom K w).mapMatrix (γ : Matrix (Fin n) (Fin n) (∀ w, K w)))
    ((Pi.evalRingHom K w).mapMatrix (a : Matrix (Fin n) (Fin n) (∀ w, K w)))
    ((Pi.evalRingHom K w).mapMatrix (b : Matrix (Fin n) (Fin n) (∀ w, K w)))
    (by rw [RingHom.mapMatrix_apply, Matrix.charpoly_map]; exact hγ.map)
    (by rw [← map_mul, ← map_mul, ← Units.val_mul, ha, Units.val_mul])
    (by rw [← map_mul, ← map_mul, ← Units.val_mul, hb, Units.val_mul])
  rw [← map_mul, ← map_mul] at key
  exact congrFun (congrFun key i) j
