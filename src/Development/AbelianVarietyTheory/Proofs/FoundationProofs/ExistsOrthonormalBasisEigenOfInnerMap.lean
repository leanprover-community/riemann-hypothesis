module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalEigenbasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

noncomputable section

namespace GlobalTheory.UnitaryTheta

theorem exists_eigenbasis_of_isPosHerm {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) (a : V →ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
      (∀ i j, H (e i) (e j) = if i = j then 1 else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i := by
  first
  | exact @_root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis
  | exact _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis
  | (apply _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis ..)

theorem unitary_exists_orthonormal_eigenbasis :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H →
      ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) →
        ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
          (∀ i j, H (e i) (e j) = if i = j then 1 else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i :=
  fun _ _ _ _ H hH a ha => exists_eigenbasis_of_isPosHerm H hH a.toLinearMap ha

end GlobalTheory.UnitaryTheta
