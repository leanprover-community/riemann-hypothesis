module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.DiscreteHaar
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
import Mathlib.Tactic.Linter.HaveILetI
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

open MeasureTheory Set Matrix
open scoped ENNReal NNReal Pointwise

namespace PI.NglqJacSplitW

theorem linModulusV_of (h : LinModulus) : LinModulusV := by
  intro F _ _ _ _ _ _ V _ _ _ _ _ ι _ _ ⟨e⟩ f hf ν hν S hS
  haveI := hν
  letI : MeasurableSpace (ι → F) := borel (ι → F)
  haveI : BorelSpace (ι → F) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V :=
    Topology.IsInducing.topologicalAddGroup e e.toHomeomorph.isInducing
  let E : V ≃ᵐ (ι → F) := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun x => rfl
  haveI : (ν.map E).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map ν e.toLinearEquiv.toAddEquiv e.continuous e.symm.continuous
  let g : (ι → F) →ₗ[F] (ι → F) :=
    (e.toLinearEquiv : V →ₗ[F] (ι → F)) ∘ₗ f ∘ₗ (e.toLinearEquiv.symm : (ι → F) →ₗ[F] V)
  have hdet : (LinearMap.toMatrix' g).det = LinearMap.det f := by
    rw [LinearMap.det_toMatrix']
    exact LinearMap.det_conj f e.toLinearEquiv
  have hmv : ∀ x, (LinearMap.toMatrix' g) *ᵥ x = g x := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have himg : (fun x => (LinearMap.toMatrix' g) *ᵥ x) '' (E '' S) = E '' (f '' S) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    rw [hmv, hE, hE]
    simp [g]
  have hES : MeasurableSet (E '' S) := E.measurableSet_image.mpr hS
  have key := h F ι (LinearMap.toMatrix' g) (by rw [hdet]; exact hf) (ν.map E) inferInstance
    (E '' S) hES
  rw [himg, hdet, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply,
    E.preimage_image, E.preimage_image] at key
  exact key

end PI.NglqJacSplitW
