module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem gU_eq_one_add {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) :
    gU i c₀ = 1 + Matrix.replicateCol Unit c₀ * Matrix.replicateRow Unit (Pi.single i (1 : A) : Fin t → A) := by
  unfold gU
  congr 1
  ext k j
  simp [Matrix.mul_apply, Pi.single_apply]

theorem det_gU {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) (h : c₀ i = 0) :
    (gU i c₀).det = 1 := by
  rw [gU_eq_one_add, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [h]

theorem exists_GL_gU : ∀ {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) (_ : c₀ i = 0),
    ∃ g : GL (Fin t) A, g.1 = gU i c₀ ∧ Matrix.GeneralLinearGroup.det g = 1 := by
  intro A _ t i c₀ h
  refine ⟨Matrix.GeneralLinearGroup.mk'' (GlobalTheory.CompanionTheory.NullFr.gU i c₀)
    (by rw [GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h]; exact isUnit_one), rfl, ?_⟩
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h

end GlobalTheory.CompanionTheory.NullFr
