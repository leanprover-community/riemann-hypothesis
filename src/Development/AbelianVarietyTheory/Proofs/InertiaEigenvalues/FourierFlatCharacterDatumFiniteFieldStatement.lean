module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierFlatCharacterDatumFiniteField
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Formalism.IndefR.Datum
open Classical

theorem _root_.GlobalTheory.T.fourier_flat_character_datum_finiteField : ∀ (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r n : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ m * C⁻¹) ∧ ∀ u : Matrix (Fin n) (Fin r) k, (∑ y : Matrix (Fin r) (Fin n) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (Matrix.trace (y * u))) = C * (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  first | exact @GlobalTheory.fourier_flatDatum_finite | exact GlobalTheory.fourier_flatDatum_finite | (intros; apply GlobalTheory.fourier_flatDatum_finite <;> assumption)
