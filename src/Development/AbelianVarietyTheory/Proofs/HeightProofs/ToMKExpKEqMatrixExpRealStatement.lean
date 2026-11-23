module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ToMKExpKEqMatrixExpReal
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.rightDeriv_norm_le_finite_words_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ), ∃ (U : List (List (Mx n))) (C : ℝ), 0 ≤ C ∧ (∀ u ∈ U, ∀ X ∈ u, inK ε X) ∧ ∀ (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d → ∀ w : List (Mx n), w.length ≤ m → (∀ X ∈ w, inK ε X ∧ hs X ≤ 1) → ‖GlobalTheory.KFourier.rder ε w φ 1‖ ≤ C * (U.map fun u => ‖GlobalTheory.KFourier.rder ε u φ 1‖).sum := by
  first | exact @GlobalTheory.KFourier.rder_bound_basisWords | exact GlobalTheory.KFourier.rder_bound_basisWords | (intros; apply GlobalTheory.KFourier.rder_bound_basisWords <;> assumption)
