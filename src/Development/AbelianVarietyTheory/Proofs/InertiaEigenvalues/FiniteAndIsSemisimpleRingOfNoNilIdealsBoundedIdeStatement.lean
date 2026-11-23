module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Idempotents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAndIsSemisimpleRingOfNoNilIdealsBoundedIde
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents : ∀ (k R : Type) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] (d : ℕ), (∀ x : R, IsIntegral k x) → (∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) → (∀ (m : ℕ) (e : Fin m → R), OrthogonalIdempotents e → (∀ i, e i ≠ 0) → m ≤ d) → Module.Finite k R ∧ IsSemisimpleRing R := by
  first | exact @GlobalTheory.AlgRing.finite_and_isSemisimpleRing | exact GlobalTheory.AlgRing.finite_and_isSemisimpleRing | (intros; apply GlobalTheory.AlgRing.finite_and_isSemisimpleRing <;> assumption)
