module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
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

open NumberField

theorem _root_.GlobalTheory.T.exists_invariant_positive_petersson_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ B : GlobalTheory.DefU.autU E n →ₗ⋆[ℂ] GlobalTheory.DefU.autU E n →ₗ[ℂ] ℂ, (∀ u v, star (B u v) = B v u) ∧ (∀ v, 0 ≤ (B v v).re) ∧ (∀ v, B v v = 0 → v = 0) ∧ ∀ g u v, B (GlobalTheory.DefU.autRep E n g u) (GlobalTheory.DefU.autRep E n g v) = B u v := by
  first | exact @GlobalTheory.DefU.Petersson.exists_invariant_pos_form | exact GlobalTheory.DefU.Petersson.exists_invariant_pos_form | (intros; apply GlobalTheory.DefU.Petersson.exists_invariant_pos_form <;> assumption)
