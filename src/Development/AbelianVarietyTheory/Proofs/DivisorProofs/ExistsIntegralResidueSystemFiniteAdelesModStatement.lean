module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralResidueSystemFiniteAdelesMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

theorem _root_.GlobalTheory.T.exists_integral_residue_system_finiteAdeles_mod : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∃ R : Finset (Af E), (∀ a ∈ R, ∀ w, Valued.v (a w) ≤ 1) ∧ ∀ z : Af E, (∀ w, Valued.v (z w) ≤ 1) → ∃! a, a ∈ R ∧ ∀ w, Valued.v (z w - a w) ≤ radN E N w := by
  first | exact @GlobalTheory.CMVal.LatEnt.Res.exists_residues | exact GlobalTheory.CMVal.LatEnt.Res.exists_residues | (intros; apply GlobalTheory.CMVal.LatEnt.Res.exists_residues <;> assumption)
