module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightUpperUnitriangularIdempotentIndepCharacter
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
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.weight_upperUnitriangularIdempotent_indep_character : ∀ (D : D7) (k : Fin 2) (ψ ψ' : AddChar (ZMod (D.host.g k)) ℂ), ψ ≠ 1 → ψ' ≠ 1 → ∀ f, wtOf D k (eUk D k ψ) f = wtOf D k (eUk D k ψ') f := by
  first | exact @GlobalTheory.BadCount.wtOf_eUk_indep | exact GlobalTheory.BadCount.wtOf_eUk_indep | (intros; apply GlobalTheory.BadCount.wtOf_eUk_indep <;> assumption)
