module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.KerAevalAddStabilizerNilradicalSocle
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

@[expose] public section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.ker_aeval_add_stabilizerNilradical_socle : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g h : Module.End F V) (f : F[X]), h ∈ nilRad (LinearMap.ker (aeval g f)) → LinearMap.ker (aeval g f) ≤ LinearMap.ker (aeval (g + h) f) ∧ (LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) → ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval (g + h) (f ^ j)))) := by
  first | exact @GlobalTheory.CuspGL.ker_aeval_add_nilRad | exact GlobalTheory.CuspGL.ker_aeval_add_nilRad | (intros; apply GlobalTheory.CuspGL.ker_aeval_add_nilRad <;> assumption)
