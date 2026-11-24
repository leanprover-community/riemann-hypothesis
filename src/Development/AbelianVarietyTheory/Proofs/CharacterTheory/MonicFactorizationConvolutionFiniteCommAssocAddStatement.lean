module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonicFactorizationConvolutionFiniteCommAssocAdd
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

theorem _root_.GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add : ∀ (F : Type) [Field F] (P : F[X]), P.Monic → {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite ∧ ∀ a b c : F[X] → ℂ, conv a b P = conv b a P ∧ conv (conv a b) c P = conv a (conv b c) P ∧ conv (a + b) c P = conv a c P + conv b c P ∧ conv (a - b) c P = conv a c P - conv b c P := by
  first | exact @GlobalTheory.CuspGL.conv_basic | exact GlobalTheory.CuspGL.conv_basic | (intros; apply GlobalTheory.CuspGL.conv_basic <;> assumption)
