module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH0BijectiveH1InjectiveUniverses
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

open CategoryTheory GlobalTheory.CxCoh

theorem _root_.GlobalTheory.T.vertical_h0_bijective_h1_injective_universes : VertHas.{1,1} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧ VertHas.{1,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧ VertHas.{0,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) := by
  first | exact @GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 | exact GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 | (intros; apply GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 <;> assumption)
