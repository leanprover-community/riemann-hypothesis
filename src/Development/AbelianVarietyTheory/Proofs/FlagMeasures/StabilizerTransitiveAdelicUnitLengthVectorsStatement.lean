module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTransitiveAdelicUnitLengthVectors
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.stabilizer_transitive_adelic_unit_length_vectors : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E) (xf g : I.Gf), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → x ∈ lamX I (1, xf) → x ∈ lamX I (1, g) → ∃ h : I.Gf, (I.fmat h *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) = (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) ∧ ∃ k ∈ I.Kset, g = h * xf * k := by
  first | exact @GlobalTheory.FinOrbit.exists_stab_mul_level | exact GlobalTheory.FinOrbit.exists_stab_mul_level | (intros; apply GlobalTheory.FinOrbit.exists_stab_mul_level <;> assumption)
