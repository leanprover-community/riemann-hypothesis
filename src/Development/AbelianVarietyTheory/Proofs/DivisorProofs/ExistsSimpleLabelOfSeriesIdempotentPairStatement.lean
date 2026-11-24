module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimpleLabelOfSeriesIdempotentPair
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
import Formalism.LocalToGlobal.Divisibility.ClassSum
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.BasicNotions Formalism.L2.DIV

theorem _root_.GlobalTheory.T.exists_simple_label_of_seriesIdempotent_pair : ∀ (g : ℕ) [Fact g.Prime] (C : LabelConv (ZMod g)) (O : LabelMap (ZMod g) C) (r : ℕ) (f : (ZMod g)[X]) (ψ : GL (Fin r) (ZMod g) → ℂ), Formalism.L2.NT.IsIrrChar ψ → ∑ x, (Formalism.L2.NT.eSerO O r f).coeff x * ψ x = ψ 1 → ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ HasLabelO O τ f ∧ ∀ x, τ.character x = ψ x := by
  first | exact @GlobalTheory.SeriesIdem.exists_simple_of_eSerO_pair | exact GlobalTheory.SeriesIdem.exists_simple_of_eSerO_pair | (intros; apply GlobalTheory.SeriesIdem.exists_simple_of_eSerO_pair <;> assumption)
