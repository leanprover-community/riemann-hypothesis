module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValues
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
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.StatementI
import Formalism.HermitianCurvature.StatementR
import Formalism.HermitianCurvature.StatementWd
import Formalism.RealPlaceAnalysis.StatementA

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.mem_span_values_of_vector_polynomial : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V) (X : ℕ → V) (ν : Fin n → ℂ), Function.Injective ν → (∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) → (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧ ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  first | exact @GlobalTheory.vecPoly_mem_span_values | exact GlobalTheory.vecPoly_mem_span_values | (intros; apply GlobalTheory.vecPoly_mem_span_values <;> assumption)
