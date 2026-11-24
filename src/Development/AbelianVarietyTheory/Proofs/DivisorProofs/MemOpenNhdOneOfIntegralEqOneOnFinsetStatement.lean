module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOpenNhdOneOfIntegralEqOneOnFinset
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.mem_open_nhd_one_of_integral_eq_one_on_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Set (finU (E := E) (n := n))), IsOpen U →
    (1 : finU (E := E) (n := n)) ∈ U → ∃ T : Finset (Pl E), ∀ u : finU (E := E) (n := n), (∀ v ∈ T, cLoc v (u : UA E n) = 1) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E) → u ∈ U := by
  first | exact @GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset | exact GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset | (intros; apply GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset <;> assumption)
