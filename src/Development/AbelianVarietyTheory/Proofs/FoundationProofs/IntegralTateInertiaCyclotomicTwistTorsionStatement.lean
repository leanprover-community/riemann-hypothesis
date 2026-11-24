module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTateInertiaCyclotomicTwistTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue

theorem _root_.GlobalTheory.T.integral_tate_inertia_cyclotomic_twist_torsion : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
  ∀ (j : ℕ), 1 ≤ j → ∀ F : Finset Ω, ∃ c : ℕ, ∀ (n : ℕ) (x : Ω), x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → CgA A l n (s x) ((((cycMod ℚ Ω l n s : ZMod (l ^ n)).val : ℕ) : Ω) ^ j * x)) →
  CgA A l n ((l : Ω) ^ c * x) 0 := by
  first | exact @GlobalTheory.IntTate.integral_tate_inertia | exact GlobalTheory.IntTate.integral_tate_inertia | (intros; apply GlobalTheory.IntTate.integral_tate_inertia <;> assumption)
