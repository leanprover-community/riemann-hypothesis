module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
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

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise

theorem _root_.GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU (E := E) (n := n), k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU (E := E) (n := n)) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  first | exact @GlobalTheory.UnitarySplit.dense_and_split | exact GlobalTheory.UnitarySplit.dense_and_split | (intros; apply GlobalTheory.UnitarySplit.dense_and_split <;> assumption)
