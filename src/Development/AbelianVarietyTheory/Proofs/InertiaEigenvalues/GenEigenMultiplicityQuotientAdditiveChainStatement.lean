module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChain
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

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.genEigenMultiplicityQuotient_additive_chain : ∀ {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (P Q S : Submodule k U), S ≤ Q → Q ≤ P → (∀ x ∈ P, T x ∈ P) → (∀ x ∈ Q, T x ∈ Q) → (∀ x ∈ S, T x ∈ S) → FiniteDimensional k (↥P ⧸ S.submoduleOf P) → ∀ x : k, gmult T P S x = gmult T P Q x + gmult T Q S x := by
  first | exact @GlobalTheory.PhiGam.GmultAdd.main | exact GlobalTheory.PhiGam.GmultAdd.main | (intros; apply GlobalTheory.PhiGam.GmultAdd.main <;> assumption)
