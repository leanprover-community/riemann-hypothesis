module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelUniformisedGeometricFree
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

open MeasureTheory Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.orbit_sum_vanishes_of_parabolic_sums : ∀ (H : Type) [Group H] (T P L U : Subgroup H) (Ψ : H → ℂ), T ≤ P →
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) →
  (∀ y : H, GlobalTheory.OrbDesc.dsum T (P ⊓ L.map (MulAut.conj y).toMonoidHom) U (fun x => if x ∈ P then Ψ (x * y) else 0) = 0) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = 0 := by
  first | (exact @GlobalTheory.OrbDesc.dsum_eq_zero_of_par) | (exact GlobalTheory.OrbDesc.dsum_eq_zero_of_par) | (intros; apply GlobalTheory.OrbDesc.dsum_eq_zero_of_par  <;> assumption)
