module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralEqZeroOfNormalisedCosetIntegrals
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary

theorem _root_.GlobalTheory.T.quotientIntegral_eq_zero_of_normalised_coset_integrals : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (T N : Subgroup H), IsClosed (T : Set H) → IsClosed (N : Set H) → IsMulCommutative T → (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) → Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2) → ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (dn : Measure N) [dn.IsHaarMeasure] [dn.IsMulRightInvariant] (φ : H → ℂ), Measurable φ → LeftInv T φ → Integrable (descend T φ) (quotMeas T dt dh) → (∀ x, ∫ n : N, φ (n * x) ∂dn = 0) → quotInt T dt dh φ = 0 := by
  first | exact @GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero | exact GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero | (intros; apply GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero <;> assumption)
