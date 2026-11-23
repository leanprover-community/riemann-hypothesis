module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogNonvanishingRatio
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

open MvPolynomial

theorem _root_.GlobalTheory.T.multihomog_nonvanishing_ratio : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (bf bg : K → ℕ) (z : ((Σ k, ι k) → ℂ)) (q : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → q ∈ P → eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u ∈ P ∧ v ∈ P ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TwistLine.forms_off_vanishing_locus | exact GlobalTheory.CompanionTheory.Ggeo.TwistLine.forms_off_vanishing_locus | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TwistLine.forms_off_vanishing_locus <;> assumption)
