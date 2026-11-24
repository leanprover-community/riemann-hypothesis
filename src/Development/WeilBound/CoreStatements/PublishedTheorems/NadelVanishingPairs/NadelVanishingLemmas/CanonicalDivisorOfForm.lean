module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDivisorOfForm
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.canonical_divisor_of_form : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → (∃ K : CartierDiv Y, IsDivOfForm K η) ∧ ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ Kc : CanonLB q n, toPic K = cls Kc.bundle Kc.isLB := by
  first | exact @_root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic | exact _root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic | (intros; apply _root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic <;> assumption)
