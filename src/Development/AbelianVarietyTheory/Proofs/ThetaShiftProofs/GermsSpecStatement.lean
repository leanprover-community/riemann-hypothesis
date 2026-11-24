module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermsSpec
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_germs_localRing_convergent_divisible : Nonempty Germs ∧ ∀ (Γ : Germs) (w : ℂ), IsLocalRing (Γ.R w) ∧ (∀ f : Γ.R w, (f : ℂ⸨X⸩) ∈ Conv.convLaurent) ∧ ∀ (f : Γ.R w) (g : ℂ⸨X⸩), Γ.ev w f ≠ 0 → (f : ℂ⸨X⸩) * g ∈ Γ.R w → g ∈ Γ.R w := by
  first | exact @GlobalTheory.GermRing.germs_spec | exact GlobalTheory.GermRing.germs_spec | (intros; apply GlobalTheory.GermRing.germs_spec <;> assumption)
