module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultPullbackRationalSectionPushforward
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.finsum_mult_pullback_rationalSection_pushforward : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), ∀ (B : LB X) (hB : B.IsLB) (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (φ : X → ℝ), ∑ᶠ w, ((divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr)).mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) = (g.residueDegree (genericPoint Y) : ℝ) * ∑ᶠ z, ((divOfRatSec hB hr).mult z : ℝ) * φ z := by
  first | exact @GlobalTheory.PushDiv.finsum_mult_pull | exact GlobalTheory.PushDiv.finsum_mult_pull | (intros; apply GlobalTheory.PushDiv.finsum_mult_pull <;> assumption)
