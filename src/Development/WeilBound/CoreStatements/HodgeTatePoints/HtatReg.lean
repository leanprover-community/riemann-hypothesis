module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenChart
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenRing
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

noncomputable section

namespace PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem chart_le_regAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    (s : ∀ k, J k) (q : Cpt 𝔐.ξ) (hs : InChart 𝔐.ξ (mseg y) s q) (hq : OverZp 𝔐 p q)
    (a : chartRing o (mseg y) s) : (a : Ω) ∈ regAt 𝔐.ξ q := by
  have ha : (a : Ω) ∈ Algebra.adjoin o (Set.range fun j => mseg y j / mseg y s) :=
    (Hcptgen.chartRing_mseg (o := o) y s hs.1).le a.2
  obtain ⟨b, hb, h⟩ := Hcptgen.mem_adjoin_loc Fact.out ho _ ha
  have h3 := (𝔐.tie.ring s hs.1 _).1 h q hs
  have h4 := (Hcptgen.overZp_iff Fact.out q).1 hq b hb
  have := mul_mem h3 h4.2.2
  rwa [mul_assoc, mul_inv_cancel₀ h4.1, mul_one] at this

end PositivityTheory.HtPt.Htat
