module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Hcptgen
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hcpt_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), CharZero Ω ∧ IsLocallyNoetherian 𝔐.X ∧ IsProper (Limits.pullback.snd 𝔐.t.G.hom 𝔐.ξ) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ 𝔐.ξ) ⟶ 𝔐.t.G) (fun a g => g ≫ 𝔐.t.act.act a) (fun n g g' c => Out.WeilIs 𝔐.t.G 𝔐.t.PP.L n g g' (unitOn c)))) ∧ 2 * Module.finrank Ω 𝔐.Li = Module.finrank ℤ D.La ∧ (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ ∀ s, mseg y s ≠ 0 → IsNoetherianRing (chartRing o (mseg y) s) ∧ IsIntegrallyClosed (chartRing o (mseg y) s) ∧ IsFractionRing (chartRing o (mseg y) s) Ω ∧ ∃ x : Sp (chartRing o (mseg y) s) ⟶ 𝔐.X, spMap (algebraMap (chartRing o (mseg y) s) Ω) ≫ x = 𝔐.ξ ∧ ∀ q : Cpt 𝔐.ξ, q.1 ∈ Set.range x ↔ (InChart 𝔐.ξ (mseg y) s q ∧ OverZp 𝔐 p q) :=
  @PositivityTheory.HtPt.Hcptgen.hcpt_generic

end GlobalTheory.CompanionTheory.Ar.HT
