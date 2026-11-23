module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartAtSiegelBlowupPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreChartOfTautologicalChartEtaleCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartCentreIsCompletedEtaleLocalMapStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin

namespace GlobalTheory.AllChart

theorem preChart_all : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, PreChart F (π ≫ z) j φ BD d x := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hmin hblow x
  obtain ⟨C, G₁, _, y, α₁, ξ, hfam, hy, hx⟩ :=
    GlobalTheory.T.exists_tautological_chart_at_siegel_blowup_point g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow x
  have : IsCommMonObj G₁ := hfam.1.comm
  obtain ⟨het, hsep⟩ :=
    GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap GlobalTheory.T.chartSeparation_data_defined_over_centre_field g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy
  have h := GlobalTheory.T.preChart_of_tautologicalChart_etaleCompletion g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy het hsep
  rwa [hx] at h

end GlobalTheory.AllChart
