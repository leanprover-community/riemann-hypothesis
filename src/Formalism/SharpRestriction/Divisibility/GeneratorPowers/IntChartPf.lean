module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartCut
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvrPf

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem intChart_of_cut (hA : ChartDataGSt) (hB : FrameSt) (hC : FBIdSt) (hGF : GlobalFnsSt) :
    IntChartStatement := by
  intro E _ _ _ H V _ _ _ hc t hprop κ _ tg htan hbas _ hstar
  obtain ⟨d, G, A, uvec, x, hd, hu, hch⟩ := hA E H (Sp V) t V (𝟙 (Sp V)) tg htan hbas
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, hpr, htr, hfa, had, hrig⟩ :=
    hB E H (Sp V) t V (𝟙 (Sp V)) d G A κ tg uvec x hch
  have hPow := globalFnsDvr_of_globalFns hGF E H V hc t hprop
  obtain ⟨hax, hr⟩ := hC E H (Sp V) t hPow hstar V (𝟙 (Sp V)) d G A κ tg uvec x e ph1 ph2 sy ad hch hfr hfa had
  refine ⟨d, mkFB G A ph1 ph2 sy ad hax hr, uvec, x, e, wP, hd, hu, hch, hfr, hpr, htr, hrig, fun k F => ?_⟩
  exact germSt_holds E H (Sp V) t V (𝟙 (Sp V)) d G.F A.act κ tg uvec x ph1 ph2 sy ad e wP hch hfr hpr htr k F

end Formalism.MainNotions.ModuliIntegralCharts.H1
