module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramesTransportToFramedPointStatement
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem chartTransport_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], ChartTransportSt Xo c := by
  intro E _ _ _ H Dw l Xo c _
  have hJ : ChartJetTrSt Xo c := chartJetTr_of Xo c (chartJetTan_holds Xo c)
    (chartJetBasis_holds Xo c (fun S _ _ y w hw =>
      FrameTangent.frame_tangent_basis E H Dw l Xo c S y w hw))
  have hF : ChartFrameTrSt Xo c := GlobalTheory.T.integral_frames_transport_to_framed_point E H Dw l Xo c
  have hM : FBMapSt := fbMap_holds
  intro hstar T io y I d B tgT uvecT xT eT wPT hbas hch hdir hfr hpr htr hrig
  obtain ⟨B', hF1, hA1, hp1, hp2, hsy, had⟩ := hM T.V T.Fr (algebraMap T.V T.Fr) d (𝓞 E) B
  obtain ⟨x, x', hchx, hj2, hj1⟩ := hJ T io y I d B.G.F B.A.act tgT uvecT xT hbas hch hdir
  obtain ⟨e, wP, hfrx, hprx, hrx, hfe, hwp⟩ :=
    hF hstar T io y I d B B' tgT xT eT wPT hF1 hA1 hp1 hp2 hsy had hch hfr hpr htr hrig x x' hj2 hj1
  obtain ⟨h, hh⟩ := canonGauge_exists T.Fr d (𝓞 E) T.Fr B'
  letI := io.toAlgebra
  have hchx' : IsChart y.1 d B'.G.F B'.A.act (fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i)) x := by
    have eF : B'.G.F = fun j => MvPowerSeries.map (algebraMap T.V T.Fr) (B.G.F j) := funext hF1
    have eA : B'.A.act = fun a j => MvPowerSeries.map (algebraMap T.V T.Fr) (B.A.act a j) :=
      funext fun a => funext (hA1 a)
    rw [eF, eA]
    exact hchx
  exact ⟨B', fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i), x, e, wP, h, hchx', hfrx, hprx, hh, hrx,
    ⟨hF1, hA1, hp1, hp2, hsy, had, fun ℓ i => rfl⟩, x', hj2, hj1, hfe, hwp⟩

end GlobalTheory
