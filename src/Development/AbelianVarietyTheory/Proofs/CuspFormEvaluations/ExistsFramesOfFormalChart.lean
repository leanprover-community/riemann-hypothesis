module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdjointnessSeriesOfFramesStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFirstPartialLawSeriesOfFramesStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesCubeDefectAlongChartOverRingStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSecondPartialLawStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSymmetrySeriesOfFramesStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameRigidificationOfCanonicalAxesStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
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



theorem exists_frames_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), IsChartG t x0 d G.F A.act tg uvec x → ∃ (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d), IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e ∧ IsPrimG t wP ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e ∧ (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) ∧ Rig0G t x0 d x A.act e wP := by
  intro E _ _ _ H X0 t S _ x0 d G A κ _ tg uvec x hc

  obtain ⟨e, hgen, htr, hax⟩ :=
    GlobalTheory.T.exists_frames_cubeDefect_along_chart_over_ring E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc

  obtain ⟨ph1, h1⟩ :=
    GlobalTheory.T.exists_firstPartialLaw_series_of_frames_alt E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax
  obtain ⟨ph2, h2⟩ :=
    GlobalTheory.T.exists_second_partial_law_alt E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax

  obtain ⟨sy, hsy⟩ :=
    GlobalTheory.T.exists_symmetry_series_of_frames_alt E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax

  obtain ⟨ad, hadc, had⟩ :=
    GlobalTheory.T.exists_adjointness_series_of_frames E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax

  obtain ⟨wP, hP⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wP t
  exact ⟨e, wP, ph1, ph2, sy, ad, ⟨hgen, h1, h2, hsy, had⟩, hP, htr, hax, hadc,
    GlobalTheory.T.frame_rigidification_of_canonical_axes E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax wP hP⟩

end GlobalTheory
