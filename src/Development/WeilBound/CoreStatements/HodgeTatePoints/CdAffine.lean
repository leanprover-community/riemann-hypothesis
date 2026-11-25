module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CdChart
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CdFrame
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars

@[expose] public section

noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj

theorem germ_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ z : X0, ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧ Nonempty (GermAt t j d) := by
  intro E _ _ _ H _ hs X0 t hp z
  obtain ⟨S, _, x0, d, G, A, tg, x, c, hj, hz, hc, ht, hb, hU⟩ := chart_affine E H X0 t z
  obtain ⟨e, ph1, ph2, sy, ad, hfr, htr, hfa, had⟩ := frame_affine E H X0 t S x0 d G A tg _ x c hc hU
  obtain ⟨hax, hr⟩ := FBIdAd.fbId E H X0 t hp hs S x0 _ G A _ tg _ x e ph1 ph2 sy ad hc hfr hfa had
  exact ⟨S, _, x0, d, hj, hz, ⟨⟨mkFB G A ph1 ph2 sy ad hax hr, x, e, tg, hc, ht, hb, hfr, htr, hfa⟩⟩⟩

end PositivityTheory.HtPt.Cd
