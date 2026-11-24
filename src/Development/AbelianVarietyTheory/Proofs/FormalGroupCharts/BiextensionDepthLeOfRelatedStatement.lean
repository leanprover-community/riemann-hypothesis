module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.biextension_depth_le_of_related : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (d : ℕ) (B B' : FB T.V d (𝓞 E)) (φ φi : Pt T.V 1 d) (h h' : PS T.Fr 2 d) (u u' : Lt1 Dw → Fin d → T.Fr), (∀ m, ∃ ε : PS T.V 2 d, JRel m B B' φ φi ε) → B.IsCanonGauge T.Fr h → B'.IsCanonGauge T.Fr h' → (∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct T.Fr B' a).mulVec (u' ℓ) = io (embK c ℓ.1 a) • u' ℓ) → (∀ ℓ, u ℓ = ((dLin φ).map (algebraMap T.V T.Fr)).mulVec (u' ℓ)) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuAlg Dw T B h u e k a n ≤ nuAlg Dw T B' h' u' e k a n := by
  first | exact @GlobalTheory.ChartCmp.nuAlg_le_of_jrel | exact GlobalTheory.ChartCmp.nuAlg_le_of_jrel | (intros; apply GlobalTheory.ChartCmp.nuAlg_le_of_jrel <;> assumption)
