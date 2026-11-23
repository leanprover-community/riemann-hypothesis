module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GermSymmetricTranslateFibreEqModel
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
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

theorem _root_.GlobalTheory.T.germ_symmetricTranslate_fibre_eq_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ), Odd k → ∀ (a : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (aV : baseOver (Sp T.V) ⟶ C.I.G.G) (r : Sp T.Fr ⟶ C.I.t'.G.left), r ≫ C.I.t'.G.hom = 𝟙 _ → r ≫ C.I.m1.φ = a.left → r ≫ C.I.m2.φ = spMap (algebraMap T.V T.Fr) ≫ aV.left → ∀ U : ThetaGrp C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)), SymLift C.I.G.G C.I.G.PP.L (k : ℤ) k aV U → ∀ (F F' : SecN Xo (xOf y) k) (f f' : PS T.V 1 (chD C.ch)), Regular C k F → GermIs C k F f → Moves Xo a F F' → (∀ σ σ' : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V))), IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ f → IsActOf C.I.G.G C.I.G.PP.L (k : ℤ) U σ σ' → IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ' f') → GermIs C k F' f' := by
  first | exact @GlobalTheory.TransportGerm.germIs_translate | exact GlobalTheory.TransportGerm.germIs_translate | (intros; apply GlobalTheory.TransportGerm.germIs_translate <;> assumption)
