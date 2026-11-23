module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformation
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_universal_first_order_deformation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (psiSet H) P → ∃ (W : FrPt Xo c (TrivSqZeroExt K (TIx Dw (psiSet H) → K))) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)), FrMap (TrivSqZeroExt.fstHom c.F K (TIx Dw (psiSet H) → K)) W P ∧ (∀ b, FrMap (GlobalTheory.FlagTan.dir c (Pi.single b (1 : K))) W (v b)) ∧ IsTanFrame (psiSet H) P v ∧ ∀ (m : TIx Dw (psiSet H) → K) (u P₀ : FrPt Xo c (DualNumber K)), FrMap (GlobalTheory.FlagTan.dir c m) W u → FrMap (GlobalTheory.FlagTan.cst c K) P P₀ → X.ptY u = X.ptY P₀ → m = 0 := by
  first | exact @GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective | exact GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective | (intros; apply GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective <;> assumption)
