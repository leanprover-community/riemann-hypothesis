module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryExtensionAlgClosed
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_levelIsometry_extension_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R))),
    GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  first | exact @GlobalTheory.LowDat.exists_xfLevel_ext | exact GlobalTheory.LowDat.exists_xfLevel_ext | (intros; apply GlobalTheory.LowDat.exists_xfLevel_ext <;> assumption)
