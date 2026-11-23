module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitiveOfLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.TateTransport
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BidegreeTwoJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BoxTuple
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.IntegralTate

theorem nonempty_tateIso_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : Type} [Field k]
    (x : Sp k ⟶ S')
    (I : TateIso D k (Over.mk (x ≫ f) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => WeilIs t.G t.PP.L n g g' (unitOn c))) :
    Nonempty (TateIso D k (Over.mk x ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
      (fun n g g' c => WeilIs t'.G t'.PP.L n g g' (unitOn c))) := by
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  refine ⟨ObjPull.tateMove (ObjPull.pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I⟩
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (weilIs_grpPullback_of_comm S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc

theorem nonempty_tateIso_of_intChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F], Nonempty (TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P F _ _ _ _ _ _
  letI := io.toAlgebra
  obtain ⟨β, hβ⟩ := GlobalTheory.LevelFibre.exists_spMap ((jFK (R := T.V) F ≫ y.1.x) ≫ Xo.s)
  obtain ⟨-, I₀, -⟩ := Xo.univ.geom F (jFK (R := T.V) F ≫ y.1.x) β hβ
  obtain ⟨I₁⟩ := nonempty_tateIso_pull C.I.m1 (jFK (R := T.V) F) I₀
  obtain ⟨I₂, -⟩ := GlobalTheory.LevelFibre.exists_tate_push_comm C.I.m2 (jFK (R := T.V) F) _ rfl
    (ObjPull.pushEquiv C.I.m2.cart (Over.mk (jFK (R := T.V) F))) (fun _ => rfl) I₁
  obtain ⟨I₃, -⟩ := ReciprocityTheory.ChartRestriction.G.H1.tateTransport_holds GlobalTheory.firstFiveLaws.1.weil E H T.V _ C.I.G P F Dw I₂
  exact ⟨I₃⟩

end GlobalTheory.IntegralTate
