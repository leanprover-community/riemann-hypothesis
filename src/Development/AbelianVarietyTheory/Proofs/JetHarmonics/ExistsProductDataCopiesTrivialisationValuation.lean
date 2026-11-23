module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaFrame
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ImportsMore
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiWeightZeroProduct
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowData



theorem exists_powData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → (∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q) ∧ ∀ n : ℕ, ∃ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G') (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (_ : UnifPowOf3 pD pA pG U' P.U) (_ : Module (𝓞 E) D'.toPre.X) (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧ (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∀ (α : 𝓞 E) (N : ℕ), 0 < N → α * star α = (N : 𝓞 E) → ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' α 1 N θ θα := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ
  obtain ⟨hL, hL2, -, hL4, -⟩ := firstFiveLaws
  have hT := GlobalTheory.twistBaseChange
  refine ⟨?_, fun n => ?_⟩
  · choose Q hQ using exists_QVal hϖ P.D
    exact ⟨Q, hQ⟩
  obtain ⟨t', P', pG, pD, pA, ⟨PU⟩, -⟩ := PelUnifPowerDvr.main hL hT T.V E H C.I.G P n
  obtain ⟨M, oD, hx, hact⟩ := powOAct_of_globalFns hL.globalFns E H T.V C.I.G P n P'.D pD
  refine ⟨P'.D, P'.A, t'.G, inferInstance, inferInstance, pD, pA, pG, P'.U, PU, M, oD, hx, hact, ?_⟩
  intro F _ _ _ _ _ _ v hv Q hQ α N hN hα
  obtain ⟨θ, hν, hθ⟩ := exists_thetaFrame hL hL2 hL4 hT T.V ϖ hϖ P'.D (sumQ pD.xe Q)
    (QBox.main T.V ϖ hϖ n P.D P'.D pD Q hQ) F v hv
  letI := M
  have hw : TraceFormTwistIso P'.D.toPre oD H.w0 :=
    PsiWZeroProd.main T.V n P.D.toPre P'.D.toPre pD (𝓞 E) (fun a x => funext (hx a x)) P.oD oD hact H.w0 P.w0
  obtain ⟨f, -, hf⟩ := PullLin.exists_pull_linearMap hL T.V P'.D F (𝓞 E) oD H.w0 hw α N 1 hN le_rfl hα
  exact ⟨θ, f θ, hν, hθ, (hf _ _).2 rfl⟩

end GlobalTheory.PowData
