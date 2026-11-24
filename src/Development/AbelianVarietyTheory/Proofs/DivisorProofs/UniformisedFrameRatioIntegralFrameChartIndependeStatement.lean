module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFrameRatioIntegralFrameChartIndepende
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.uniformisedFrame_ratio_integralFrame_chart_independent : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x), e.IsGen → ∀ (h : 𝟙_ (Over (Sp V)) ⟶ G) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), f.IsGen → GlobalTheory.Poinc.IntTerm.Ext U x h → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA JA' : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG JG' : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → Good A.L z JA' → Good U.LG.L z JG' → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG)⁻¹ = Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG' (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA' x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA' * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG')⁻¹ := by
  first | exact @GlobalTheory.Poinc.FrameIndep.frame_ratio_indep | exact GlobalTheory.Poinc.FrameIndep.frame_ratio_indep | (intros; apply GlobalTheory.Poinc.FrameIndep.frame_ratio_indep <;> assumption)
