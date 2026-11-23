module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramesRespectCubicalStructures
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

theorem _root_.GlobalTheory.T.integral_frames_respect_cubical_structures : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)) (g : Finset (Fin 3) → GtPt D.toPre (𝟙_ (Over (Sp V)))) (f : ∀ S, LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h S).left) (fun _ => 1))) (t : ∀ S, LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, ((g S).b).left] (DegPre.lineε 1))), h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (g ∅).b = 1 → (g {0, 1}).b = (g {0}).b * (g {1}).b → (g {0, 2}).b = (g {0}).b * (g {2}).b → (g {1, 2}).b = (g {1}).b * (g {2}).b → (g {0, 1, 2}).b = (g {0}).b * (g {1}).b * (g {2}).b → (∀ S, GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre (h S) (g S)) → (∀ S, (f S).IsGen) → (∀ S, (t S).IsGen) → (∀ S (e : ℕ), GlobalTheory.Poinc.IntEval.TRel U.toUnifPre (h S) (g S).b (f S) (t S) e) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z JG → Good D.toPre.P.L z JB → (val (f {0, 1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {0}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {1}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {2}) (toUnit (TF (R := V) (FractionRing V))).left z JG) * (val (t {0, 1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {0}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {1}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {2}) (toUnit (TF (R := V) (FractionRing V))).left z JB) * cubV D.toPre.cub z JB ((toUnit (TF (R := V) (FractionRing V))) ≫ (g {0}).b) ((toUnit (TF (R := V) (FractionRing V))) ≫ (g {1}).b) ((toUnit (TF (R := V) (FractionRing V))) ≫ (g {2}).b) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (val (f {0, 1}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {0, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f ∅) (toUnit (TF (R := V) (FractionRing V))).left z JG) * (val (t {0, 1}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {0, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t ∅) (toUnit (TF (R := V) (FractionRing V))).left z JB) := by
  first | exact @GlobalTheory.Poinc.IntCube.integral_cube | exact GlobalTheory.Poinc.IntCube.integral_cube | (intros; apply GlobalTheory.Poinc.IntCube.integral_cube <;> assumption)
