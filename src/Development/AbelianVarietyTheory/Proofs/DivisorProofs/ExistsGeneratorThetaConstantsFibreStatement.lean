module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorThetaConstantsFibre
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_generator_thetaConstants_fibre : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K)
  (o : Type) [CommRing o] (g m : ℕ) (J : Type) (b : TBase o (m ^ 2)) (s : Sp K ⟶ Sp o) (t : TObj g (m ^ 2) J b s)
  (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
  LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
  ∀ v : Ix g (m ^ 2) → K, t.HasTh (𝟙 _) v →
  ∃ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))) (κ : K), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th ∧ κ ≠ 0 ∧
    ∀ a, ∃ y : Over.mk (spMap ev) ⟶ D.P.A, GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L D.rig m th y (GlobalTheory.Ex.fnOf (κ * v a)) := by
  first | exact @GlobalTheory.FibThetaMove.exists_gen_thG_fibre | exact GlobalTheory.FibThetaMove.exists_gen_thG_fibre | (intros; apply GlobalTheory.FibThetaMove.exists_gen_thG_fibre <;> assumption)
