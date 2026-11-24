module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalNoetherianStalkFactorOfFieldPoint
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem _root_.GlobalTheory.T.exists_normalNoetherianStalk_factor_of_fieldPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), IsNormalScheme M.Z → ∀ (R : Subalgebra o Ω) (K : Type) [Field K] (x : Sp K ⟶ M.Z) (yK : R →+* K), (∀ a ∈ R, a ∈ M.O (x (closedPoint K))) → (∀ a : R, yK a = M.val x a) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (_ : IsIntegrallyClosed O) (_ : Algebra O Ω) (_ : IsFractionRing O Ω) (xO : Sp O ⟶ M.Z) (u : R →+* O) (v : O →+* K), spMap (algebraMap O Ω) ≫ xO = M.pt ∧ (algebraMap O Ω).comp u = R.val.toRingHom ∧ spMap v ≫ xO = x ∧ v.comp u = yK := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor | exact GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor <;> assumption)
