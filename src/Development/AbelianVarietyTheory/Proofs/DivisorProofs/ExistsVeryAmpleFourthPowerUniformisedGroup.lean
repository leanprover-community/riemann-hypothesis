module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsUniformisedGroupPowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAlongPullbackTransportIsoStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_veryAmpleAlong_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), ∃ (m : ℕ) (σ : Fin (m + 1) → H0 U.LG.L 4), VeryAmpleAlong ((Over.pullback (jK R)).obj G).hom (pullback.fst G.hom (jK R)) U.LG.L σ := by
  intro R _ _ I D A G _ _ U
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field GlobalTheory.lawsAndExpansions.1.1.ample _ A
  obtain ⟨σ, c, H⟩ := GlobalTheory.T.exists_integral_sections_uniformisedGroup_power R I D A G U (k := 4) (by norm_num) b
  have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact ⟨m, σ, GlobalTheory.T.veryAmpleAlongPullback_transport_iso _ A.A.hom U.gen.hom.left (Over.w U.gen.hom) _ U.LG.isLB A.isLB b hb σ c H⟩
