module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianTorsionInjective
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.semiabelian_torsion_injective : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [CharZero R'] (Ω : Type) [Field Ω] [Algebra R' Ω] [IsFractionRing R' Ω] (T : Type) [CommGroup T] (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (x' : Spec (CommRingCat.of R') ⟶ X) (ξ : Spec (CommRingCat.of Ω) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap R' Ω)) ≫ x' = ξ → ∀ N : ℕ, 1 ≤ N → ∀ pt : T →* (Over.mk ξ ⟶ G), Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → FullTorsion G ξ N → ∃ (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G x' N i' ∧ ∀ (a : FractionRing R' →+* Ω), a.comp (algebraMap R' (FractionRing R')) = algebraMap R' Ω → ∀ t, (pt t).left = Spec.map (CommRingCat.ofHom a) ≫ (Γ'.pt t).left ≫ i' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.exists_qfGroup_of_generic_fullTorsion | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.exists_qfGroup_of_generic_fullTorsion | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.exists_qfGroup_of_generic_fullTorsion <;> assumption)
