module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeOfUniformisationEqModelLattice
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.lattice_of_uniformisation_eq_model_lattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (Gu : Over (Sp V)) [GrpObj Gu] [IsCommMonObj Gu], IsSemiAbelian Gu → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A Gu) (F : I → (Gu ⟶ Gu)) (m : I → D.toPre.X →+ D.toPre.X), (∀ e, EndChar U (F e) (m e)) → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (fV : V →+* V'), IsLocalHom fV → ∀ (ξ : Sp V' ⟶ M.Z) (a : o →+* V'), ξ ≫ M.s = spMap a → ∀ (G' : Over (Sp V')) [GrpObj G'] (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left), IsGrpPullback G' Gu (spMap fV) β → IsGrpPullback G' G ξ β' → (∀ e, ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ (F e).left ∧ F'.left ≫ β' = β' ≫ (f e).left) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (iK : V' →+* K), Function.Injective iK → iK.comp fV = (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V)) → ∀ c : T → D.toPre.X →+ ZMod L, (∀ t, ExtNear (gγ t) (ξ (closedPoint V')) ∧ ∃ (q : QkPt D.toPre K L) (τ : Multiplicative D.toPre.X →* Kˣ) (x : TFK (R := V) K ⟶ A.A) (x' : Sp K ⟶ G'.left), q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkToAkU U.toUnifPre K L q x ∧ (∀ χ, (τ (Multiplicative.ofAdd χ) : K) = iK (a ((ζ : o) ^ (c t χ).val))) ∧ x' ≫ G'.hom = spMap iK ∧ x' ≫ β = x.left ≫ genMap U ∧ ValAt (gγ t) (spMap iK ≫ ξ) (x' ≫ β')) → LatAt f gγ ζ L m c (ξ (closedPoint V')) := by
  first | exact @GlobalTheory.Poinc.FibLat.latAt_of_unif | exact GlobalTheory.Poinc.FibLat.latAt_of_unif | (intros; apply GlobalTheory.Poinc.FibLat.latAt_of_unif <;> assumption)
