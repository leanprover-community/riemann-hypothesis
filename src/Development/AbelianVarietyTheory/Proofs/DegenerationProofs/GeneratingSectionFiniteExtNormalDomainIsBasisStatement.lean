module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeneratingSectionFiniteExtNormalDomainIsBasis
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.generatingSection_finite_ext_normal_domain_isBasis : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left), L.IsLB → ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (χ : Sp W ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))), IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ) σ) → (∃ e, UnivBasis G L (jK W ≫ χ) e) → SecM.ofSec G (VVRank.pullS G _ (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) σ) ≠ 0 → GlobalTheory.LN.BasisAlong G L 1 (𝟙 (Over.mk χ)) (fun _ : Fin 1 => σ) := by
  first | exact @GlobalTheory.Ex.OneGenBasis.basisAlong_of_isGenSec | exact GlobalTheory.Ex.OneGenBasis.basisAlong_of_isGenSec | (intros; apply GlobalTheory.Ex.OneGenBasis.basisAlong_of_isGenSec <;> assumption)
