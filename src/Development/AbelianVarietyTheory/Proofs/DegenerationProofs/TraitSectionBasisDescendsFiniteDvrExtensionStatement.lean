module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtension
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.trait_sectionBasis_descends_finite_dvr_extension : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), Flat G.hom → L.IsLB → ∀ (N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ Z) (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (io : W →+* W') (io' : FractionRing W →+* FractionRing W'), io.Finite → (∀ y, io' (algebraMap W _ y) = algebraMap W' _ (io y)) → ∀ (gam : K →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap gam ≫ x = jK W ≫ χ) (h' : spMap (io'.comp gam) ≫ x = jK W' ≫ spMap io ≫ χ) (n : ℕ) (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))), FrameAt G L N x (io'.comp gam) (spMap io ≫ χ) h' f → FrameAt G L N x gam χ h f := by
  first | exact @GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite | exact GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite | (intros; apply GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite <;> assumption)
