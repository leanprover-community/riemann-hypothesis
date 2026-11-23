module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrEigenTangentExtension
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.dvr_eigen_tangent_extension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (T : Over (Sp V)) [GrpObj T] [IsCommMonObj T] (GK : Over (Sp K)) [GrpObj GK] (φ₀ : GK.left ⟶ T.left)
    (Oe : Type) [CommRing Oe] (actT : OAct Oe T) (actK : OAct Oe GK) (g n : ℕ) (ML : LieModel GK (𝟙 _) (Fin g → K))
    (ρK : Oe →+* Module.End K (Fin g → K)) (σV : Oe →+* V) (vV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T)) (b : Fin n → Fin g → K),
    IsGrpPullback GK T (spMap (algebraMap V K)) φ₀ → (∀ a, (actK.act a).left ≫ φ₀ = φ₀ ≫ (actT.act a).left) →
    ML.IsActOf actK.act ρK → IsEigFrame actT (𝟙 _) σV vV →
    (∀ i, (ML.pt (b i)).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ (vV i).left) →
    ∀ w, w ∈ Submodule.span V (Set.range b) ↔
      (∃ a : epsAt (𝟙 (Sp V)) ⟶ T, IsTanAt T (𝟙 _) a ∧ (ML.pt w).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ a.left) ∧
        ∀ r, ρK r w = algebraMap V K (σV r) • w := by
  exact @GlobalTheory.CompanionTheory.Ar.Flat.EigLin.mem_span_iff
