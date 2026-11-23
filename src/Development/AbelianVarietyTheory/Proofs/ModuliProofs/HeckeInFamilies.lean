module

public import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.HeckeInFamilies
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransferPts
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientReducedBaseStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeCorrespondenceSecondProjectionFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyHeckeCorrespondenceSchemeStatement
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem heckeInFamilies : HeckeInFamilies := by
  intro E _ _ _ H D l Xo 𝔓 p i hr hA
  refine ⟨?_, fun S s o C j h₁ h₂ h₃ h₄ h₅ => GlobalTheory.T.existsUnique_heckeQuotient_reducedBase E H D l Xo 𝔓 p i S s o C j hr hA h₁ h₂ h₃ h₄ h₅⟩
  obtain ⟨Z⟩ := GlobalTheory.T.nonempty_heckeCorrespondenceScheme E H D l Xo 𝔓 p i hr hA
  obtain ⟨a, b, c⟩ := GlobalTheory.T.heckeCorrespondence_secondProjection_finite_etale E H D l Xo 𝔓 p i Z hr hA
  obtain ⟨d, e⟩ := GlobalTheory.T.heckeKernelScheme_geometric_points_eq_kernels E H D l Xo 𝔓 p i Z.toKerScheme hA
  exact ⟨Z, a, b, fun h => ⟨e h, c h⟩, fun k _ _ y C hC =>
    ⟨d k y C hC, fun z hz => pointQuot_snd E H D l Xo 𝔓 p i Z hA k z y C hz⟩⟩

end GlobalTheory.HkFam
