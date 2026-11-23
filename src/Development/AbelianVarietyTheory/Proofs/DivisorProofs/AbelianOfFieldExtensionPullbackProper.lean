module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
public import Mathlib.CategoryTheory.MorphismProperty.Descent

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem abelian_of_field_of_pullback : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Sp K)) [GrpObj G] (B : Over (Sp K')) [GrpObj B] (φ : B.left ⟶ G.left) (g : ℕ), IsSemiAbelian G → IsGrpPullback B G (spMap i) φ → IsProper B.hom → SmoothOfRelativeDimension g B.hom → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom := by
  intro K K' _ _ i G _ B _ φ g hG h hP hB
  have hc := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have : Flat (spMap i) := inferInstance
  have : Surjective (spMap i) := inferInstance
  have : UniversallyClosed G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hp : IsProper G.hom := ⟨⟩
  have : ConnectedSpace G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) (𝟙 _) (𝟙 _) G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (eSec G (default : PrimeSpectrum K))
  have hd' : SmoothOfRelativeDimension d B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback h.1 hd
  have e : d = g := ReciprocityTheory.ChartRestriction.G.H1.dim_unique B.hom hd' hB (eSec B (default : PrimeSpectrum K'))
  subst e
  exact ⟨⟨hc, inferInstance, hp, inferInstance⟩, hd⟩

end GlobalTheory.Mum.GenDesc
