module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.FieldDescentSm

theorem smoothOfRelativeDimension_and_geometricallyConnected_descend : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  intro k E _ _ _ Y X p q π H D hX hD hq
  have hf := GlobalTheory.FieldDescentAb.fpqc_spMap (algebraMap k E)
  have hsq : Smooth q := SmoothOfRelativeDimension.smooth D q
  have hsm : Smooth p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hf hsq
  have hp : GeometricallyConnected p :=
    GlobalTheory.FieldDescentAb.geometricallyConnected_of_isPullback (algebraMap k E) H
  refine ⟨?_, hp⟩
  have hc : ConnectedSpace Y :=
    hp.geometrically_connectedSpace (𝟙 _) (𝟙 Y) p (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨x⟩ := hX
  obtain ⟨D', hD'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected p (π x)
  have h' : SmoothOfRelativeDimension D' q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D').of_isPullback H hD'
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique q hD h' x]
  exact hD'

end GlobalTheory.FieldDescentSm
