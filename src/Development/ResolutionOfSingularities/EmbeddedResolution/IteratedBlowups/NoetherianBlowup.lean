module

public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

theorem isNoetherian_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f] :
    AlgebraicGeometry.IsNoetherian X := by
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace ↥X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  constructor

theorem isNoetherian_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian Y := by
  have : AlgebraicGeometry.LocallyOfFiniteType e.inv := inferInstance
  have : AlgebraicGeometry.QuasiCompact e.inv := inferInstance
  exact isNoetherian_of_locallyOfFiniteType e.inv

theorem isNoetherian_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    {π : X' ⟶ X} {I : X.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf π I) :
    AlgebraicGeometry.IsNoetherian X' := by
  have : AlgebraicGeometry.IsProper π := Blowup.blowupIsProper.{u} X X' π I h
  have : AlgebraicGeometry.LocallyOfFiniteType π := inferInstance
  have : AlgebraicGeometry.QuasiCompact π := inferInstance
  exact isNoetherian_of_locallyOfFiniteType π

instance instIsNoetherianAffineSpaceIdx (k : Type u) [Field k] (n : Type u) [Finite n] :
    AlgebraicGeometry.IsNoetherian (affineSpaceIndexedBy k n) := by
  have : IsNoetherianRing ↑(CommRingCat.of (MvPolynomial n k)) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial n k))
  have : AlgebraicGeometry.IsNoetherian
      (Spec (CommRingCat.of (MvPolynomial n k))) := inferInstance
  exact isNoetherian_of_iso
    (AlgebraicGeometry.AffineSpace.SpecIso n (CommRingCat.of k)).symm

theorem isNoetherian_schemeAt {X : Scheme.{u}} (B : SequenceOfBlowups X)
    [AlgebraicGeometry.IsNoetherian X] (i : ℕ) (hi : i ≤ B.length) :
    AlgebraicGeometry.IsNoetherian (B.schemeAt i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    exact isNoetherian_of_iso B.isoZero.symm
  | succ n ih =>
    intro hi
    have hn : n < B.length := hi
    exact @isNoetherian_of_isBlowupAlongIdealSheaf (B.schemeAt n) (B.schemeAt (n + 1)) (ih (le_of_lt hn)) _ _
      (B.isBlowupAlongIdealSheaf_blowupMorphism n hn)

theorem isNoetherian_ambientLevel {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (i : ℕ)
    (hi : i ≤ S.ambientLength) :
    AlgebraicGeometry.IsNoetherian (S.ambientLevel i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    have : AlgebraicGeometry.IsNoetherian S.ambient :=
      instIsNoetherianAffineSpaceIdx k (ULift.{u, 0} (Fin S.dim))
    exact isNoetherian_of_iso S.ambientBlowups.isoZero.symm
  | succ n ih =>
    intro hi
    have hn : n < S.ambientLength := hi
    exact @isNoetherian_of_isBlowupAlongIdealSheaf (S.ambientLevel n) (S.ambientLevel (n + 1)) (ih (le_of_lt hn)) _ _
      (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

theorem embeddedPrincipalizationAmbientIsNoetherian (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    EmbeddedPrincipalizationAmbientIsNoetherian A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  exact isNoetherian_ambientLevel (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) i hi

end FunctorialResolution.EmbeddedResolution
