module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure SmoothLocalChart {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
    {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y pY) (H : EmbeddingDatum k V pV) (u : V ⟶ Y) (y : ↥V) where
  func : Γ(H.ambient, ⊤)
  mem_domain : y ∈ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  isAffine_ambient : AlgebraicGeometry.IsAffine ambient
  smooth_ambientStruct : AlgebraicGeometry.Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : AlgebraicGeometry.LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : AlgebraicGeometry.QuasiCompact ambientStruct
  toAmbient : ambient ⟶ G.ambient
  smooth_toAmbient : AlgebraicGeometry.Smooth toAmbient
  comp_eq : toAmbient ≫ G.ambientStruct = ambientStruct
  imm : (H.emb ⁻¹ᵁ H.ambient.basicOpen func).toScheme ⟶ ambient
  isClosedImmersion_imm : AlgebraicGeometry.IsClosedImmersion imm
  isPullback :
    CategoryTheory.IsPullback imm ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u) toAmbient
      G.emb

namespace SmoothLocalChart

variable {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
  {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
  {G : EmbeddingDatum k Y pY} {H : EmbeddingDatum k V pV} {u : V ⟶ Y} {y : ↥V}

abbrev chartDomain (C : SmoothLocalChart G H u y) : V.Opens :=
  H.emb ⁻¹ᵁ H.ambient.basicOpen C.func

instance instSmoothToAmbient (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.Smooth C.toAmbient := C.smooth_toAmbient

theorem isAffineOpen_chartDomain [AlgebraicGeometry.IsAffine V]
    (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.IsAffineOpen C.chartDomain := by
  show AlgebraicGeometry.IsAffineOpen (H.emb ⁻¹ᵁ H.ambient.basicOpen C.func)
  have h : (H.emb ⁻¹ᵁ H.ambient.basicOpen C.func) = V.basicOpen (H.emb.app ⊤ C.func) :=
    Scheme.preimage_basicOpen H.emb C.func
  rw [h]
  exact (isAffineOpen_top V).basicOpen _

theorem isPullback_morphismRestrict_basicOpen (C : SmoothLocalChart G H u y) :
    CategoryTheory.IsPullback
      (AlgebraicGeometry.morphismRestrict H.emb (H.ambient.basicOpen C.func))
      C.chartDomain.ι (H.ambient.basicOpen C.func).ι H.emb :=
  AlgebraicGeometry.isPullback_morphismRestrict H.emb (H.ambient.basicOpen C.func)

end SmoothLocalChart

end FunctorialResolution.EmbeddedResolution

end
