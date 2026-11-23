module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeOfSmoothOverNormal
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NeronCurve

theorem exists_torus_hom_extension : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
    ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i₀ : splitTorus (Sp K) X ⟶ (Over.pullback x).obj G) [IsMonHom i₀],
    ∃ (i : splitTorus C X ⟶ G) (ψ : (splitTorus (Sp K) X).left ⟶ (splitTorus C X).left), IsMonHom i ∧
      IsGrpPullback (splitTorus (Sp K) X) (splitTorus C X) x ψ ∧ ψ ≫ i.left = i₀.left ≫ pullback.fst G.hom x := by
  intro k _ C _ hC K _ x hx G _ hG X _ _ _ i₀ _
  obtain ⟨hs, -, hc⟩ := hC
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  have : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  have hN : Geo.Tor.IsNormalScheme C :=
    GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension (Sp k) C (strHom k C) 1
      (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec k)
  obtain ⟨hxd, hxp⟩ := hx
  have hj : IsGenericPointHom x := IsGenericPointHom.of_isPreimmersion x
  have hT := GlobalTheory.Diag.isSemiAbelian C X
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian (splitTorus C X) hT
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  have := hT.quasiCompact
  have := hG.smooth
  have hφ := GlobalTheory.Diag.isGrpPullback X x
  obtain ⟨V, hV, -, g, hg, w, h₁, h₂⟩ :=
    spread_hom_generic_of_isGrpPullback hj hφ (isGrpPullback_pullback G x) i₀
  have : IsDominant V.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact V.isOpen.dense ⟨_, hV⟩⟩
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.homExtNormal C V V.ι hN inferInstance inferInstance (splitTorus C X) G hT hG g hg
  refine ⟨F, _, hF, hφ, ?_⟩
  rw [← h₂, ← hF', GlobalTheory.ExtUnique.pullback_map_left_fst, ← h₁]
  exact Category.assoc _ _ _

end GlobalTheory.NeronCurve
