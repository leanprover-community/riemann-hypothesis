module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem forall_principalizationCertificate_of_subset {k : Type u} [Field k]
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W p I m Mem Z _ =>
      ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (motive_2 := fun W p N μ Mem Z _ =>
      ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro W p I m Mem Z hmem Mem' hsub
    exact PrincipalizationCertificate.memory (Set.Subset.trans hmem hsub)
  · intro W p I m Mem Z hm Mem' _
    exact PrincipalizationCertificate.large hm
  · intro W p I m Mem Z M N μ hI hM hmu hZ _ ih Mem' hsub
    exact PrincipalizationCertificate.toOrder M N μ hI (Set.Subset.trans hM hsub) hmu hZ (ih Mem' hsub)
  · intro W p I m Mem Z U hU _ ih Mem' hsub
    refine PrincipalizationCertificate.localize U hU ?_
    intro z hz
    exact ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hsub)
  · intro W p N μ Mem Z hmem Mem' hsub
    exact OrderCertificate.memory (Set.Subset.trans hmem hsub)
  · intro W p N μ Mem Z hmu Mem' _
    exact OrderCertificate.large hmu
  · intro W p N μ Mem Z U hU _ ih Mem' hsub
    refine OrderCertificate.localize U hU ?_
    intro z hz
    exact ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hsub)
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hsub
    refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
    · intro z hz Jz hJz x hx
      exact hJloc z hz Jz hJz x fun hmem => hx (hsub hmem)
    · intro z hz Jz hJz
      exact ih z hz Jz hJz (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem')
        (Set.preimage_mono hsub)

theorem principalizationCertificate_mono_of_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem Mem' : Set ↥W} {Z : W.IdealSheafData} (hsub : Mem ⊆ Mem')
    (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p I m Mem' Z :=
  forall_principalizationCertificate_of_subset h Mem' hsub

private theorem forall_orderCertificate_of_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z) :
    ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z := by
  refine @OrderCertificate.rec k ‹Field k›
    (fun W p I m Mem Z _ => ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (fun W p N μ Mem Z _ => ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ W p N μ Mem Z h
  · intro W p I m Mem Z hmem Mem' hs
    exact PrincipalizationCertificate.memory (Set.Subset.trans hmem hs)
  · intro W p I m Mem Z hm Mem' _
    exact PrincipalizationCertificate.large hm
  · intro W p I m Mem Z M N μ hI hM hmu hZ _ ih Mem' hs
    exact PrincipalizationCertificate.toOrder M N μ hI (Set.Subset.trans hM hs) hmu hZ (ih Mem' hs)
  · intro W p I m Mem Z U hU _ ih Mem' hs
    exact PrincipalizationCertificate.localize U hU fun z hz =>
      ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hs)
  · intro W p N μ Mem Z hmem Mem' hs
    exact OrderCertificate.memory (Set.Subset.trans hmem hs)
  · intro W p N μ Mem Z hmu Mem' _
    exact OrderCertificate.large hmu
  · intro W p N μ Mem Z U hU _ ih Mem' hs
    exact OrderCertificate.localize U hU fun z hz =>
      ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hs)
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hs
    refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
    · intro z hz Jz hJ x hx
      exact hJloc z hz Jz hJ x fun hm => hx (hs hm)
    · intro z hz Jz hJ
      exact ih z hz Jz hJ (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem')
        (Set.preimage_mono hs)

theorem orderCertificate_mono_of_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem Mem' : Set ↥W} {Z : W.IdealSheafData} (hsub : Mem ⊆ Mem')
    (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W p N μ Mem' Z :=
  forall_orderCertificate_of_subset h Mem' hsub

end FunctorialResolution.EmbeddedResolution
