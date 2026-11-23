module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem dim_eq_of_mem_inf {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : X.Opens} {n m : ℕ}
    (hU : SmoothOfRelativeDimension n (U.ι ≫ f)) (hV : SmoothOfRelativeDimension m (V.ι ≫ f))
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) : n = m := by
  have e₁ : SmoothOfRelativeDimension (0 + n) ((U ⊓ V).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_left : U ⊓ V ≤ U), Category.assoc]; infer_instance
  have e₂ : SmoothOfRelativeDimension (0 + m) ((U ⊓ V).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_right : U ⊓ V ≤ V), Category.assoc]; infer_instance
  simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨x, hxU, hxV⟩

theorem smoothOfRelativeDimension_iSup {X Y : Scheme.{0}} (f : X ⟶ Y) (D : ℕ) {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, SmoothOfRelativeDimension D ((U i).ι ≫ f)) :
    SmoothOfRelativeDimension D ((⨆ i, U i).ι ≫ f) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} D) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} D)
    (fun i => (⨆ i, U i).ι ⁻¹ᵁ U i) ?_ fun i => ?_
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · let j := ((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι
    have hr : Set.range j ⊆ Set.range (U i).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2
    let k := IsOpenImmersion.lift (U i).ι j hr
    have hk : k ≫ (U i).ι = j := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion (k ≫ (U i).ι) := by rw [hk]; infer_instance
    have : IsOpenImmersion k := IsOpenImmersion.of_comp k (U i).ι
    have e : ((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι ≫ f = k ≫ (U i).ι ≫ f := by
      rw [← Category.assoc, ← Category.assoc, hk]
    rw [e]
    exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension.{0} D) (hU i) k

theorem exists_clopen_smoothOfRelativeDimension :
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ), Smooth s → ∃ W : ℕ → X.Opens, (∀ D, IsClosed (W D : Set X)) ∧ (∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s)) ∧ (⨆ D, W D) = ⊤ ∧ Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
  intro X s hs
  let W : ℕ → X.Opens := fun D => ⨆ U : {U : X.Opens // SmoothOfRelativeDimension D (U.ι ≫ s)}, U.1
  have hsm : ∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s) := fun D =>
    smoothOfRelativeDimension_iSup s D _ fun U => U.2
  have hcov : (⨆ D, W D) = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨n, U, hx, hU⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim s x
    exact Opens.mem_iSup.2 ⟨n, Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩⟩
  have hdis : Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
    intro D D' hne
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨U, hU⟩ := Opens.mem_iSup.1 hx.1
    obtain ⟨V, hV⟩ := Opens.mem_iSup.1 hx.2
    exact (hne (dim_eq_of_mem_inf s U.2 V.2 hU hV)).elim
  refine ⟨W, fun D => ?_, hsm, hcov, hdis⟩
  have hc : (W D : Set X)ᶜ = ((⨆ D' : {D' // D' ≠ D}, W D'.1 : X.Opens) : Set X) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (⨆ D, W D) := hcov ▸ trivial
      obtain ⟨D', hD'⟩ := Opens.mem_iSup.1 hx'
      refine Opens.mem_iSup.2 ⟨⟨D', fun e => hx (e ▸ hD')⟩, hD'⟩
    · intro hx hxD
      obtain ⟨D', hD'⟩ := Opens.mem_iSup.1 hx
      have := hdis D'.2
      have hm : x ∈ W D'.1 ⊓ W D := ⟨hD', hxD⟩
      rw [this] at hm
      exact hm
  rw [← isOpen_compl_iff, hc]
  exact Opens.isOpen _

end GlobalTheory.CompanionTheory.Gaga
