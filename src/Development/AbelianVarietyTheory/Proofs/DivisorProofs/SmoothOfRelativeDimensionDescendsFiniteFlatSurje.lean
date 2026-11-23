module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodOfFiniteSurjective
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjRelDim

theorem eq_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f] (p : Y ⟶ S)
    [Nonempty Y] {g m : ℕ} (hX : SmoothOfRelativeDimension g (f ≫ p)) (hY : SmoothOfRelativeDimension m p) :
    g = m := by
  let y : Y := Classical.arbitrary Y
  let t := S.fromSpecResidueField (p y)
  have hpb₂ := IsPullback.of_hasPullback p t
  have hpb₁ := IsPullback.of_hasPullback f (pullback.fst p t)
  have hpX : IsPullback (pullback.fst f (pullback.fst p t))
      (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t) (f ≫ p) t := hpb₁.paste_vert hpb₂
  have hgK : SmoothOfRelativeDimension g (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hpX hX
  have hmK : SmoothOfRelativeDimension m (pullback.snd p t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange m).of_isPullback hpb₂ hY
  obtain ⟨w, hw⟩ : p y ∈ Set.range t := by
    rw [Scheme.range_fromSpecResidueField]; rfl
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y w hw.symm
  obtain ⟨a, -⟩ := (pullback.snd f (pullback.fst p t)).surjective z
  have : Nonempty ↥(pullback f (pullback.fst p t)) := ⟨a⟩
  exact GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := (p y |> S.residueField))
    (pullback.snd f (pullback.fst p t)) (pullback.snd p t) hgK hmK

theorem smoothOfRelativeDimension_of_finite_surjective : ∀ (S : Scheme.{0}) (A B : Over S) (g : ℕ) (q : A ⟶ B),
    SmoothOfRelativeDimension g A.hom → Smooth B.hom → IsFinite q.left → Flat q.left → Surjective q.left →
    SmoothOfRelativeDimension g B.hom := by
  intro S A B g q hg hB hfin _ hsurj
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim B.hom
  have hn : ∀ y, n y = g := fun y => by
    have : Nonempty (W y) := ⟨⟨y, hW y⟩⟩
    have hd' := hd y
    have : Surjective (q.left ∣_ W y) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
    have hX : SmoothOfRelativeDimension g ((q.left ∣_ W y) ≫ (W y).ι ≫ B.hom) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q]
      have : SmoothOfRelativeDimension (0 + g) ((q.left ⁻¹ᵁ W y).ι ≫ A.hom) := inferInstance
      simpa using this
    exact (eq_of_finite_surjective (q.left ∣_ W y) ((W y).ι ≫ B.hom) hX hd').symm
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FiniteSurjRelDim
