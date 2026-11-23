module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)

namespace GlobalTheory.FibreDim

theorem smoothOfRelativeDimension_of_forall_field : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (g : ℕ), Smooth X.hom → (∀ (k : Type) [Field k] [Algebra R k], SmoothOfRelativeDimension g (Limits.pullback.snd X.hom (spMap (algebraMap R k)))) → SmoothOfRelativeDimension g X.hom := by
  intro R _ X g hs h
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have hn : ∀ x, n x = g := fun x => by
    let p : PrimeSpectrum R := X.hom x
    have hk := h p.asIdeal.ResidueField
    let t := spMap (algebraMap R p.asIdeal.ResidueField)
    obtain ⟨y, hy⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)) := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      exact Ideal.ker_algebraMap_residueField p.asIdeal
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n x)
    have h1 : SmoothOfRelativeDimension (n x) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) :=
      this.of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t) (hd x)
    have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) := by
      rw [← Limits.pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t)
      ⟨x, hW x⟩ y hy.symm
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FibreDim
