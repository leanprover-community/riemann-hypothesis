module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

theorem UpperTheory.Gal.Int.Geo.Cut.fEtCut :
    UpperTheory.Gal.Int.Geo.Cut.FEtCut := by
  intro Y' Y T' T j s t i s' t' d hj hr hst hs
  haveI := hj.op
  haveI := hr.op
  have hpre : s ⁻¹ᵁ j.opensRange = i.opensRange := by
    apply SetLike.coe_injective
    change s ⁻¹' Set.range j = Set.range i
    rw [hr.rng]
    ext x
    exact ⟨fun h => ⟨h, hst x h⟩, fun h => h.1⟩
  have pb : IsPullback s' i j s := IsOpenImmersion.isPullback s' i j s hr.es.symm hpre
  obtain ⟨hfin, het, hcard⟩ := hs
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) pb.flip hfin,
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) pb.flip het, ?_⟩
  intro K _ _ x
  rw [← hcard K (x ≫ j)]
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ i, by rw [Category.assoc, ← pb.w, ← Category.assoc, y.2]⟩
      invFun := fun z => ⟨pb.lift x z.1 z.2.symm, pb.lift_fst _ _ _⟩
      left_inv := fun y => Subtype.ext (pb.hom_ext (by simp [y.2]) (by simp))
      right_inv := fun z => Subtype.ext (pb.lift_snd _ _ _) }
