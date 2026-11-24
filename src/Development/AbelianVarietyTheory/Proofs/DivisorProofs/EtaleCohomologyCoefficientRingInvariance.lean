module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionComparisonStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpecStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearResolutionMapCohomologyEqZeroOfKillStatement
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem SemiMap.sub_op {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ ρ' : SemiMap I J)
    (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (ρ.sub ρ').op.app E n x = ρ.op.app E n x - ρ'.op.app E n x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ').1 E n α
  have hsub : (ρ.sub ρ').IsImage α.1 (β - β').1 := by
    intro p s h U x
    rw [show (β - β').1 = β.1 - β'.1 from rfl, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 β.1 β'.1 p s h U x).2.1, hβ p s h U x,
      hβ' p s h U x]
    rfl
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R _).2 E n α _ hsub, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n α β hβ,
    (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ').2 E n α β' hβ', CohomologyClass.mk_sub]

theorem a8 : A8 := by
  intro R S _ _ φ E F n
  obtain ⟨ρ₀, h₀, hb⟩ := GlobalTheory.T.restrictScalars_resolution_comparison R S φ F
  have hz := GlobalTheory.T.semilinearResolutionMap_cohomology_eq_zero_of_kill S R F ((restr φ).obj F) ((restrMap φ F).sub ρ₀) (fun U a => by
    change (restrMap φ F).app U 0 _ - ρ₀.app U 0 _ = 0
    rw [GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec R S φ F U a, h₀ U a, sub_self])
  have he : restrH φ E F n = ρ₀.op.app E n := by
    ext x
    have := hz E n x
    rw [SemiMap.sub_op] at this
    exact sub_eq_zero.mp this
  rw [he]
  exact hb E n

end GlobalTheory.EtC
