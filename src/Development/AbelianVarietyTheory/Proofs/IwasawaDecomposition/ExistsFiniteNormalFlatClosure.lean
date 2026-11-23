module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
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

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem exists_normalisation_of_locallyClosed : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (P U : Scheme.{0}) (s : P ⟶ Sp O) (Ω : P.Opens) (j : U ⟶ Ω.toScheme), IsProjOver s → IsClosedImmersion j → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U → Flat (j ≫ Ω.ι ≫ s) → ∃ (Z' : Scheme.{0}) (ν : Z' ⟶ P) (e : U ⟶ Z'), IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsProjOver (ν ≫ s) ∧ Flat (ν ≫ s) ∧ IsPullback e j ν Ω.ι ∧ Dense (Set.range e) := by
  intro O _ _ _ P U s Ω j hs _ hn hfl
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).mp hs).1
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (j ≫ Ω.ι)
  obtain ⟨h, eh⟩ : ∃ h : U ⟶ P, h = j ≫ Ω.ι := ⟨_, rfl⟩
  have : QuasiCompact h := eh ▸ inferInstance
  have : IsSeparated h := eh ▸ inferInstance
  have : LocallyOfFiniteType h := eh ▸ inferInstance
  have : Flat (h ≫ s) := by rw [eh, Category.assoc]; exact hfl
  have : IsFinite h.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of O) h s
      fun x hx => charZero_residueField_of_flat (h ≫ s) hx
  have : Flat (h.toNormalization ≫ h.fromNormalization ≫ s) := by
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc]
    infer_instance
  exact ⟨h.normalization, h.fromNormalization, h.toNormalization, inferInstance,
    IsNormalScheme.pred _, isProjOver_comp_of_isFinite _ hs, flat_normalization h _,
    isPullback_toNormalization_of_mono j Ω.ι h eh, h.toNormalization.denseRange⟩

end GlobalTheory.GraphClosure
