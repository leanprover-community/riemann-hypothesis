module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem finite_dvr_limits_of_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X)
    (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt →
    ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀),
      spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro X Y₀ S q U s₀ t₀ gt hq hS _ hgt hfin z hz
  refine ((gt.finite_preimage_singleton ⟨z, hz⟩).image s₀).subset ?_
  rintro u ⟨V, K, _, _, _, _, _, _, y', z', x, h1, h2, rfl, rfl⟩

  have hr : Set.range z' ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map z'.continuous).mem_open U.isOpen hz
  set z'' := IsOpenImmersion.lift U.ι z' hr with hz''
  have hfac : z'' ≫ U.ι = z' := IsOpenImmersion.lift_fac _ _ _

  have hsq : x ≫ gt = spMap (algebraMap V K) ≫ z'' := by
    rw [← cancel_mono U.ι, Category.assoc, hgt, Category.assoc, hfac, h2]
  have hE : ValuativeCriterion.Existence gt :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed gt) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) gt).1
  obtain ⟨l, hl1, hl2⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z'', commSq := ⟨hsq⟩ }).exists_lift
  dsimp only at hl1 hl2

  have hU := IsSeparated.valuativeCriterion (q ≫ terminal.from S)
  have hsq' : (x ≫ s₀) ≫ (q ≫ terminal.from S) = spMap (algebraMap V K) ≫ terminal.from _ :=
    terminal.hom_ext _ _
  have hy : y' = l ≫ s₀ := by
    have := hU { R := V, K := K, i₁ := x ≫ s₀, i₂ := terminal.from _, commSq := ⟨hsq'⟩ }
    have e := this.elim ⟨y', h1, terminal.hom_ext _ _⟩
      ⟨l ≫ s₀, by change spMap (algebraMap V K) ≫ l ≫ s₀ = x ≫ s₀; rw [← Category.assoc, hl1], terminal.hom_ext _ _⟩
    exact congrArg CommSq.LiftStruct.l e
  refine ⟨l (IsLocalRing.closedPoint V), ?_, ?_⟩
  · show gt (l _) = _
    apply Subtype.ext
    change (l ≫ gt ≫ U.ι) _ = z' _
    rw [← Category.assoc, hl2, hfac]
  · rw [hy]; rfl

end GlobalTheory.UPel.HT.ES
