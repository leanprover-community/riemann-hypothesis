module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIsoStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CosieveRel

theorem serre_of_equiv {R : Type} [CommRing R] (𝒮 : Serre.{1} R) {M N : Type 1} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : 𝒮.P M) : 𝒮.P N := by
  refine 𝒮.mid M N PUnit.{2} e.toLinearMap 0 ?_ h (𝒮.zero PUnit.{2} inferInstance)
  intro y
  exact iff_of_true (Subsingleton.elim _ _) ⟨e.symm y, e.apply_symm_apply y⟩

theorem serre_union : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (W : ι → ObjectProperty C) (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') (𝒮 : Serre.{1} R) (n : ℕ),
    (∀ p q, p + q = n → 𝒮.P ((cechH F W q).cx.H p)) → 𝒮.P (HU F (fun T => ∃ α, W α T) n) := by
  intro R _ C _ F ι W hW 𝒮 n h
  have hle : ∀ α, W α ≤ (fun T => ∃ β, W β T : ObjectProperty C) := fun α T hT => ⟨α, hT⟩
  refine GlobalTheory.T.serre_class_of_cech_spectral_sequence ((ObjectProperty.ι (fun T => ∃ β, W β T : ObjectProperty C)) ⋙ F)
    (fun α T => W α T.obj) (fun α => by
      intro T T' f hT
      exact hW α f.hom hT T'.property) (fun T => T.property) 𝒮 n ?_
  intro p q hpq
  obtain ⟨e⟩ := GlobalTheory.T.cech_cohomology_full_subcategory_iso F (fun T => ∃ β, W β T : ObjectProperty C) W hle q p
  exact serre_of_equiv 𝒮 e.symm (h p q hpq)

end GlobalTheory.CompanionTheory.CosieveRel
