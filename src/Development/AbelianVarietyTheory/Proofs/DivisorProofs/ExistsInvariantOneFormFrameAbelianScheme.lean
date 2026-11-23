module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantOneFormsAbelianSchemeFiniteProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInvariantOneFormsAffineOpenAbelianSchemeEqToStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvFormBC

open GlobalTheory.InvForm

theorem isBaseChange_invForm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) := by
  intro R _ A _ g hab hdim U
  let f := evForm A.hom U ∘ₗ (InvForm A).subtype
  let L := f.liftBaseChange (Sec A.hom U.unop.1)
  have hs : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top R A g hab hdim U]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp [L, f]⟩
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_retraction_differentials_invariantOneForms_affine R A g hab hdim U
  have hl : ∀ x, r (L x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      have : L (b ⊗ₜ w) = b • evForm A.hom U w.1 := by simp [L, f]
      rw [this, map_smul, hr, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective L := fun x y h ↦ by rw [← hl x, ← hl y, h]
  have hb : Function.Bijective L := ⟨hi, hs⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective L hb) fun x ↦
    show L (1 ⊗ₜ x) = f x from (LinearMap.liftBaseChange_tmul _ f 1 x).trans (one_smul _ _)

theorem exists_invariant_frame : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (j : M →ₗ[R] GlobForm A.hom), Module.Finite R M ∧ Module.Projective R M ∧ ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ j) := by
  intro R _ A _ g hab hdim
  have hbc := isBaseChange_invForm R A g hab hdim
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.invariantOneForms_abelianScheme_finite_projective R A g hab hdim hbc
  exact ⟨InvForm A, inferInstance, inferInstance, (InvForm A).subtype, hfin, hproj, hbc⟩

end GlobalTheory.InvFormBC
