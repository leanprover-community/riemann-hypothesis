module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormsTwoCocycleCoboundaryOfRestrict
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.oneForms_twoCocycle_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict (FormExt.omExt F) G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) := by
  first | exact @GlobalTheory.CechDR.FormExt.coboundary_of_restrict_forms | exact GlobalTheory.CechDR.FormExt.coboundary_of_restrict_forms | (intros; apply GlobalTheory.CechDR.FormExt.coboundary_of_restrict_forms <;> assumption)
