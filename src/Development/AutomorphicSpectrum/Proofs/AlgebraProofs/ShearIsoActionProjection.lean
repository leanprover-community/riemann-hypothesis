module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section

namespace GlobalTheory.CompanionTheory.FreeQuotProof

theorem action_eq_fst_smul_snd {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] :
    (γ[G, X] : G ⊗ X ⟶ X) = (fst G X) • (snd G X) := by
  rw [CategoryTheory.Hom.smul_def, lift_fst_snd, Category.id_comp]

theorem exists_iso_swap_action_snd : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], ∃ σ : G ⊗ X ⟶ G ⊗ X, IsIso σ ∧ σ ≫ snd G X = γ[G, X] ∧ σ ≫ γ[G, X] = snd G X := by
  intro S G X _ _
  have hγ : (γ[G, X] : G ⊗ X ⟶ X) = fst G X • snd G X := GlobalTheory.CompanionTheory.FreeQuotProof.action_eq_fst_smul_snd G X
  obtain ⟨σ, h₁, h₂⟩ : ∃ σ : G ⊗ X ⟶ G ⊗ X,
      σ ≫ snd G X = fst G X • snd G X ∧ σ ≫ fst G X = (fst G X)⁻¹ :=
    ⟨lift (fst G X)⁻¹ (fst G X • snd G X), lift_snd _ _, lift_fst _ _⟩
  have h₃ : σ ≫ (fst G X • snd G X) = snd G X := by
    rw [CategoryTheory.ModObj.comp_smul, h₂, h₁, inv_smul_smul]
  have h₄ : σ ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, h₂, CategoryTheory.Hom.inv_def, ← Category.assoc, h₂,
        ← CategoryTheory.Hom.inv_def, inv_inv, Category.id_comp]
    · rw [Category.assoc, h₁, h₃, Category.id_comp]
  exact ⟨σ, ⟨σ, h₄, h₄⟩, by rw [hγ]; exact h₁, by rw [hγ]; exact h₃⟩

end GlobalTheory.CompanionTheory.FreeQuotProof
