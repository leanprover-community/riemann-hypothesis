module

public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotProof

theorem mem_orbit_self {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x : X.left) :
    x ∈ orbit G X x := by
  have h1 : lift (1 : X ⟶ G) (𝟙 X) ≫ snd G X = 𝟙 X := lift_snd _ _
  have h2 : lift (1 : X ⟶ G) (𝟙 X) ≫ (γ[G, X] : G ⊗ X ⟶ X) = 𝟙 X := by
    have := one_smul (X ⟶ G) (𝟙 X)
    rwa [Hom.smul_def] at this
  have h1' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (snd G X).left = 𝟙 X.left := by
    rw [← Over.comp_left, h1, Over.id_left]
  have h2' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (γ[G, X] : G ⊗ X ⟶ X).left = 𝟙 X.left := by
    rw [← Over.comp_left, h2, Over.id_left]
  refine ⟨(lift (1 : X ⟶ G) (𝟙 X)).left x, ?_, ?_⟩
  · change (snd G X).left ((lift (1 : X ⟶ G) (𝟙 X)).left x) = x
    rw [← Scheme.Hom.comp_apply, h1']; rfl
  · rw [← Scheme.Hom.comp_apply, h2']; rfl

end GlobalTheory.CompanionTheory.FreeQuotProof
