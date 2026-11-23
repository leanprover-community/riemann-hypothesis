module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
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
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.LbChain

theorem lbIso_chain : ∀ {A₀ X₁ G₁ G₂ Z P Q : Scheme.{0}} (LA : LB A₀) (L₁ : LB G₁) (L₂ : LB G₂) (LZ : LB Z) (LQ : LB Q) (a : X₁ ⟶ A₀) (a' : A₀ ⟶ X₁) (f₁ : X₁ ⟶ G₁) (f₂ : G₁ ⟶ G₂) (f₃ : G₂ ⟶ Z) (ψ : P ⟶ Z) (π : P ⟶ Q) (t : A₀ ⟶ P), LA.IsLB → L₁.IsLB → L₂.IsLB → LZ.IsLB → LQ.IsLB → a' ≫ a = 𝟙 A₀ → LBIso (LA.pull a) (L₁.pull f₁) → LBIso L₁ (L₂.pull f₂) → LBIso L₂ (LZ.pull f₃) → LBIso (LZ.pull ψ) (LQ.pull π) → t ≫ ψ = a' ≫ f₁ ≫ f₂ ≫ f₃ → LBIso LA (LQ.pull (t ≫ π)) := by
  intro A₀ X₁ G₁ G₂ Z P Q LA L₁ L₂ LZ LQ a a' f₁ f₂ f₃ ψ π t hA h₁ h₂ hZ hQ hs e₁ e₂ e₃ e₄ ht
  have E0 : LBIso LA (LA.pull (a' ≫ a)) :=
    LBIso.chartPull (chartPullUnpull LA (a' ≫ a) hs) (chartPullId _) (PolBaseChange.lbIso_refl (pull_isLB hA _))
  have E1 : LBIso (LA.pull (a' ≫ a)) (L₁.pull (a' ≫ f₁)) := GlobalTheory.GenSpread.lbIso_pull_comp a' rfl rfl e₁
  have E2 : LBIso (L₁.pull (a' ≫ f₁)) (L₂.pull (a' ≫ f₁ ≫ f₂)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₂ (a' ≫ f₁) (by simp)
  have E3 : LBIso (L₂.pull (a' ≫ f₁ ≫ f₂)) (LZ.pull (t ≫ ψ)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₃ (a' ≫ f₁ ≫ f₂) (by rw [ht]; simp)
  have E4 : LBIso (LZ.pull (t ≫ ψ)) (LQ.pull (t ≫ π)) := GlobalTheory.GenSpread.lbIso_pull_comp t rfl rfl e₄
  exact LBIso.trans hA (pull_isLB hA _) (pull_isLB hQ _) E0
    (LBIso.trans (pull_isLB hA _) (pull_isLB h₁ _) (pull_isLB hQ _) E1
      (LBIso.trans (pull_isLB h₁ _) (pull_isLB h₂ _) (pull_isLB hQ _) E2
        (LBIso.trans (pull_isLB h₂ _) (pull_isLB hZ _) (pull_isLB hQ _) E3 E4)))

end GlobalTheory.LbChain
