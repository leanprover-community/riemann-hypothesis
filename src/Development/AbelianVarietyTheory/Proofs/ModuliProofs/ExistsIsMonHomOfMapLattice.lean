module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfComplementary
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsThetaSeriesApplyNeZeroOfLargeForm
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open LatticeHom in
theorem exists_isMonHom_of_map_lattice :
    ThetaUnifAV → Out.Laws → ∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hT hL P P' g u u' F hg hg' hF
  have key : ∀ (Q : Out.PolAV (Sp ℂ)) (w : HolUnif Q.A Q.L g), Q.g = g →
      ∃ (v : HolUnif Q.A Q.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : v.Λ → ℂ) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        v.IsAH Hm χ ∧ (∀ (k : ℕ) θ, v.IsThetaFn Hm χ k θ → ∃ s, v.IsFnPow k s θ) ∧
        (∀ (k : ℕ) s, ∃ θ, v.IsThetaFn Hm χ k θ ∧ v.IsFnPow k s θ) ∧ ∀ z, v.ex (T z) = w.ex z := by
    rintro Q w rfl
    obtain ⟨rig, hrig⟩ := Q.rigid
    obtain ⟨v, Hm, χ, -, hAH, -, -, -, -, hsec, -⟩ := hT Q rig hrig
    obtain ⟨T, hTv⟩ := exists_linearEquiv_of_holUnif hL.mulN Q w v
    exact ⟨v, Hm, χ, T, hAH, fun k θ h => ((hsec k).2 θ h).exists, fun k s => ((hsec k).1 s).exists, hTv⟩
  obtain ⟨v, Hm, χ, T, hAH, hsec, -, hv⟩ := key P u hg
  obtain ⟨v', Hm', χ', T', hAH', -, hfn, hv'⟩ := key P' u' hg'
  let F₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀ : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hΛ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := fun l hl => by
    obtain ⟨z, rfl⟩ := T.surjective l
    rw [hF₀, ← v'.ker, hv', u'.ker]
    refine hF z ?_
    rwa [← u.ker, ← hv, v.ker]
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.isLB P'.isLB hAH hAH'
    F₀ hΛ 4
  obtain ⟨f, hf, hfe⟩ := exists_isMonHom_of_complementary hL.ample P P' v v' hsec hfn F₀ hΛ d hd
  exact ⟨f, hf, fun z => by rw [← hv', ← hF₀, hfe, hv]⟩

end GlobalTheory
