module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfComplementary
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsThetaSeriesApplyNeZeroOfLargeForm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open LatticeHom in
theorem existsUnique_isMonHom_of_map_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃! f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hlaws _ _ hT P P' L L' u u' F hF
  obtain ⟨rig, hrig⟩ := P.8
  obtain ⟨rig', hrig'⟩ := P'.8
  obtain ⟨v, Hm, χ, Ef, hAH, -, -, -, -, hth, -⟩ := hT P rig hrig
  obtain ⟨v', Hm', χ', Ef', hAH', -, -, -, -, hth', -⟩ := hT P' rig' hrig'
  obtain ⟨T, hTu⟩ := exists_linearEquiv_of_holUnif hlaws.6 P u v
  obtain ⟨T', hTu'⟩ := exists_linearEquiv_of_holUnif hlaws.6 P' u' v'
  set F₀ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) :=
    T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀T : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hF₀ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := by
    intro l hl
    have h1 : u.ex (T.symm l) = 1 := by
      rw [← hTu, T.apply_symm_apply]
      exact (v.5 l).2 hl
    have h2 : u'.ex (F (T.symm l)) = 1 := (u'.5 _).2 (hF _ ((u.5 _).1 h1))
    refine (v'.5 _).1 ?_
    have h3 : F₀ l = T' (F (T.symm l)) := by simp [F₀]
    rw [h3, hTu']
    exact h2
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.7 P'.7
    hAH hAH' F₀ hF₀ 4
  obtain ⟨f, hf, hfF⟩ := exists_isMonHom_of_complementary hlaws.3 P P' v v'
    (fun k θ hθ => ((hth k).2 θ hθ).exists) (fun k s => ((hth' k).1 s).exists) F₀ hF₀ d hd
  have hfu : ∀ z, u'.ex (F z) = u.ex z ≫ f := by
    intro z
    rw [← hTu' (F z), ← hTu z, ← hfF, hF₀T]
  refine ⟨f, ⟨hf, hfu⟩, ?_⟩
  rintro f' ⟨-, hf'⟩
  have := P.5
  have : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g P.A.hom
  have : IsReduced P.A.left := isReduced_of_smooth_complex P.A.left P.A.hom inferInstance
  have := P'.3
  have : IsSeparated P'.A.hom := inferInstance
  apply ComplexPoints.over_hom_ext_of_complexPoints
  intro x
  obtain ⟨z, rfl⟩ := u.3 x
  rw [← hf' z, hfu z]

end GlobalTheory
