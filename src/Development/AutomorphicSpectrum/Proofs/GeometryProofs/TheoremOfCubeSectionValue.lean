module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem exists_lin_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    {T : Over S} (x a : T ⟶ G) (m : ℕ) (hx : x ^ m = 1) :
    ∃ v : FG L.L T.left, (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U),
        v.sum U h = h (x * a ^ m).left * (h (a ^ m).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left) ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → ρ ≫ a = 1 → v.v ρ.left z J = 1 := by
  obtain ⟨t₂, ht₂, v₂⟩ := exists_cubN c (1 : T ⟶ G) a x m
  obtain ⟨t₁, ht₁, v₁⟩ := exists_cubN c (1 : T ⟶ G) x a m
  refine ⟨FG.mul ⟨Fin 8, _, _, t₂, ht₂⟩ (FG.inv ⟨Fin 8, _, _, t₁, ht₁⟩), fun U _ h => ?_, fun T' ρ z J hJ hρ => ?_⟩
  · rw [FG.sum_mul, FG.sum_inv]
    simp only [FG.sum, Fin.prod_univ_succ, Fin.prod_univ_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, hx,
      _root_.one_mul, _root_.mul_one, mul_comm a x, mul_comm (a ^ m) x]
    apply Additive.ofMul.injective
    simp [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · rw [FG.v_mul hJ, FG.v_inv]
    show val t₂ ρ.left z J * (val t₁ ρ.left z J)⁻¹ = 1
    rw [v₂ T' ρ z J hJ, v₁ T' ρ z J hJ, hρ, (isCub_cubV c hJ).N_one]
    have : cubN (cubV c z J) m (ρ ≫ (1 : T ⟶ G)) 1 (ρ ≫ x) = 1 :=
      Finset.prod_eq_one fun _ _ => (isCub_cubV c hJ).face₂ _ _ |>.symm ▸ rfl
    rw [this]
    simp

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
