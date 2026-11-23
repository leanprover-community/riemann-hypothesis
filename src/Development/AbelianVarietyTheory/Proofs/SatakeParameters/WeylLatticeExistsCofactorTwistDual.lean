module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwapStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeightStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeightStatement
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem applyWord_hw_cofRel (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) (w : List (Fin (m + 1) × Fin (m + 1) × ℕ)) :
    (∃ μ : Fin (m + 1) → ℕ, IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (applyWord R w (hw R le_rfl ν)) μ) ∧
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (applyWord R w (hw R le_rfl ν)) g := by
  induction w with
  | nil => exact ⟨⟨_, hwRowWeight R _ _ le_rfl ν hν⟩, GlobalTheory.T.exists_cofactorTwist_highestWeight R m ν hν h0⟩
  | cons x w ih =>
    obtain ⟨a, b, k⟩ := x
    obtain ⟨⟨μ, hμ⟩, g, hg, hrel⟩ := ih
    have hstep : applyWord R ((a, b, k) :: w) (hw R le_rfl ν) =
        rowDiv R a b k (applyWord R w (hw R le_rfl ν)) := rfl
    rw [hstep]
    obtain ⟨h1, h2⟩ := GlobalTheory.T.isWeightedHomogeneous_div_and_diag_eq_choose_smul R _ _ μ _ hμ
    refine ⟨h1 a b k, ?_⟩
    by_cases hab : a = b
    · subst hab
      refine ⟨((μ a).choose k) • g, nsmul_mem hg _, ?_⟩
      rw [h2 a k]
      unfold CofRel at hrel ⊢
      rw [map_nsmul, ← hrel, mul_smul_comm]
    · exact ⟨_, zsmul_mem (weylRowDivStable R _ _ le_rfl _ b a k g hg) _, GlobalTheory.T.cofactorTwistRelation_rowDiv_swap R m ν a b k _ g hab hrel⟩

theorem weyl_exists_cofRel : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ν (Fin.last m) = 0 → ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl ν,
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν hν h0 f hf
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact (applyWord_hw_cofRel R m ν hν h0 w).2
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g, hg, hr⟩ := hx
    obtain ⟨g', hg', hr'⟩ := hy
    refine ⟨g + g', add_mem hg hg', ?_⟩
    unfold CofRel at hr hr' ⊢
    rw [map_add (f := _), ← hr, ← hr', mul_add]
  | smul c x _ hx =>
    obtain ⟨g, hg, hr⟩ := hx
    refine ⟨c • g, Submodule.smul_mem _ c hg, ?_⟩
    unfold CofRel at hr ⊢
    rw [map_smul, ← hr, mul_smul_comm]

end GlobalTheory.ValCmp
