module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) (X : Matrix A D k), IsPrimFrame (stdLat k D) X → ∃ u ∈ KO k D, X = X0 k σ * (invT u).val := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ X hX
  obtain ⟨R, hR, hXR⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hX
  let X' : Matrix A D 𝒪[k] := Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩
  let R' : Matrix D A 𝒪[k] := Matrix.of fun i j => ⟨R i j, hR i j⟩
  have h1 : X' * R' = 1 := by
    apply Matrix.map_injective (f := algebraMap 𝒪[k] k) Subtype.val_injective
    show (X' * R').map (algebraMap 𝒪[k] k) = (1 : Matrix A A 𝒪[k]).map (algebraMap 𝒪[k] k)
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hXR
  let ρ := IsLocalRing.residue 𝒪[k]
  have h2 : X'.map ρ * R'.map ρ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : (X'.map ρ).rank = Fintype.card A := by
    refine le_antisymm (Matrix.rank_le_card_height _) ?_
    have := Matrix.rank_mul_le_left (X'.map ρ) (R'.map ρ)
    rwa [h2, Matrix.rank_one] at this
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ _).1 h3
  choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
  let C : Matrix D D 𝒪[k] := Matrix.of fun r j =>
    Sum.elim (fun i => X' i j) (fun i => l ((invT h).val (σ (Sum.inr i)) j)) (σ.symm r)
  have h4 : ρ.mapMatrix C = (invT h).val := by
    ext r j
    obtain ⟨i | i, rfl⟩ := σ.surjective r
    · have := congrFun (congrFun hh i) j
      rw [frameMatrixFirstColumnBlock_mul_apply] at this
      simpa [C] using this
    · simp [C, ρ, hl]
  have hK : IsUnit C := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    rw [show (IsLocalRing.residue 𝒪[k]).mapMatrix C = _ from h4]
    exact (invT h).det_ne_zero
  obtain ⟨w, hw⟩ := hK
  refine ⟨invT (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w), invT_mem_KO ⟨w, rfl⟩, ?_⟩
  rw [invT_invT]
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply]
  show _ = ((w.val (σ (Sum.inl i)) j : 𝒪[k]) : k)
  rw [hw]
  simp [C, X']
