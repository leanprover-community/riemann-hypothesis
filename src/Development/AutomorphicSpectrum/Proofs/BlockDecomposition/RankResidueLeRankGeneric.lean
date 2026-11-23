module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.Jp

theorem rank_residue_map_le_rank_fraction_map :
    ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L]
      [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O),
      (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  intro O L _ _ _ _ _ _ n T
  obtain ⟨S, τ, hdet⟩ := GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank (IsLocalRing.ResidueField O)
    (Fin n) (Fin n) _ (T.map (IsLocalRing.residue O)) le_rfl
  have hres : IsLocalRing.residue O (T.submatrix S τ).det =
      ((T.map (IsLocalRing.residue O)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hfrac : algebraMap O L (T.submatrix S τ).det =
      ((T.map (algebraMap O L)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hO : (T.submatrix S τ).det ≠ 0 := by
    intro h
    apply hdet
    rw [← hres, h, map_zero]
  have hL : ((T.map (algebraMap O L)).submatrix S τ).det ≠ 0 := by
    rw [← hfrac]
    intro h
    exact hO (IsFractionRing.injective O L (h.trans (map_zero _).symm))
  calc (T.map (IsLocalRing.residue O)).rank
      = ((T.map (algebraMap O L)).submatrix S τ).rank := by
        rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)),
          Fintype.card_fin]
    _ ≤ (T.map (algebraMap O L)).rank := Matrix.rank_submatrix_le _ _ _

end GlobalTheory.CompanionTheory.Jp
