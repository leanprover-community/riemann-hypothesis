module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem UpperTheory.V.ZK.Up.phi_zSeq {R B : Type} [CommRing R] [AddCommGroup B] {m l : ℕ} (hl : 0 < l)
    (φ : ∀ n : ℕ, grpH (GL (Fin n) R) m →+ B) (hφ : IsPrimH φ) (n t : ℕ) :
    ∃ c : ℤ, ∀ x : grpH (GL (Fin n) R) m,
      φ (lev l n t) (zSeq R hl x t) = ((l : ℤ) ^ t * (1 - l * c)) • φ n x := by
  induction t with
  | zero => exact ⟨0, fun x => by simp only [pow_zero, mul_zero, sub_zero, mul_one, one_smul]; rfl⟩
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (l : ℤ) ^ t - l * c * (l : ℤ) ^ t, fun x => ?_⟩
    have h : φ (lev l n (t + 1)) (zSeq R hl x (t + 1)) =
        φ (l * lev l n t) ((grpHMap (psi R l (lev l n t)) m).hom (zSeq R hl x t) -
          l ^ (t + 2) • (grpHMap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) m).hom
            (zSeq R hl x t)) := rfl
    rw [h, map_sub, map_nsmul, hφ.psi, hφ.stab, hc, ← natCast_zsmul, ← natCast_zsmul, ← sub_smul, smul_smul]
    congr 1
    push_cast
    ring

theorem UpperTheory.V.ZK.Up.zVal :
    UpperTheory.V.ZK.Up.ZVal := by
  intro R B _ _ m l ν hl hB φ hφ n t
  obtain ⟨c, hc⟩ := UpperTheory.V.ZK.Up.phi_zSeq hl φ hφ n t
  refine ⟨∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i, fun x => ?_⟩
  have hg : (∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i) * ((l : ℤ) ^ t * (1 - l * c)) =
      (l : ℤ) ^ t - ((l : ℤ) ^ t * c ^ ν) * ((l ^ ν : ℕ) : ℤ) := by
    have := geom_sum_mul_neg ((l : ℤ) * c) ν
    push_cast
    rw [mul_left_comm, this, mul_pow]
    ring
  rw [map_zsmul, hc, smul_smul, hg, sub_smul, mul_smul _ ((l ^ ν : ℕ) : ℤ), natCast_zsmul, hB, smul_zero, sub_zero,
    ← natCast_zsmul, Nat.cast_pow]
