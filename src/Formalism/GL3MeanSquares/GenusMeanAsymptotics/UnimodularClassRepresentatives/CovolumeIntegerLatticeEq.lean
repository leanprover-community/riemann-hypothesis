module

public import Formalism.HermitianLattices.StatementMass
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem nrComplexPlaces_eq_fDeg (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    InfinitePlace.nrComplexPlaces K = Formalism.HermitianLatticesTheory.fDeg K := by
  have h0 : InfinitePlace.nrRealPlaces K = 0 := by
    classical
    unfold InfinitePlace.nrRealPlaces
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h0, zero_add]

theorem finrank_eq_two_fDeg (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
  rw [← nrComplexPlaces_eq_fDeg hK]
  have h0 : InfinitePlace.nrRealPlaces K = 0 := by
    classical
    unfold InfinitePlace.nrRealPlaces
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  have := InfinitePlace.card_add_two_mul_card_eq_rank K
  omega

theorem vInv_pos (K : Type) [Field K] [NumberField K] : 0 < Formalism.HermitianLatticesTheory.vInv K := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have hd : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  exact div_pos (Real.rpow_pos_of_pos hd _) two_pos

theorem covolume_integerLattice_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| =
      Formalism.HermitianLatticesTheory.vInv K ^ Formalism.HermitianLatticesTheory.fDeg K := by
  rw [nrComplexPlaces_eq_fDeg hK]
  unfold Formalism.HermitianLatticesTheory.vInv
  have hpos : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have hf : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [div_pow, ← Real.rpow_natCast (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K))),
    ← Real.rpow_mul (abs_nonneg _), Real.sqrt_eq_rpow]
  have e : (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K) * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) = 1 / 2 := by
    field_simp
  rw [e, inv_pow]
  ring

end Formalism.HermitianLattices.Ext.L3
