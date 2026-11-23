module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory

namespace PSymplMinkowskiBox

theorem box_neg {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, |(A *ᵥ x) i| < a i) : ∀ i, |(A *ᵥ (-x)) i| < a i := by
  intro i
  rw [mulVec_neg, Pi.neg_apply, abs_neg]
  exact hx i

theorem box_convex {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    Convex ℝ {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} := by
  intro x hx y hy s t hs ht hst i
  have hlt : s • |(A *ᵥ x) i| + t • |(A *ᵥ y) i| ∈ Set.Iio (a i) :=
    convex_Iio (a i) (hx i) (hy i) hs ht hst
  rw [Set.mem_Iio, smul_eq_mul, smul_eq_mul] at hlt
  rw [mulVec_add, mulVec_smul, mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]
  calc |s * (A *ᵥ x) i + t * (A *ᵥ y) i| ≤ |s * (A *ᵥ x) i| + |t * (A *ᵥ y) i| := abs_add_le _ _
    _ = s * |(A *ᵥ x) i| + t * |(A *ᵥ y) i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ < a i := hlt

theorem volume_fundamentalDomain_basisFun (ι : Type) [Fintype ι] :
    volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by
  rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

end PSymplMinkowskiBox


open PSymplMinkowskiBox in
theorem SymplMinkowskiBox.proof (h1 : SymplBoxVolume.Statement) : SymplMinkowskiBox.Statement := by
  intro ι _ _ A a hdet ha hprod
  have hdet0 : A.det ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    exact zero_ne_one hdet
  set s : Set (ι → ℝ) := {x | ∀ i, |(A *ᵥ x) i| < a i} with hs
  have hvol : volume s = ENNReal.ofReal (2 ^ Fintype.card ι * ∏ i, a i) := by
    rw [hs, h1 ι A a hdet0 ha, hdet, div_one, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hP : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hbig : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) * 2 ^ Module.finrank ℝ (ι → ℝ) <
      volume s := by
    rw [volume_fundamentalDomain_basisFun, one_mul, Module.finrank_fintype_fun_eq_card, hvol,
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact lt_mul_of_one_lt_right hP hprod
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))
    infer_instance
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup)
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume)
    (fun y hy => box_neg A a y hy) (box_convex A a) hbig
  have hint : ∀ i, ∃ z : ℤ, (z : ℝ) = (x : ι → ℝ) i := by
    intro i
    obtain ⟨z, hz⟩ := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ (x : ι → ℝ)).mp x.2 i
    exact ⟨z, by simpa using hz⟩
  choose v hv using hint
  have hxv : intVec v = (x : ι → ℝ) := funext hv
  refine ⟨v, ?_, fun i => ?_⟩
  · rintro rfl
    apply hx0
    ext i
    rw [← hv i]
    simp
  · rw [hxv]
    exact hxs i

end GroundTheory.Heights₂.Heights
