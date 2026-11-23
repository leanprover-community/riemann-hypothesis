module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerSquare

theorem memLp_column (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (y : X.G) : MemLp (fun x => ker X.Γ φ x y) 2 X.ν := by
  have hcont : Continuous fun x => ker X.Γ φ x y :=
    (hK X φ hφ).2.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  have hΩ : IsCompact (tsupport φ) := hφ.2
  have hbound := hS X φ B (tsupport φ) hφ hB hΩ (subset_tsupport φ) y
  have hμ : X.μ (tsupport φ)⁻¹ ≠ ⊤ := hΩ.inv.measure_lt_top.ne
  have hcnt : cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y ≠ ⊤ :=
    (hC X).1 _ (hΩ.inv.mul hΩ) y
  have hfin : ENNReal.ofReal B ^ 2 * X.μ (tsupport φ)⁻¹ *
      cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hμ.lt_top) hcnt.lt_top
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
    (by norm_num) (by norm_num) hcont.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  exact hbound.trans_lt hfin

theorem memLp_row (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (x : X.G) : MemLp (fun y => ker X.Γ φ x y) 2 X.ν := by
  obtain ⟨-, hcont, -, hadj, hconj, -⟩ := hK X φ hφ
  have hc : Continuous fun y => ker X.Γ φ x y :=
    hcont.comp (continuous_const.prodMk continuous_id)
  refine (memLp_column hK hC hS X (adj φ) hadj x).of_le hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [hconj y x, RCLike.norm_conj]

theorem kernel_rows_columns_square_integrable : KerBasic → CntBasic → ColSq → KernelL2RowsColumns := fun hK hC hS X φ hφ =>
  ⟨memLp_column hK hC hS X φ hφ, memLp_row hK hC hS X φ hφ⟩

end GlobalTheory.CompanionTheory.KerSquare
