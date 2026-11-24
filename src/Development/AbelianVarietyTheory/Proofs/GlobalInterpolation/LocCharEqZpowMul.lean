module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.LocCharVal

theorem isUnit_redP {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (hb : P.valuation E b = 1) : IsUnit (redP P b) := by
  have h1 : Formalism.L2.Col.IntAt P b := (GlobalTheory.CharVal.intAt_iff _).2 hb.le
  have h2 : Formalism.L2.Col.IntAt P b⁻¹ := (GlobalTheory.CharVal.intAt_iff _).2 (by rw [map_inv₀, hb]; simp)
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have h3 := reduction_mul h1 h2
  rw [mul_inv_cancel₀ hb0] at h3
  have h4 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [h4] at h3
  exact IsUnit.of_mul_eq_one _ h3.symm

theorem locChar_eq_zpow_mul : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), P.valuation E (q : E) = WithZero.exp (-1 : ℤ) → a ≠ 0 → ∃ (z : ℤ) (ζ : Kˣ), IsOfFinOrder ζ ∧ LocE.locChar q cq χ a = cq ^ z * (ζ : K) := by
  intro E K _ _ _ P q cq χ a hq ha
  have hv : P.valuation E a ≠ 0 := by simpa using ha
  have hex : ∃ z : ℤ, IsUnit (redP P (a / (q : E) ^ z)) := by
    refine ⟨-WithZero.log (P.valuation E a), isUnit_redP P _ ?_⟩
    rw [map_div₀, map_zpow₀, hq, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log hv, hv]
  have hu : IsUnit (redP P (a / (q : E) ^ LocE.vP P q a)) := Classical.epsilon_spec hex
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨LocE.vP P q a, χ hu.unit, MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite _), ?_⟩
  unfold LocE.locChar LocE.unitV
  rw [dite_eq_left hu]

end GlobalTheory.LocCharVal
