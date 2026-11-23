module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.PlaceShiftModel

open NumberField IsDedekindDomain GlobalTheory.CompHt GlobalTheory.HTLat

variable {E : Type} [Field E] [NumberField E] {ℓ : ℕ} [Fact ℓ.Prime]

theorem norm_le_one (τ : E →+* ℂ_[ℓ]) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  rw [← algebraMap_embO (PadicComplexInt.integers ℓ) τ a]
  exact (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 (Subtype.prop _)

theorem norm_ell : ‖(ℓ : ℂ_[ℓ])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[ℓ] ℂ_[ℓ]), norm_algebraMap']
  exact Padic.norm_p_lt_one

end GlobalTheory.FlatCM.PlaceShiftModel

end
