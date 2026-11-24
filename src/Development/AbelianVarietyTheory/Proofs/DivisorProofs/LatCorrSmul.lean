module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_smul {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type}
    (_hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (hΛ : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := by

  have key : ∀ a : k', valuation k' a ≤ 1 → ∀ y ∈ Λ₂, a • y ∈ Λ₂ := fun a ha y hy =>
    Λ₂.smul_mem (⟨a, (Valuation.mem_integer_iff _ _).2 ha⟩ : 𝒪[k']) hy
  have hc₂ : valuation k' (c₂ : k') ≠ 0 := by simp
  set u : k' := (c₂⁻¹ : k'ˣ) * j c with hu
  have hu1 : valuation k' u = 1 := by
    rw [hu, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hc, inv_mul_cancel₀ hc₂]
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  have hu1' : valuation k' u⁻¹ = 1 := by rw [map_inv₀, hu1, inv_one]
  intro x
  rw [mem_smul_lat, mem_smul_lat, ← hΛ]
  have heq : (c₂⁻¹ : k'ˣ) • (fun d => j (x (cD d))) = u • (fun d => j (((c⁻¹ : kˣ) • x) (cD d))) := by
    funext d
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, map_mul, hu, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
  rw [heq]
  constructor
  · intro h
    have := key u⁻¹ hu1'.le _ h
    rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul] at this
  · exact key u hu1.le _

end GlobalTheory.PureMatch.Transport
