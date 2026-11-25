module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
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

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ChowHt

namespace PositivityTheory.UnitarySelfGeneration

def ChowFormHeight : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (d N m δ : ℕ) (g : Matrix (Fin N) (Fin m) K)
    (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span K (Set.range g.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) →
    ConjCompat A → ∀ (y : Fin N → Ω) (Z : GlobalTheory.ZH.RatModel (𝓞 K) Ω),
    Z.IsCl (fun k => ∑ j, algebraMap K Ω (g j k) * y j) → GlobalTheory.IsArithVar Z.s d →
    ∀ (Φ : MvPolynomial (Fin (d + 1) × Fin N) K), IsChowFormInt (GlobalTheory.CompHt.coneIdeal K y) d δ Φ →
    ∀ (H : LB Z.Z) (hH : H.IsLB) (e : H.ι → Ω), Z.GenTriv H e → ∀ (s : Fin m → H.Sec),
    (∀ k, Z.HasVal e (s k) (∑ j, algebraMap K Ω (g j k) * y j)) →
    ∀ (hs : ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ)
      (hdet : ∀ σ, (Mt σ).det ≠ 0)
      (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U),
      (∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 =
        GlobalTheory.Adelic.archSize (A σ) x ^ 2) →
      (GlobalTheory.HermLB.fs Z.s hH s hs Mt hdet hc).IsSelfInter ((Module.finrank ℚ K : ℝ) * formHeight δ g A Φ)

end PositivityTheory.UnitarySelfGeneration
