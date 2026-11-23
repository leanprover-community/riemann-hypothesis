module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendsTaylorPowerSeriesRing
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

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin

theorem _root_.GlobalTheory.T.derivation_extends_taylorPowerSeriesRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → (∀ a r, ds a (inc r) = 0) → ∀ (d : Derivation ℤ A A) (D : Derivation ℤ R R), (∀ r, d (inc r) = inc (D r)) → ∃ dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R), (∀ r, dΩ (MvPowerSeries.C r) = MvPowerSeries.C (D r)) ∧ ∀ f, dΩ (taylor ev (fun i => ⇑(ds i)) f) = taylor ev (fun i => ⇑(ds i)) (d f) := by
  first | exact @GlobalTheory.FormalOrigin.Extend.derivation_extends | exact GlobalTheory.FormalOrigin.Extend.derivation_extends | (intros; apply GlobalTheory.FormalOrigin.Extend.derivation_extends <;> assumption)
