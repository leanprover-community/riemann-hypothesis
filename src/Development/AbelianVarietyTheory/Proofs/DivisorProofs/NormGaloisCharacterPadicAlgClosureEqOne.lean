module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

namespace GlobalTheory.ExpFrame.CharUnit

open NumberField Polynomial in
private theorem le_one_of_forall_pow_le {a C : ℝ} (h : ∀ n : ℕ, a ^ n ≤ C) : a ≤ 1 := by
  by_contra ha
  push_neg at ha
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ha
  exact absurd (h n) (not_le.mpr hn)


open NumberField Polynomial in
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [NormedField K] (χ : Γ →* Kˣ) (hc : Continuous fun g => ((χ g : Kˣ) : K)) (g : Γ) :
    ‖((χ g : Kˣ) : K)‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hb : ∀ h : Γ, ∀ n : ℕ, ‖((χ h : Kˣ) : K)‖ ^ n ≤ C := fun h n => by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow]
    exact hC _ ⟨h ^ n, rfl⟩
  have h1 := le_one_of_forall_pow_le (hb g)
  have h2 := le_one_of_forall_pow_le (hb g⁻¹)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ g : Kˣ) : K)‖ := norm_pos_iff.mpr (χ g).ne_zero
  have : 1 ≤ ‖((χ g : Kˣ) : K)‖ := by
    by_contra hlt
    push_neg at hlt
    have := one_lt_inv₀ hpos |>.mpr hlt
    linarith
  linarith


open NumberField Polynomial in
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (χ : _root_.Formalism.ConjugateSelfDual.G E Ω →* (PadicAlgCl l)ˣ), Continuous (_root_.GlobalTheory.TripleGal.rk1 χ) → ∀ g, ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
  intro E Ω _ _ _ _ _ l _ χ hχ g
  refine _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact χ ?_ g
  have h := (Units.continuous_val.comp hχ).matrix_elem 0 0
  convert h using 1
  funext x
  simp [_root_.GlobalTheory.TripleGal.rk1]

end GlobalTheory.ExpFrame.CharUnit
