module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultEqZeroOfInj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusion
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem sen_near_of_abc : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (D : ModPG R n (Vc k m)) {r : ℕ} (Dt : TopData n r) (N₁ N₂ : Lats k n m),
    ABC D Dt.w Dt.wst N₁ → ABC D Dt.w Dt.wst N₂ → ∀ i y, sen (D.γ i) (N₂ i) y ≠ 0 →
      ∃ j : ℤ, |j| ≤ Dt.sg l i ∧ sen (D.γ i) (N₁ i) (y + j) ≠ 0 := by
  intro k _ l n m _ _ _ R D r Dt N₁ N₂ h₁ h₂ i y hy
  obtain ⟨hL₁, hAB₁, hC₁⟩ := h₁
  obtain ⟨hL₂, hAB₂, hC₂⟩ := h₂
  have e12 := CloseTw.main D Dt.h Dt.w N₁ N₂ hL₁ hL₂ hAB₁ hAB₂ i
  have e21 := CloseTw.main D Dt.h Dt.w N₂ N₁ hL₂ hL₁ hAB₂ hAB₁ i
  have hle : N₂ i ≤ sh (-(sg l Dt.h i : ℤ)) (N₁ i) := by
    have h' := sh_le_sh (-(sg l Dt.h i : ℤ)) e21
    rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h'
  exact Compare.sen_compare R (D.γ i) (D.γ_semi i) (N₁ i) (N₂ i) (hL₁ i) (hL₂ i) (hC₁ i) (hC₂ i) _ e12 hle y hy

end GlobalTheory.Models
