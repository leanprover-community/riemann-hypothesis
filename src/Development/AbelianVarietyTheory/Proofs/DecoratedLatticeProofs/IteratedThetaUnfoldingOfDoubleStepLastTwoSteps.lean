module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.IterProof

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem rTrans_lift {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (s : Step ψ V V₀ W W₀ ρ σ) (G : GA D W → ℂ) (Φ : WO V W → ℂ)
    (g : GA D V) : rTrans g (s.lift G Φ) = s.lift G (s.om (g, 1) Φ) := by
  funext x
  have key : ∀ h, s.om (x * g, h) Φ = s.om (x, h) (s.om (g, 1) Φ) := by
    intro h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [rTrans, Step.lift, liftS_apply, key]

end GlobalTheory.Unf.IterProof


open GlobalTheory.Unf.IterProof in
theorem GlobalTheory.Unf.iter_of_doubleStep_lastLaw : ∀ D : D7, DoubleStep D → LastLaw D → IT D := by
  intro D hD hL ψ T ρ B c
  induction c with
  | @last B t =>
    intro Φ F φ g hΦ hF hφ _
    show B.per ψ φ (rTrans g (t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ.2) Φ.1)) =
      t.Q φ (t.s.om (g, 1) Φ.1) Φ.2 F
    rw [rTrans_lift]
    exact hL ψ T B t φ _ Φ.2 F hφ hF (t.s.weil.om_pres _ _ hΦ.1) hΦ.2
  | @step σ B J B' s₁ s₂ l vL c ih =>
    intro Φ F φ g hΦ hF hφ hR
    obtain ⟨hR₁, hR₂, hR₃⟩ := hR
    obtain ⟨hΦ₁, hΦ₂, hΦ₃⟩ := hΦ
    obtain ⟨hcont, f₁, h₁, h₂⟩ := hD ψ σ B J B' s₁ s₂ l vL Φ.1 Φ.2.1 φ (c.down Φ.2.2 F) g hΦ₁ hΦ₂ hφ hR₂ hR₁
    refine ⟨f₁, fun a b => B'.per ψ (Chain.hand s₁ s₂ l vL Φ.1 Φ.2.1 φ g a b) (rTrans b (c.down Φ.2.2 F)), h₁,
      fun a => ⟨h₂ a, fun b => ?_⟩⟩
    exact ih Φ.2.2 F _ b hΦ₃ hF (hcont a b) hR₃
