module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BanachHol
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamLocal
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
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ}
  {sL : PX m n →ₗ[ℂ] (GR n → ℂ)} {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ}
  {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem lam_cont (hBH : BanachHol) (hFL : FactorL) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) {B : Set ℂ} (hB : IsOpen B) {w : ℂ} (hw : w ∈ B) (F : ℂ → G → ℂ)
    (hFc : ContinuousOn (fun y : ℂ × G => F y.1 y.2) (B ×ˢ univ)) (hFh : ∀ g, DifferentiableOn ℂ (F · g) B)
    (hFi : ∀ z ∈ B, ∀ γ ∈ Γ, ∀ g, F z (γ * g) = F z g) : ContinuousAt (fun z => l (F z)) w := by
  obtain ⟨C, hCc, hCb⟩ := hG.Λbd l hl
  obtain ⟨L, hL⟩ := hFL G (invSub Γ) l C hCc (fun F hF => hF.1)
    (fun a F hF F' hF' => hG.Λadd l hl a F F' hF.1 hF'.1 hF.2 hF'.2)
    (fun F hF M hM => hCb F M hF.1 hF.2 hM)
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hFcont : ∀ z ∈ B, Continuous (F z) := by
    intro z hzB
    exact hFc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hzB, mem_univ g⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := hBH C B (fun z x => F z x) hB
    (hFc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))
    (fun x => hFh x)
  have hfeq : ∀ z ∈ B, l (F z) = L (Φ z) := by
    intro z hzB
    have hmem : F z ∈ invSub Γ := ⟨hFcont z hzB, hFi z hzB⟩
    rw [hL (F z) hmem (hFcont z hzB)]
    congr 1
    ext x
    rw [hΦ z hzB x]
    rfl
  have hd : DifferentiableOn ℂ (fun z => l (F z)) B :=
    (L.differentiable.comp_differentiableOn hΦd).congr hfeq
  exact (hd.differentiableAt (hB.mem_nhds hw)).continuousAt

end PositivityTheory.Rg.Sw.AbsSt.Vac
