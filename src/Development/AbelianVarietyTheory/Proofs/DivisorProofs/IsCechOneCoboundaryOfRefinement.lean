module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Aesop.Frontend.Tactic
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.KS

namespace GlobalTheory.KS.Refine

theorem isCob_of_refine : ∀ {Y : Scheme.{0}} {I J : Type} (Uc : I → Y.Opens) (c : GlobalTheory.KS.C1 Uc),
    GlobalTheory.KS.IsCoc Uc c → ∀ (V : J → Y.Opens) (σ : J → I), (∀ p, V p ≤ Uc (σ p)) → (⨆ p, V p = ⊤) →
    ∀ (B : ∀ p, Γ(Y, V p)), (∀ p p', GlobalTheory.KS.rsT (c (σ p) (σ p')) (V p ⊓ V p') =
      GlobalTheory.KS.rsT (B p') (V p ⊓ V p') - GlobalTheory.KS.rsT (B p) (V p ⊓ V p')) → GlobalTheory.KS.IsCob Uc c := by
  intro Y I J Uc c hc V σ hV hVt B hB
  have hV' : ∀ p y, y ∈ V p → y ∈ Uc (σ p) := fun p y h => hV p h
  have cov : ∀ O : Y.Opens, O ≤ ⨆ p, O ⊓ V p := by
    intro O x hx
    have : x ∈ ⨆ p, V p := by rw [hVt]; trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩
  have glue : ∀ i, ∃ t : Γ(Y, Uc i), ∀ p, rsT t (Uc i ⊓ V p) =
      rsT (B p) (Uc i ⊓ V p) + rsT (c (σ p) i) (Uc i ⊓ V p) := by
    intro i
    refine exists_rsT_eq (fun p => Uc i ⊓ V p) (fun p => inf_le_left) (cov _) _ fun p p' => ?_
    have h1 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hB p p')
    have h2 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hc (σ p) (σ p') i)
    simp only [rsT_add, rsT_sub] at h1 h2 ⊢
    repeat
      first | rw [rsT_rsT] at h1 | rw [rsT_rsT] at h2 | rw [rsT_rsT]
      all_goals try (intro x hx; try simp only [TopologicalSpace.Opens.mem_inf] at hx ⊢; aesop)
    linear_combination h1 - h2
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun p => Uc i ⊓ Uc j ⊓ V p) (fun p => inf_le_left) (cov _) _ _ fun p => ?_
  have h1 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht i p)
  have h2 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht j p)
  have h3 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (hc (σ p) i j)
  simp only [rsT_add, rsT_sub] at h1 h2 h3 ⊢
  repeat
    first | rw [rsT_rsT] at h1 | rw [rsT_rsT] at h2 | rw [rsT_rsT] at h3 | rw [rsT_rsT]
    all_goals try (intro x hx; try simp only [TopologicalSpace.Opens.mem_inf] at hx ⊢; aesop)
  linear_combination h1 - h2 + h3

end GlobalTheory.KS.Refine
