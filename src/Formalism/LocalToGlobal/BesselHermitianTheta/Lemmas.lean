module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Const

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem Rder_const (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) :
    Rder θ V τ Z (fun _ => c) = fun _ => 0 := by
  funext g
  unfold Rder
  simp

theorem RderC_const (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) :
    RderC θ V τ Z (fun _ => c) = fun _ => 0 := by
  funext g
  unfold RderC
  simp [Rder_const]

theorem foldr_const (l : List ((GA D V → ℂ) → (GA D V → ℂ)))
    (hl : ∀ f ∈ l, ∀ c : ℂ, ∃ c' : ℂ, f (fun _ => c) = fun _ => c') (c : ℂ) :
    ∃ c' : ℂ, l.foldr (fun f acc => f acc) (fun _ => c) = fun _ => c' := by
  induction l with
  | nil => exact ⟨c, rfl⟩
  | cons f l ih =>
    obtain ⟨c1, h1⟩ := ih (fun g hg => hl g (by simp [hg]))
    obtain ⟨c2, h2⟩ := hl f (by simp) c1
    exact ⟨c2, by simp only [List.foldr_cons, h1, h2]⟩

theorem gelf_const (τ : D.what₂.Tau) (k : ℕ) (c : ℂ) : ∃ c' : ℂ, gelf θ V τ k (fun _ => c) = fun _ => c' := by
  unfold gelf
  apply Finset.sum_induction _ (fun F => ∃ c', F = fun _ => c')
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, rfl⟩
  · exact ⟨0, rfl⟩
  · intro idx _
    apply foldr_const
    intro f hf c0
    rw [List.mem_ofFn] at hf
    obtain ⟨a, rfl⟩ := hf
    exact ⟨0, RderC_const θ V τ _ c0⟩

theorem foldrRder_const (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) :
    ∃ c' : ℂ, l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun _ => c) = fun _ => c' := by
  induction l with
  | nil => exact ⟨c, rfl⟩
  | cons p l ih =>
    obtain ⟨c1, h1⟩ := ih
    exact ⟨0, by simp only [List.foldr_cons, h1, Rder_const]⟩

theorem isAutFunSm_const (c : ℂ) : IsAutFunSm θ V (fun _ => c) := by
  refine ⟨⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩,
    fun _ _ _ _ _ => contDiff_const, ?_, ?_⟩
  ·
    refine ⟨Submodule.span ℂ {fun _ => (1 : ℂ)}, FiniteDimensional.span_singleton ℂ _, ?_, ?_⟩
    · exact Submodule.mem_span_singleton.2 ⟨c, by funext g; simp⟩
    · intro τ k f hf
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
      have e : (a • fun _ : GA D V => (1 : ℂ)) = fun _ => a := by funext g; simp
      obtain ⟨c', hc'⟩ := gelf_const θ V τ k a
      rw [e, hc']
      exact Submodule.mem_span_singleton.2 ⟨c', by funext g; simp⟩
  ·
    refine ⟨0, fun l _ x => ?_⟩
    obtain ⟨c', hc'⟩ := foldrRder_const θ V l c
    exact ⟨‖c'‖, fun g _ => by rw [hc', pow_zero, mul_one]⟩

end Const

theorem VolTieG.volTie (h : VolTieG D) : Formalism.MainNotions.StandardLattice.VolTie D := by
  unfold VolTieG at h
  unfold Formalism.MainNotions.StandardLattice.VolTie
  intro W P Q hW hsig
  have e1 : (fun ρ => (W.sig (tauE D ρ)).1) = fun _ => P := by
    funext ρ
    rw [hsig]
  have e2 : (fun ρ => (W.sig (tauE D ρ)).2) = fun _ => Q := by
    funext ρ
    rw [hsig]
  have h' := h W hW
  rw [e1, e2] at h'
  exact h'

end Formalism.L2.Theta

end
