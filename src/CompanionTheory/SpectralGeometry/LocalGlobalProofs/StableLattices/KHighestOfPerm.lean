module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.DSData

open Formalism.REAL (KHighest)
open CompanionTheory.RgExh CompanionTheory.RgExh.Fin

variable {n : ℕ}

theorem kHighest_of_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x) :
    KHighest ε E (μ ∘ s.symm) x := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · simpa using h.1 (s.symm a)
  · have h1 : (ε ∘ s) (s.symm a) = (ε ∘ s) (s.symm b) := by simpa using he
    simpa using h.2 (s.symm a) (s.symm b) (GlobalTheory.DSId.PermK.mono_symm hs a b hab h1) h1

theorem kHighest_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest ε E (μ ∘ s.symm) x) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x := by
  refine ⟨fun a => ?_, fun a b hab he => h.2 _ _ (hs a b hab he) he⟩
  simpa using h.1 (s a)

theorem dsOfData : DSOfData := by
  intro n ε H _ _ σ D E hK s mu hSq hA
  obtain ⟨-, hord, hmin, v, hv0, hv⟩ := hA
  obtain ⟨hT, -, -, hS, -⟩ := GlobalTheory.DSId.PermK.permKType n ε s H σ hord
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.1 hSq
  have e : ∀ f : Fin n → ℝ, (f ∘ s.symm) ∘ s = f := fun f => by funext a; simp
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · obtain ⟨T, hT'⟩ := hK.ty _ v hv0 (kHighest_of_perm hord hv)
    refine ⟨T, ?_⟩
    have h6 := (hT _ T).1 hT'
    rwa [e] at h6
  · intro μ S hS'
    have h6 : Formalism.MainNotions.S.IsKTypeOf ε σ (μ ∘ s.symm) S := by
      refine (hT _ S).2 ?_
      rwa [e]
    obtain ⟨w, hw0, -, hw⟩ := hK.hw _ S h6
    exact hmin μ w hw0 (kHighest_perm hord hw)

end GlobalTheory.CompanionTheory.DSData
