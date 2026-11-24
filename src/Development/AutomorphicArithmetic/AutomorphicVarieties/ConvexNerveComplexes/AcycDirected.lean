module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_directed :
    ∀ {I : Type} (S : ∀ n, Set (Fin n → I)), (∀ (n : ℕ) (s : Finset (Fin n → I)), (↑s : Set (Fin n → I)) ⊆ S n → ∃ S' : ∀ k, Set (Fin k → I), (∀ k, S' k ⊆ S k) ∧ (↑s : Set (Fin n → I)) ⊆ S' n ∧ Acyc S') → Acyc S := by
  intro I S h
  refine ⟨fun c hc => ?_, fun n c hc h0 => ?_⟩
  · obtain ⟨S', hS, hs, hA⟩ := h 0 c.support ((Finsupp.mem_supported ℤ c).1 hc)
    obtain ⟨b, hb, e⟩ := hA.1 c ((Finsupp.mem_supported ℤ c).2 hs)
    exact ⟨b, Finsupp.supported_mono (hS 1) hb, e⟩
  · obtain ⟨S', hS, hs, hA⟩ := h (n + 1) c.support ((Finsupp.mem_supported ℤ c).1 hc)
    obtain ⟨b, hb, e⟩ := hA.2 n c ((Finsupp.mem_supported ℤ c).2 hs) h0
    exact ⟨b, Finsupp.supported_mono (hS (n + 2)) hb, e⟩
