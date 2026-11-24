module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  intro V₁ V₂ _ _ Λ D₁ D₂ h1 h2 v
  obtain ⟨l₂, ⟨⟨s, hs⟩, hl₂D⟩, -⟩ := h2 v.2
  obtain ⟨l₁, ⟨hl₁, hl₁D⟩, -⟩ := h1 (v.1 + s)
  have hl₁' : ((l₁, 0) : V₁ × V₂) ∈ Λ := hl₁
  refine ⟨(s + l₁, l₂), ⟨?_, ?_⟩, ?_⟩
  · have e : ((s + l₁, l₂) : V₁ × V₂) = (s, l₂) + (l₁, 0) := by simp
    rw [e]; exact Λ.add_mem hs hl₁'
  · refine ⟨?_, ?_⟩
    · show v.1 + (s + l₁) ∈ D₁
      rw [← add_assoc]; exact hl₁D
    · exact hl₂D
  · rintro ⟨m₁, m₂⟩ ⟨hm, hmD⟩
    have hmD1 : v.1 + m₁ ∈ D₁ := hmD.1
    have hmD2 : v.2 + m₂ ∈ D₂ := hmD.2
    have e2 : m₂ = l₂ := (h2 v.2).unique ⟨⟨m₁, hm⟩, hmD2⟩ ⟨⟨s, hs⟩, hl₂D⟩
    subst e2
    have hx : ((m₁ - s, 0) : V₁ × V₂) ∈ Λ := by
      have := Λ.sub_mem hm hs
      simpa using this
    have e1 : m₁ - s = l₁ := (h1 (v.1 + s)).unique
      ⟨hx, by show v.1 + s + (m₁ - s) ∈ D₁; simpa using hmD1⟩ ⟨hl₁, hl₁D⟩
    have : m₁ = s + l₁ := by rw [← e1]; abel
    rw [this]

end GlobalTheory
