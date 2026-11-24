module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas

theorem typeSet_measurable_invariant : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)), MeasurableSet B → MeasurableSet (typeSet I j B) ∧ (∀ γ ∈ I.GFset, ∀ x ∈ typeSet I j B, γ * x ∈ typeSet I j B) ∧ ∀ x ∈ typeSet I j B, ∀ k ∈ I.Kset, (x.1, x.2 * k) ∈ typeSet I j B := by
  intro I a j B hB
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, hs, hm, he⟩ := type_measurable I a j
    have : typeSet I j B = {x : I.GA | ∃ τ, HasType I x j τ} ∩ s ⁻¹' B := by
      ext x
      constructor
      · rintro ⟨τ, h1, h2⟩
        exact ⟨⟨τ, h2⟩, by rw [Set.mem_preimage, he x τ h2]; exact h1⟩
      · rintro ⟨⟨τ, h2⟩, h1⟩
        rw [Set.mem_preimage, he x τ h2] at h1
        exact ⟨τ, h1, h2⟩
    rw [this]
    exact hm.inter (hs hB)
  · rintro γ ⟨g, hg, h1, h2⟩ x ⟨τ, hτ, h⟩
    exact ⟨τ, hτ, ((GlobalTheory.PointEquivariance.equivariance I x g γ hg h1 h2).2.2.2.2.1 a j τ).2 h⟩
  · rintro x ⟨τ, hτ, h⟩ k hk
    refine ⟨τ, hτ, GlobalTheory.PointEquivariance.hasType_of I x (x.1, x.2 * k) (OrderIso.refl _) ?_
      (fun _ => rfl) (fun _ => rfl) j τ h⟩
    have e : ((x.1, x.2 * k) : I.GA) = x * (1, k) := Prod.ext (mul_one _).symm rfl
    rw [e]
    exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I x (1, k)).1 hk

end GlobalTheory.FlagMeas
