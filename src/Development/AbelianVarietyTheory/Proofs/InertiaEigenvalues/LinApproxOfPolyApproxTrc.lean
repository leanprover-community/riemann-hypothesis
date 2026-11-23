module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem linApprox_of_polyApprox_trc : ∀ (k Γ : Type) [NormedField k] [IsUltrametricDist k] [Group Γ] (a : ℕ)
    (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)), PolyApprox (trc r) (trc '' C) → LinApprox r C := by
  intro k Γ _ _ _ a r C h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  let f : (Γ → k) → (Γ →* GL (Fin a) k) := Function.invFunOn trc C
  have hf : ∀ η ∈ s, f η ∈ C ∧ trc (f η) = η := fun η hη =>
    ⟨Function.invFunOn_mem (hs hη), Function.invFunOn_eq (hs hη)⟩
  have hinj : Set.InjOn f (s : Set (Γ → k)) := fun x hx y hy hxy => by
    rw [← (hf x hx).2, ← (hf y hy).2, hxy]
  refine ⟨s.image f, fun ρ => c (trc ρ), ?_, fun g => ?_⟩
  · intro ρ hρ
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
    exact (hf η hη).1
  · have := hP (MvPolynomial.X g)
    simp only [MvPolynomial.aeval_X] at this
    rw [Finset.sum_image hinj]
    have e : ∑ x ∈ s, c (trc (f x)) * trc (f x) g = ∑ η ∈ s, c η * η g :=
      Finset.sum_congr rfl fun η hη => by rw [(hf η hη).2]
    rw [e]
    exact this

end GlobalTheory.Cong
