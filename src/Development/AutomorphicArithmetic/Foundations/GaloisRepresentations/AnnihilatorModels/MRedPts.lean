module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
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

@[expose] public section

namespace UpperTheory.Gal.crystallineComparison.Mod

theorem redPts_of : RedPts := by
  intro k H X _ _ _ _ _ C ρ h D
  obtain ⟨s, hs⟩ : ∃ s : H ⧸ C → H, Function.RightInverse s C.mkQ :=
    ⟨Function.surjInv (Submodule.mkQ_surjective C), Function.rightInverse_surjInv _⟩
  let g : H ⧸ C → X := fun q => ρ (s q)
  have hg : ∀ a, ρ a = g (C.mkQ a) := by
    intro a
    refine (h _ _).2 ?_
    have h1 : C.mkQ (s (C.mkQ a)) = C.mkQ a := hs _
    have h2 := (Submodule.Quotient.eq C).1 h1
    have h3 : a - s (C.mkQ a) = -(s (C.mkQ a) - a) := by abel
    rw [h3]
    exact C.neg_mem h2
  have hinj : Function.Injective g := by
    intro q1 q2 hq
    have hm := (h _ _).1 hq
    have e := (Submodule.Quotient.eq C).2 hm
    simpa [Submodule.mkQ_apply, hs q1, hs q2] using
      (show C.mkQ (s q1) = C.mkQ (s q2) from e)
  have himg : ∀ E : Submodule k H, ρ '' (E : Set H) = g '' ((Submodule.map C.mkQ E : Submodule k (H ⧸ C)) : Set (H ⧸ C)) := by
    intro E
    rw [Submodule.map_coe, Set.image_image]
    exact Set.image_congr (fun a _ => hg a)
  have hcard : ∀ V : Submodule k (H ⧸ C), Nat.card V = Nat.card k ^ Module.finrank k V := by
    intro V
    have : Finite (H ⧸ C) := Module.finite_of_finite k
    letI := Fintype.ofFinite k
    letI := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  refine ⟨?_, ?_⟩
  · rw [himg D, Nat.card_image_of_injective hinj]
    exact hcard _
  · intro D' hD
    rw [himg D, himg D', hD]

end UpperTheory.Gal.crystallineComparison.Mod
