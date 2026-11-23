module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsLast
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Disc

theorem eq_zero_of_lt_one {L : Type} [Field L] [NumberField L] (a : 𝓞 L)
    (h : ∀ w : InfinitePlace L, w (a : L) < 1) : a = 0 := by
  apply GlobalTheory.SmallIntegerVanishing.eq_zero_of_small <;> assumption

theorem continuous_entry {L : Type} [Field L] [NumberField L] {N : ℕ} (w : InfinitePlace L) (i j : Fin N) :
    Continuous fun x : Sp L N => mt x w i j := by
  fun_prop

theorem mt_latS {L : Type} [Field L] [NumberField L] {N : ℕ} (σ : SpecialLinearGroup (Fin N) (𝓞 L))
    (w : InfinitePlace L) (i j : Fin N) :
    mt ((MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w)) σ) w i j =
      w.embedding (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j : 𝓞 L) : L) := rfl

theorem countable_O (L : Type) [Field L] [NumberField L] : Countable (𝓞 L) :=
  (RingOfIntegers.basis L).equivFun.injective.countable

end PositivityTheory.KB.MomentRationality.Disc

namespace PositivityTheory.KB

open MomentRationality MomentRationality.Disc

theorem discrete_specialLinearGroup_ringOfIntegers : SDisc := by
  intro L _ _ N
  refine ⟨?_, ?_⟩
  · rw [discreteTopology_iff_isOpen_singleton_one]
    let U : Set (Sp L N) :=
      {x | ∀ w i j, ‖mt x w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1}
    have hU : IsOpen U := by
      simp only [U, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i =>
        isOpen_iInter_of_finite fun j =>
          isOpen_lt ((continuous_entry w i j).sub continuous_const).norm continuous_const
    refine isOpen_induced_iff.2 ⟨U, hU, ?_⟩
    ext ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hγU
      obtain ⟨σ, rfl⟩ := hγ
      have hσ : σ = 1 := by
        refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
        have h0 := eq_zero_of_lt_one
          (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j) - (1 : Matrix (Fin N) (Fin N) (𝓞 L)) i j) (fun w => ?_)
        · simpa using sub_eq_zero.1 h0
        · have h1 := hγU w i j
          rw [mt_latS] at h1
          rw [← norm_embedding_eq]
          convert h1 using 2
          by_cases hij : i = j
          · subst hij
            simp
          · simp [Matrix.one_apply, hij]
      subst hσ
      apply Subtype.ext
      simp
    · intro h
      have h' : γ = 1 := congrArg Subtype.val h
      subst h'
      intro w i j
      have hone : mt (1 : Sp L N) w = 1 := rfl
      rw [hone, sub_self, norm_zero]
      exact one_pos
  · haveI := countable_O L
    haveI : Countable (Matrix (Fin N) (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable (Fin N → Fin N → 𝓞 L))
    haveI : Countable (SpecialLinearGroup (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable {A : Matrix (Fin N) (Fin N) (𝓞 L) // A.det = 1})
    exact (MonoidHom.rangeRestrict_surjective
      (MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w))).countable

end PositivityTheory.KB

end
