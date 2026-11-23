module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem fibrePointsLE_diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ)
    (h : FibrePointsLE f (n + 1)) : FibrePointsLE (diagComplHom f) n := by
  intro K _ y s hs hinj
  set t : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z) := fun j => s j ≫ (diagCompl f).ι ≫ pullback.fst f f
    with ht
  have hsnd : ∀ j, s j ≫ (diagCompl f).ι ≫ pullback.snd f f = y := fun j => by
    simpa [diagComplHom] using hs j
  have htf : ∀ j, t j ≫ f = y ≫ f := fun j => by
    simp only [ht, Category.assoc, pullback.condition]
    rw [← hsnd j]
    simp only [Category.assoc]
  have hne : ∀ j, t j ≠ y := by
    intro j hj
    have heq : s j ≫ (diagCompl f).ι = y ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp [← hj, ht]
      · simp [hsnd j]
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
    have h1 : (s j ≫ (diagCompl f).ι).base x ∈ diagCompl f := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    rw [heq] at h1
    exact h1 ⟨_, rfl⟩
  apply h K (y ≫ f) (Fin.cons y t)
  · intro j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simpa using htf j
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij.symm (hne _)
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij (hne _)
    · rename_i i j
      simp only [Fin.cons_succ] at hij
      congr 1
      apply hinj
      rw [← cancel_mono (diagCompl f).ι]
      apply pullback.hom_ext
      · simpa [ht] using hij
      · simp [hsnd i, hsnd j]

end GlobalTheory.EtC.Tr
