module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.aElt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ g, ∃ a ∈ M.gr 0, M.x0 a = 0 ∧ ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ (M.toSS a) = D.aVal g (M.rep ξ) := by
  intro Ω _ _ _ l _ c D _ M g
  choose f hf hπ using fun i : Fin 4 => M.hom g i i
  have hf0 : ∀ i, f i ∈ M.aPart 0 := by
    intro i
    have h := hf i
    rw [(wt_eq_zero i i).mpr rfl] at h
    exact h
  let fA : Fin 4 → M.A := fun i => ⟨f i, M.aPart_le (hf0 i)⟩
  have hx0 : ∀ i, M.x0 (fA i) = D.r0 g i i := fun i => M.at0 g i i (f i) (hπ i)
  have hss : ∀ i, M.toSS (fA i) = M.ent g i i := fun i => Subtype.ext (hπ i)
  refine ⟨∑ i, fA i - algebraMap c.O M.A (Matrix.trace (D.r0 g)), ?_, ?_, ?_⟩
  · apply Submodule.sub_mem
    · exact Submodule.sum_mem _ fun i _ => hf0 i
    · rw [Algebra.algebraMap_eq_smul_one]
      apply Submodule.smul_mem
      show (1 : M.R) ∈ M.aPart 0
      exact SetLike.GradedOne.one_mem
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, AlgHom.commutes]
    simp only [hx0, Algebra.algebraMap_self, RingHom.id_apply, Matrix.trace, Matrix.diag]
    exact sub_self _
  · intro ξ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_sum, AlgHom.commutes, AlgHom.commutes]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hss, Raw.aVal, Matrix.trace, Matrix.diag, map_sum]
    rfl
