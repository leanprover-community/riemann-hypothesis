module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousHPart
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousUMatApply
public import Formalism.RealPlaceAnalysis.FinalF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix
open scoped Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem isClosedEmbedding_uMat {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  (Formalism.REAL.uJEmb n ε).1

theorem proper_action_instance : InstProper := by
  intro I r e f z hF N H hNs hHs C hC
  let K : ∀ v, Set (Matrix (Fin I.n) (Fin I.n) ℂ) := fun v =>
    hPart (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) ''
      ((fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v)) '' C)
  have hK : ∀ v, IsCompact (K v) := fun v =>
    (hC.image (continuous_uMat_apply I v)).image (continuous_hPart _ _ _ _)
  let K2 : Set I.Ginf := Set.univ.pi fun v => (fun g : Formalism.REAL.UJ (I.ε v) => Formalism.MainNotions.S.uMat g) ⁻¹' K v
  have hK2 : IsCompact K2 :=
    isCompact_univ_pi fun v => (isClosedEmbedding_uMat (I.ε v)).isCompact_preimage (hK v)
  have hsub : {p : I.Ginf × I.Ginf | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} ⊆ (C * K2⁻¹) ×ˢ K2 := by
    rintro ⟨x, h⟩ ⟨hx, hh, hxh⟩
    have hx' : x ∈ Ninf I e z := by rw [← hNs]; exact hx
    have hh' : h ∈ Hset I (frameSet I e f z) := by rw [← hHs]; exact hh
    have hK2h : h ∈ K2 := by
      intro v _
      refine ⟨Formalism.MainNotions.S.uMat ((x * h) v), ⟨x * h, hxh, rfl⟩, ?_⟩
      show hPart _ _ _ _ (Formalism.MainNotions.S.uMat (x v * h v)) = Formalism.MainNotions.S.uMat (h v)
      rw [uMat_mul]
      exact hPart_mul (rFrame_of hF v) (hx' v) (uMat_inUJ (h v))
        (fun a => hh' v _ (Or.inl (Or.inl ⟨a, rfl⟩))) (fun a => hh' v _ (Or.inl (Or.inr ⟨a, rfl⟩)))
        (hh' v _ (Or.inr rfl))
    refine ⟨?_, hK2h⟩
    rw [← mul_inv_cancel_right x h]
    exact Set.mul_mem_mul hxh (Set.inv_mem_inv.mpr hK2h)
  have hcl : IsClosed {p : I.Ginf × I.Ginf | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} := by
    have hNc : IsClosed (N : Set I.Ginf) := by rw [hNs]; exact isClosed_Ninf I e z
    have hHc : IsClosed (H : Set I.Ginf) := by rw [hHs]; exact isClosed_Hset I _
    exact (hNc.preimage continuous_fst).inter ((hHc.preimage continuous_snd).inter
      (hC.isClosed.preimage continuous_mul))
  exact ((hC.mul hK2.inv).prod hK2).of_isClosed_subset hcl hsub

end PI.ScMuExists.UnitaryGroupMassFormula
