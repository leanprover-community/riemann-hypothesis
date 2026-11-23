module

public import Formalism.PeriodIntegrals.NMeasInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.RightInvOfContract
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousUMatApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HaarSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstLeftInvMuInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ModOne
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

open MeasureTheory NumberField

namespace PI.NMeasInv.UnitaryGroupMassFormula

def Contract : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∃ C : Set I.Ginf, IsCompact C ∧ ∀ n ∈ Ninf I e z, ∃ a : I.Ginf,
      (∀ x ∈ Ninf I e z, a * x * a⁻¹ ∈ Ninf I e z) ∧ (∀ x ∈ Ninf I e z, a⁻¹ * x * a ∈ Ninf I e z) ∧
      a * n * a⁻¹ ∈ C

theorem haarOn_of (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (μ : Measure I.Ginf) (hμ : IsHaarOnSet I (Ninf I e z) μ) :
    HaarOn (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) μ := by
  exact hμ

theorem finite_compact_measure : FinCpt := by
  intro I r e f z _ μ hμ K hK
  exact (haarOn_props (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z)
    (PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf (I := I) (e := e) (z := z)) μ (haarOn_of I e z μ hμ)).1 K hK

theorem rightInv_of (hC : Contract) : RightInv := by
  intro I r e f z h μ hμ n hn
  obtain ⟨C, hCc, hcon⟩ := hC I r e f z h
  exact rightInv_of_contract (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) (PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf (I := I) (e := e) (z := z))
    (haarOn_of I e z μ hμ) C hCc hcon n hn

theorem invInv_of (hR : RightInv) : InvInv := by
  intro I r e f z h μ hμ
  exact invInv_of_right (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) (PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf (I := I) (e := e) (z := z))
    (haarOn_of I e z μ hμ) (hR I r e f z h μ hμ)

theorem conjugation_invariant_measure : ConjInv := by
  intro I r e f z hF μ hμ h hh
  have hN : IsClosed ((PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z : Subgroup I.Ginf) : Set I.Ginf) :=
    PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf (I := I) (e := e) (z := z)
  have hC := PI.ScMuExists.UnitaryGroupMassFormula.instConj_of
    (PI.ScMuExists.UnitaryGroupMassFormula.genModOne_of PI.ScMuExists.UnitaryGroupMassFormula.generic_haar_subgroup)
    PI.ScMuExists.UnitaryGroupMassFormula.place_decomposition_instance PI.ScMuExists.UnitaryGroupMassFormula.measure_subFacts
  have hconj := hC I r e f z hF (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z)
    (PI.ScMuExists.UnitaryGroupMassFormula.HSub I (PI.ScMuExists.UnitaryGroupMassFormula.frameSet I e f z)) hN rfl rfl h hh
  have hG := PI.ScMuExists.UnitaryGroupMassFormula.generic_haar_subgroup I.Ginf (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) hN
  have hν : HaarOn (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) (PI.ScMuExists.UnitaryGroupMassFormula.haarSub _ hN) :=
    ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1⟩
  obtain ⟨c, -, -, hc⟩ := haarOn_unique (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) hN hν (haarOn_of I e z μ hμ)
  rw [hc, Measure.map_smul, hconj]
  fun_prop

theorem nMeasInv_of (hC : Contract) : Target := by
  exact ⟨finite_compact_measure, rightInv_of hC, invInv_of (rightInv_of hC), conjugation_invariant_measure⟩

end PI.NMeasInv.UnitaryGroupMassFormula
