module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem orbitFinite_of (hA : UnipotentIntegralIsGroup) (hB : OrbitReps) : OrbitFinite := by
  intro D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ
  obtain ⟨K, hKf, hK⟩ := hB D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ
  obtain ⟨-, hsymm, htrans⟩ := hA D F0 Λ
  unfold cntE
  rw [Set.encard_ne_top_iff]
  refine (hKf.image (fun k : (Fin D.R.rS → (VS D).V) × (VS D).V =>
      {F'' : LFlag (VS D) D.R.rS (Tn u') | F'' ∈ EZ (Tn u') F0 Λ Z ∧
        ∃ n ∈ N0 F0 Λ, (∀ a, n (k.1 a) = F''.fl.e a) ∧ n k.2 = F''.fl.z})).subset ?_
  rintro O ⟨F', hF', rfl⟩
  obtain ⟨n₀, hn₀, hk⟩ := hK F' hF'
  refine ⟨_, hk, ?_⟩
  ext F''
  simp only [Set.mem_setOf_eq, NilradicalFlagMoved]
  constructor
  · rintro ⟨hE, m, hm, he, hz⟩
    refine ⟨hE, n₀.trans m, htrans _ hn₀ _ hm, fun a => ?_, ?_⟩
    · simpa using he a
    · simpa using hz
  · rintro ⟨hE, n, hn, he, hz⟩
    refine ⟨hE, n₀.symm.trans n, htrans _ (hsymm _ hn₀) _ hn, fun a => ?_, ?_⟩
    · simpa using he a
    · simpa using hz

end PI.UnitaryGroupMassFormula.CntFormula
