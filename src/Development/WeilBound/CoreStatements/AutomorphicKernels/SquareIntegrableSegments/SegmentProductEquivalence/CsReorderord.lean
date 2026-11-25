module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.CsOrderfree
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace PositivityTheory.PfEss.Zc2

theorem cs_reorderord : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (σ : Equiv.Perm (Fin h)) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (hd' : ∑ a, (y (σ a)).1 = N), (∀ i j, i < j → ¬ (Γ i).Precedes (Γ j)) → (∀ i j, i < j → ¬ (Γ (σ i)).Precedes (Γ (σ j))) → (∀ i, IsLSeg (Γ i) (y i).rep) → Nonempty ((prodIrr y hd).Equiv (prodIrr (y ∘ σ) hd')) := by
  intro k _ _ _ _ _ hUC h N Γ σ y hd hd' hΓ hΓσ hseg
  have hnl : ∀ a b : Fin h, a < b → σ.symm b < σ.symm a → ¬(Γ a).Linked (Γ b) := by
    intro a b hab hba hl
    rcases Segment.linked_iff_precedes.mp hl with hp | hp
    · exact hΓ a b hab hp
    · have := hΓσ (σ.symm b) (σ.symm a) hba
      simp only [Equiv.apply_symm_apply] at this
      exact this hp
  exact CompanionTheory.PfEss.Zc2.reach_of_inv hUC hd hseg _ σ rfl hnl hd'

end PositivityTheory.PfEss.Zc2
