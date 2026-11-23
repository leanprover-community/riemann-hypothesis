module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.Centred
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.CsReorderord
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reorder {h N : ℕ} (δ : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (s : Fin h → ℝ)
    (hL : ∀ j, IsLSeg (Δ j) (δ j).rep) (hc : ∀ j, PositivityTheory.UdReth2.IsCentred (Δ j)) (hs : ∀ j, |s j| < 1 / 2)
    (σ : Equiv.Perm (Fin h)) (hd : ∑ j, ((δ j).nu (s j)).1 = N) (hd' : ∑ j, ((δ (σ j)).nu (s (σ j))).1 = N) :
    Nonempty ((prodIrr (fun j => (δ j).nu (s j)) hd).Equiv (prodIrr (fun j => (δ (σ j)).nu (s (σ j))) hd')) := by
  have hnp : ∀ i j, ¬ ((Δ i).nu ((s i : ℝ) : ℂ)).Precedes ((Δ j).nu ((s j : ℝ) : ℂ)) := by
    intro i j hp
    have h1 := PositivityTheory.UdReth2.add_one_le_of_precedes (Δ i) (Δ j) (hc i) (hc j) (s i) (s j) hp
    have := hs i
    have := hs j
    rw [abs_lt] at *
    linarith
  exact PositivityTheory.PfEss.Zc2.cs_reorderord PositivityTheory.RgGu.NR.ConjDual.irrAdm' (GlobalTheory.RgGu.Holds.lUnlinkedComm_holds k)
    (fun j => (Δ j).nu ((s j : ℝ) : ℂ)) σ (fun j => (δ j).nu (s j)) hd hd'
    (fun i j _ => hnp i j) (fun i j _ => hnp (σ i) (σ j)) (fun j => GlobalTheory.isLSeg_nu (hL j) _)

end PositivityTheory.Gud.Pf

end
