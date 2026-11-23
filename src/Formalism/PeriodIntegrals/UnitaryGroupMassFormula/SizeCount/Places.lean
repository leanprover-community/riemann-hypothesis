module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Development
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

theorem eTau_tauPl (D : D7) (z : Bool × HH D) :
    (D.eTau (tauPl D z) : D.R.GG) = plGG D z := by
  unfold Formalism.BasicNotions.tauPl
  simp

theorem ramifiedTau1_ne_ramifiedTau2 (φ : Formalism.HC.Frame) (a b : φ.A) : φ.tau1 a ≠ φ.tau2 b := by
  intro h
  have h1 := congrArg (fun x => x.1.1) h
  simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h1
  revert h1
  decide

theorem tau1_injective_alt (φ : Formalism.HC.Frame) {a b : φ.A} (h : φ.tau1 a = φ.tau1 b) : a = b := by
  simp only [Formalism.HC.Frame.tau1, Prod.mk.injEq, true_and] at h
  simpa [Formalism.HC.Frame.iota] using h

theorem placeFacts : PlaceFacts := by
  intro D
  have h1 : ∀ t : HH D, (D.eTau (tauPl D (false, t)) : D.R.GG) = D.R.tau1 t := by
    intro t; rw [eTau_tauPl]; simp [plGG]
  have h2 : ∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) = D.R.tau2 t := by
    intro t; rw [eTau_tauPl]; simp [plGG]
  have hPsi : ∀ z : Bool × HH D, (D.eTau (tauPl D z) : D.R.GG) ∈ D.R.Psi :=
    fun z => (D.eTau (tauPl D z)).2
  have hnt : ∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) ∉ D.host.topPlaces := by
    intro t h
    rw [h2] at h
    unfold Host.topPlaces at h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    exact ramifiedTau1_ne_ramifiedTau2 _ _ _ ha
  refine ⟨h1, ?_, hnt, ?_⟩
  · intro t ht
    refine ⟨hPsi _, ?_, ?_⟩
    · intro h
      rw [h1] at h
      unfold Host.topPlaces at h
      obtain ⟨a, ha, hat⟩ := Finset.mem_image.1 h
      exact ht (tau1_injective_alt _ hat ▸ ha)
    · intro h
      rw [h1] at h
      unfold Host.thickPlaces at h
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
      exact ramifiedTau1_ne_ramifiedTau2 _ _ _ ha.symm
  · intro t
    by_cases h : (D.eTau (tauPl D (true, t)) : D.R.GG) ∈ D.host.thickPlaces
    · exact Or.inl h
    · exact Or.inr ⟨hPsi _, hnt t, h⟩

end PI.SzCt.UnitaryGroupMassFormula
