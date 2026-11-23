module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

theorem smonorm_of : Meet → CuspidalIrreducibleSubrep → SmoNorm := by
  intro hM hG E _ _ _ a π π' hπ hπ' hS
  let μ : Measure (GA E a) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨H, hH, hf⟩ := hG E a μ π hπ
  obtain ⟨H', hH', hf'⟩ := hG E a μ π' hπ'
  have hne : H ⊓ H' ≠ ⊥ := hM E a μ π π' H H' hπ hπ' hH.1 hH'.1
    (fun φ hφ => ⟨hf.finitePartMemL2 φ hφ, hf.classes_le (toL2_mem_classes hφ (hf.finitePartMemL2 φ hφ))⟩)
    (fun φ hφ => ⟨hf'.finitePartMemL2 φ hφ, hf'.classes_le (toL2_mem_classes hφ (hf'.finitePartMemL2 φ hφ))⟩) hS
  have h1 : H ⊓ H' = H := (hH.2.2 _ inf_le_left (hH.1.inf hH'.1)).resolve_left hne
  have h2 : H ⊓ H' = H' := (hH'.2.2 _ inf_le_right (hH.1.inf hH'.1)).resolve_left hne
  have e : H = H' := h1.symm.trans h2
  subst e
  exact hf.unique hf'

end PositivityTheory.jumpWindows

end
