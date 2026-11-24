module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem ku_of : jumpWindows.G5 → D0 → KU := by
  intro hG hD E _ _ _ k ψ hψ φ u hφ h1
  obtain ⟨-, -, -, hW⟩ := hG E k ψ hψ
  have hWc : Continuous (Wh ψ φ) := (hW φ hφ).1
  obtain ⟨hpos, hmul, hcont, -⟩ := hD E k
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hmul 1 1
    rw [show (1 : GA E k) * 1 = 1 from mul_one 1] at h
    exact mul_left_cancel₀ (hpos 1).ne' (h.symm.trans (mul_one _).symm)
  set F : GA E k → ℂ := fun c => conj (Wh ψ φ c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I) with hF
  have hDc : Continuous fun c : GA E k => (Dt c : ℂ) := Complex.continuous_ofReal.comp hcont
  have hFc : Continuous F := (Complex.continuous_conj.comp hWc).mul
    (hDc.cpow continuous_const fun c => Complex.ofReal_mem_slitPlane.2 (hpos c))
  have hF1 : F 1 = 1 := by simp [F, h1, hD1]
  refine ⟨{c | Dt c ∈ Set.Ioo (1 / 2 : ℝ) 2} ∩ {c | 0 < (F c).re}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.preimage hcont).inter (isOpen_lt continuous_const (Complex.continuous_re.comp hFc))
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, hD1, hF1]
      norm_num
  · rintro c ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha.le, hb.le, hc⟩

end PositivityTheory.AdelicQuotientData

end
