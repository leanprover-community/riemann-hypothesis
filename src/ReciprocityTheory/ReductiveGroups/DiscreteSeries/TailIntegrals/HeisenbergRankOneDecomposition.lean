module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.GoodRowsProjectorApplyEqSum
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Phi2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.StarLastDotLast

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem yx_ga (hB2 : InductiveHeisenbergInputs) (hIW : IW) (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') :
    0 < Ga k (1 + r') 0 (Yx k r' x) ∧ ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hHM, -⟩ := hB2
  exact ea_yx_ga hHM x

theorem heisenberg_rankOne_decomposition (hB2 : InductiveHeisenbergInputs) (hIW : IW) (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (c : ℂ) (hc : c ≠ 0) :
    ∃ κ ∈ Kset k (1 + r'), ∃ m ∈ GV k r', ∃ z : HPar k r',
      (heis0 k r' x)⁻¹ * w0 k r' c =
        κ * w0 k r' (c * (Real.sqrt (Ga k (1 + r') 0 (Yx k r' x)) : ℂ)) * ιLev k 1 r' m * heis0 k r' z ∧
      ∀ l : Fin (r' + 1), Ga k r' l (fun a => m *ᵥ phiV' k r' a) * Ga k (1 + r') 0 (Yx k r' x) =
        Ga k (1 + r') (sc r' l) (Yx k r' x) := by
  exact heisenberg_rankOne_decomposition_levi hB2 hIW k r' hk x c hc

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
