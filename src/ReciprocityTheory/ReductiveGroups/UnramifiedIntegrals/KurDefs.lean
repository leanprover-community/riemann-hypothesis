module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section Concrete

variable (l : ℕ) [Fact l.Prime]

def muP : Set ℂ_[l] := {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}

def Rmu : Subring ℂ_[l] := Subring.closure (muP l)

def Kmu : Subfield ℂ_[l] := Subfield.closure (muP l)

def Tch : Set ℂ_[l] := insert 0 (muP l)

theorem kur_complete : CompleteSpace (MaximalUnramifiedExtension l) :=
  (Subfield.isClosed_topologicalClosure (Kmu l)).completeSpace_coe

end Concrete

structure FrobField (K : Type) [NormedField K] (l : ℕ) (σ : K →+* K) : Prop where
  prime : l.Prime
  norm_l : ‖(l : K)‖ < 1
  isom : ∀ x : K, ‖σ x‖ = ‖x‖
  frob : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ l‖ ≤ ‖(l : K)‖
  discrete : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : K)‖

def ResClosed (K : Type) [NormedField K] (l : ℕ) : Prop :=
  ∀ P : Polynomial K, P.Monic → 0 < P.natDegree → (∀ i, ‖P.coeff i‖ ≤ 1) →
    ∃ x : K, ‖x‖ ≤ 1 ∧ ‖P.eval x‖ ≤ ‖(l : K)‖

end ReciprocityTheory.ChartRestriction.L1
