module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm

namespace GlobalTheory.CompanionTheory.BesselMapSm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem dsLin : DsLin := by
  intro n Hm H _ _ _ σ hσ u hu
  have h1 : (1 : Mat n) ∈ Formalism.QuantumDeterminants.UH Hm := hσ.grp.2.1
  obtain ⟨U, F, hUo, h1U, hF, hfF⟩ := hu 1 h1
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have hmem : ∀ t : ℝ, ex X t ∈ Formalism.QuantumDeterminants.UH Hm := fun t => ex_mem_of_lie hX t
  have hd : HasDerivAt (fun t : ℝ => ex X t) X 0 := by
    simpa using hasDerivAt_mul_ex (1 : Mat n) X
  have hl := hasDerivAt_local (f := fun g => σ g u) hmem (ex_zero X) hd hUo h1U hF hfF
  exact hl.deriv

end GlobalTheory.CompanionTheory.BesselMapSm
