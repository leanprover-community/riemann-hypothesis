module

public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingEquivApplyNeOfIsAlgebraic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingEquivNeOfTranscendental
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed :
    ∀ z : ℂ, (∀ σ : ℂ ≃+* ℂ, σ z = z) → ∃ q : ℚ, z = q := by
  intro z hz
  by_contra h
  push_neg at h
  by_cases ha : IsAlgebraic ℚ z
  · obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.ClassFin.exists_ringEquiv_apply_ne_of_isAlgebraic z ha h
    exact hσ (hz σ)
  · obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.ClassFin.exists_ringEquiv_ne_of_transcendental z ha
    exact hσ (hz σ)

end GlobalTheory.ClassFin
