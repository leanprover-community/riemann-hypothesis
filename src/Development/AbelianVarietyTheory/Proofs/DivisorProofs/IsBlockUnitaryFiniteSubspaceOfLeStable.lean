module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_of_le : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U →
    (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  intro ι M _ _ _ _ s F U U' hU hle hst
  obtain ⟨hfin, -, ip, hsym, hpos, hadj⟩ := hU
  refine ⟨Submodule.finiteDimensional_of_le hle, hst, ip, ?_, ?_, ?_⟩
  · intro x hx y hy; exact hsym x (hle hx) y (hle hy)
  · intro x hx h0; exact hpos x (hle hx) h0
  · intro a b hab x hx y hy; exact hadj a b hab x (hle hx) y (hle hy)

end GlobalTheory.HoweR
