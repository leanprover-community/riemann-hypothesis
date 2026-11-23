module

public import GroundTheory.PAdicHodge.FieldOfNormsUpper
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]


variable {L : IntermediateField K Ω} [IsGalois K L]

variable (hL : IsAPF K Ω L)
include hL



variable {L : IntermediateField K Ω} [IsGalois K L] (hL : IsAPF K Ω L)
include hL


section Construction

variable {L : IntermediateField K Ω} [IsGalois K L]

structure APFData (L : IntermediateField K Ω) where
  apf : IsAPF K Ω L
  c : ℝ
  c_pos : 0 < c
  u₀ : ℝ
  one_le_u₀ : 1 ≤ u₀
  le_psi : ∀ u, u₀ ≤ u → c * apfIndex K Ω L u ≤ apfPsi K Ω L u

namespace APFData

variable (d : APFData L)

def u (n : ℕ) : ℝ := d.u₀ + n * (d.c / 2)


end APFData

end Construction



namespace APFData

variable {L : IntermediateField K Ω} [IsGalois K L] (d : APFData L)


end APFData

end GroundTheory.PAdicHodge
