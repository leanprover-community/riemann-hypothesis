module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImageStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodSubgroupFinitePointsSemidirectStatement
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellMass

theorem cell_fubini : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ j ∈ idx D,
    ∀ ρ : Measure ((rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))))) (ν : Measure (GfC (ch.G.V (.top j)))),
      0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : GfC (ch.G.V (.grid D.R.m j)),
        ρ.real {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} =
          κ * la.real {n | b⁻¹ * n.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} * ν.real (prSet ch.G j b) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro j hj ρ hρ
  obtain ⟨-, -, -, h4, h5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.grid D.R.m j))
  obtain ⟨-, -, -, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.top j))
  obtain ⟨c1, c2, c3, c4, c5, π, σ, hπ, hσ, hπσ, hker, hpr⟩ := GlobalTheory.T.rowPeriodSubgroup_finitePoints_semidirect ch j hj
  obtain ⟨κ, la, ν, hκ, hla, hν, h⟩ := GlobalTheory.T.haar_trace_conj_eq_const_mul_kernel_image _ _ _ π σ c1 c2 c3 c4 c5 hπ hσ hπσ hker ρ hρ
  exact ⟨κ, la, ν, hκ, hla, hν, fun b => by rw [hpr b]; exact h b⟩

end GlobalTheory.CellMass
