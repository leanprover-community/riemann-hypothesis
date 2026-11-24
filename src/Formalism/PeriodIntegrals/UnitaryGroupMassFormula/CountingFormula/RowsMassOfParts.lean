module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pos

end Pos


variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]


section Bridge

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem hWb_isSymm : (hWb D F0).IsSymm := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [hWb_mk, hWb_mk]
  exact (VS D).herm.eq a.1 b.1

theorem one_mem_stabF : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := by
  refine ⟨Subgroup.one_mem _, fun j => ?_, rfl⟩
  ext x
  simp

theorem one_mem_hz {V1 : Type} [AddCommGroup V1] [Module D.host.E V1]
    (h1 : V1 →ₗ⋆[D.host.E] V1 →ₗ[D.host.E] D.host.E) (z : V1) :
    (1 : V1 ≃ₗ[D.host.E] V1) ∈ hz h1 z :=
  ⟨Subgroup.one_mem _, rfl⟩

theorem gmap_one' {V1 : Type} [AddCommGroup V1] [Module D.host.E V1] [Module (𝓞 D.host.E) V1]
    [IsScalarTower (𝓞 D.host.E) D.host.E V1] (M : Submodule (𝓞 D.host.E) V1) :
    Formalism.HermitianLatticesTheory.gmap (1 : V1 ≃ₗ[D.host.E] V1) M = M := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

end Bridge

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
