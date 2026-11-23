module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

noncomputable section

variable {E : Type*} [Field E]
variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineCoeffsFG.proof : LineCoeffsFG.Statement (E := E) W := by
  intro La x hLa hx
  let f : E →+ W := (smulAddHom E W).flip x
  have hf : Function.Injective f.toIntLinearMap := by
    intro a b hab
    have h : a • x = b • x := hab
    exact smul_left_injective E hx h
  have hS : La.toIntSubmodule.FG := by
    rw [Submodule.fg_iff_addSubgroup_fg]
    simpa using hLa
  have hle : (lineCoeffs (E := E) La x).toIntSubmodule.map f.toIntLinearMap ≤
      La.toIntSubmodule := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  have hN : (lineCoeffs (E := E) La x).toIntSubmodule.FG :=
    Submodule.fg_of_fg_map_injective _ hf (hS.of_le hle)
  rw [Submodule.fg_iff_addSubgroup_fg] at hN
  simpa using hN

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
