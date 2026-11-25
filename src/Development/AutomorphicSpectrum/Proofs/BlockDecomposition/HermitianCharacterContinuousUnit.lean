module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel

namespace GlobalTheory.CompanionTheory.CoefWeight

theorem continuous_norm_coefChar : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : PositivityTheory.GramSchwartzFunctions.HermE D n, Continuous (fun b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n => ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧ ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ‖ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 := by
  intro D n ψ hψ β
  refine ⟨?_, fun b => hψ.2.1 _⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold GlobalTheory.StdUnn.halfTr
  exact hψ.1.comp ((continuous_const.mul (ht.comp
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace))).neg)

end GlobalTheory.CompanionTheory.CoefWeight
