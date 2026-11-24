module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterTransport
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirFun

open Matrix

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_glEmbHom (n : ℕ) : Continuous (glEmbHom k n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun A : Matrix (Fin n) (Fin n) k => glEmbMat k n A i j
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases <;> simpa [glEmbMat] using continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j =>
      simp only [glEmbMat, Fin.lastCases_castSucc]
      exact (continuous_apply j).comp (continuous_apply i)

theorem continuous_levi (n : ℕ) : Continuous (levi k n) := by
  have h : Continuous (glEmb k n) := Continuous.units_map _ (continuous_glEmbHom k n)
  exact h.subtype_mk _

theorem smPsiMinus : SmPsiMinus k :=
  by apply _root_.UpperTheory.Reformulated.B.DYhc8.main <;> assumption

end GlobalTheory.CompanionTheory.BZMirFun
