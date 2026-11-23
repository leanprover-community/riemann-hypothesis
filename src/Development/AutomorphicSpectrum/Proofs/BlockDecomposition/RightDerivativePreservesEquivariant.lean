module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_mem_Eqv (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) :
    h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  intro hh p hp g hg
  have hpg : p * g ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hp.1 hg
  rw [DR_apply X h hpg, DR_apply X h hg]
  have dg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hg
  have dpg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hpg
  have ev : (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) =ᶠ[nhds g] fun y => φ p • h.1 y := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact hh p hp y hy
  have e1' : fderiv ℝ (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) g (g * X)
      = fderiv ℝ h.1 (p * g) (p * (g * X)) :=
    GlobalTheory.CompanionTheory.RCalc.fderiv_comp_clm (GlobalTheory.CompanionTheory.RCalc.mulL p) dpg (g * X)
  rw [ev.fderiv_eq] at e1'
  have e2' := GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply dg (φ p) (g * X)
  simp only [Rd]
  rw [Matrix.mul_assoc, ← e1']
  exact e2'

end GlobalTheory.CompanionTheory.ModelS
