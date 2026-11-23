module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.eig :
    EigZero → Eig := by
  intro hE T J _ _ _ _ _ ρ s A hA hμs
  obtain ⟨μ, l0, hl0, hl0eq, hgen⟩ := hE T J ρ
  have hμ : ∀ t, μ (s t) = μ t := hμs μ hgen
  let W : Submodule ℂ (Module.Dual ℂ J) :=
    { carrier := {l | ∀ t y, l (ρ t y) = (μ t : ℂ) * l y}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.add_apply, ha t y, hb t y]
        ring
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro t y
        simp
      smul_mem' := by
        intro c l hl
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.smul_apply, smul_eq_mul, hl t y]
        ring }
  have hAW : ∀ l ∈ W, LinearMap.dualMap A l ∈ W := by
    intro l hl t y
    show l (A (ρ t y)) = (μ t : ℂ) * l (A y)
    rw [hA, hl, hμ]
  let A' : W →ₗ[ℂ] W := (LinearMap.dualMap A).restrict hAW
  haveI : Nontrivial W := ⟨⟨⟨l0, hl0eq⟩, 0, fun h => hl0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A'
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨μ, (v : Module.Dual ℂ J), c, fun h => hv.2 (Subtype.ext h), hμ, v.2, fun y => ?_⟩
  have := congrArg (fun w : W => (w : Module.Dual ℂ J) y) hv.apply_eq_smul
  simpa [A'] using this
