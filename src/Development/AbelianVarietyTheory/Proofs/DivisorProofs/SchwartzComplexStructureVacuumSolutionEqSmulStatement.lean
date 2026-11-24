module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmul
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply

@[expose] public section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

theorem _root_.GlobalTheory.T.schwartz_complexStructure_vacuum_solution_eq_smul : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ y, (∀ x, B x y = 0) → y = 0) →
    ∀ (J e : (V × V) →ₗ[ℝ] (V × V)) (e' : V →ₗ[ℝ] V), (∀ y, J (J y) = -y) → (∀ y, e (e y) = e y) →
    (∀ y, J (e y) = e (J y)) → (∀ y, (e y).1 = e' y.1) → (∀ y x, B x (e y).2 = B (e' x) y.2) →
    ∀ (f g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ y x, fderiv ℝ g x (J y).1 - 2 * Real.pi * Complex.I * (B x (J y).2 : ℝ) * g x =
      Complex.I * (fderiv ℝ g x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * g x)) →
    (∀ y x, fderiv ℝ f x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I * (B x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f x =
      Complex.I * (fderiv ℝ f x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * f x)) →
    ∃ z : ℂ, f = z • g := by
  first | exact @GlobalTheory.VacCore.schwartz_vacuum_eq_smul | exact GlobalTheory.VacCore.schwartz_vacuum_eq_smul | (intros; apply GlobalTheory.VacCore.schwartz_vacuum_eq_smul <;> assumption)
