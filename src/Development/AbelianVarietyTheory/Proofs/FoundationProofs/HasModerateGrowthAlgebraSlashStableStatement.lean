module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.hasModerateGrowth_algebra_slash_stable : (∀ F G : ℍ → ℂ, Mod F → Mod G → Mod (fun τ => F τ + G τ) ∧ Mod (fun τ => F τ * G τ)) ∧ (∀ c : ℂ, Mod fun _ => c) ∧ (∀ (F : ℍ → ℂ) (k : ℕ) (δ : M2), 0 < δ.det → δ 1 0 = 0 → Mod F → Mod (slz k δ F)) := by
  first | exact @GlobalTheory.EisM.mod_algebra | exact GlobalTheory.EisM.mod_algebra | (intros; apply GlobalTheory.EisM.mod_algebra <;> assumption)
