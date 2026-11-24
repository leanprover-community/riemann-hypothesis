module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions : ∀ (N : ℕ), IsRAct (vact N) ∧ (∀ D, IsRAct (gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, vmul (vmul x α) β = vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, vmul (M • x) α = M • vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), vmul x (dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, redGL N (γ * δ) = redGL N γ * redGL N δ) ∧ redGL N 1 = 1 := by
  first | exact @GlobalTheory.WpFam.Act.rightActions | exact GlobalTheory.WpFam.Act.rightActions | (intros; apply GlobalTheory.WpFam.Act.rightActions <;> assumption)
