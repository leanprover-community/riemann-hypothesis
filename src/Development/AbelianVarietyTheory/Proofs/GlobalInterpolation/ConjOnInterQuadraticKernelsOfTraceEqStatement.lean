module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjOnInterQuadraticKernelsOfTraceEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.conj_on_inter_quadraticKernels_of_trace_eq : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ ρ' : Γ →* GL (Fin n) k) (χ₁ χ₂ : Γ →* ℤˣ), IsSSRep ρ → IsSSRep ρ' → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ P : GL (Fin n) k, ∀ g, χ₁ g = 1 → χ₂ g = 1 → ρ' g = P⁻¹ * ρ g * P := by
  first | exact @GlobalTheory.QuadKernelConj.conj_on_ker_inf_ker | exact GlobalTheory.QuadKernelConj.conj_on_ker_inf_ker | (intros; apply GlobalTheory.QuadKernelConj.conj_on_ker_inf_ker <;> assumption)
