module

public import GroundTheory.AutomorphicForms.RealGroupsLie
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace SecondKind

abbrev MatProd {f : ℕ} (p q : Fin f → ℕ) : Type :=
  (τ : Fin f) → Matrix (Fin (p τ) ⊕ Fin (q τ)) (Fin (p τ) ⊕ Fin (q τ)) ℂ

def lieProd {f : ℕ} (p q : Fin f → ℕ) : Submodule ℝ (MatProd p q) :=
  Submodule.pi Set.univ fun τ => indefiniteUnitaryLieAlgebra (p τ) (q τ)

def hsInner {f : ℕ} {p q : Fin f → ℕ} (X X' : MatProd p q) : ℝ :=
  ∑ τ, (trace (X τ * (X' τ)ᴴ)).re

structure OrthoFrame where

  f : ℕ

  r : ℕ
  f_pos : 1 ≤ f
  r_pos : 1 ≤ r

  p : Fin f → ℕ

  q : Fin f → ℕ
  sig : ∀ τ, p τ + q τ = r

  place : Fin (f * r ^ 2) → Fin f

  E : Fin (f * r ^ 2) → MatProd p q
  span : Submodule.span ℝ (Set.range E) = lieProd p q
  orthonormal : ∀ k l, hsInner (E k) (E l) = if k = l then 1 else 0
  supp : ∀ l τ, τ ≠ place l → E l τ = 0

namespace OrthoFrame

variable (F : OrthoFrame)

end OrthoFrame

end SecondKind

end

end GroundTheory.Heights₂.Theta
