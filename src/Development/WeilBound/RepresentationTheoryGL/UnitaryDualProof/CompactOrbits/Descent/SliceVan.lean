module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
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

@[expose] public section

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def JCPoly : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ y, ∃ P : k[X], ∀ x ∈ Bz Z, pZ Z x = y →
    Module.End.IsSemisimple (Matrix.toLin' (aeval x P)) ∧ IsNilpotent (x - aeval x P)

def SliceVan : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ s ∈ Bz Z,
    Module.End.IsSemisimple (Matrix.toLin' s) → Van (adj Z s) →
    ∀ (F : Set (Matrix (Fin n) (Fin n) k)) (P : k[X]), IsClosed F → F ⊆ Bz Z →
      (∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F) →
      (∀ x ∈ F, aeval x P ∈ F ∧ Module.End.IsSemisimple (Matrix.toLin' (aeval x P)) ∧ IsNilpotent (x - aeval x P) ∧
        ∃ g ∈ Gz Z, g.val * aeval x P * g⁻¹.val = s) →
      ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (F ×ˢ Set.univ) → Inv Z ξ → Kills ξ {p | p.2 ≠ 0}

end PositivityTheory.RgUd.T.Desc
