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

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Loc

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Split : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m : ℕ} (F : Fin m → Set (Matrix (Fin n) (Fin n) k)),
    (∀ i, IsClosed (F i) ∧ ∀ g ∈ Gz Z, ∀ x ∈ F i, g.val * x * g⁻¹.val ∈ F i) → (∀ i j, i ≠ j → Disjoint (F i) (F j)) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ ((⋃ i, F i) ×ˢ Set.univ) → Inv Z ξ →
      ∃ η : Fin m → (Sp k n → ℂ) →ₗ[ℂ] ℂ, (∀ i, Supp (η i) (F i ×ˢ Set.univ) ∧ Inv Z (η i)) ∧
        ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ξ f = ∑ i, η i f

def LocChi : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (U : Set (Sp k n)), IsOpen U →
    (∀ χ : k[X], ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ ((Bz Z ∩ {x | x.charpoly = χ}) ×ˢ Set.univ) → Inv Z ξ → Kills ξ U) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → Kills ξ U

end PositivityTheory.RgUd.TP.Loc
