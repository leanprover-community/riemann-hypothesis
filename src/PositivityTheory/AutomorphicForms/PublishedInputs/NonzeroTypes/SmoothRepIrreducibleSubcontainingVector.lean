module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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

namespace UpperTheory.NonzeroTypeTheory

def SmoothRepIrreducibleSubcontainingVector : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (m : ℕ)
    (V : Representation ℂ K (Fin m → ℂ)), GlobalTheory.PRep.IsSmooth V → ∀ v0 : Fin m → ℂ, v0 ≠ 0 →
      ∃ (S : Submodule ℂ (Fin m → ℂ)) (p : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)),
        S ≠ ⊥ ∧ (∀ k, ∀ s ∈ S, V k s ∈ S) ∧
        (∀ S' : Submodule ℂ (Fin m → ℂ), S' ≤ S → (∀ k, ∀ s ∈ S', V k s ∈ S') → S' = ⊥ ∨ S' = S) ∧
        (∀ v, p v ∈ S) ∧ (∀ s ∈ S, p s = s) ∧ (∀ k v, p (V k v) = V k (p v)) ∧ p v0 ≠ 0

def SmoothRepMinimalSubrepresentation : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] (m : ℕ)
    (V : Representation ℂ K (Fin m → ℂ)), GlobalTheory.PRep.IsSmooth V → ∀ S : Submodule ℂ (Fin m → ℂ), S ≠ ⊥ →
      (∀ k, ∀ s ∈ S, V k s ∈ S) →
      (∀ S' : Submodule ℂ (Fin m → ℂ), S' ≤ S → (∀ k, ∀ s ∈ S', V k s ∈ S') → S' = ⊥ ∨ S' = S) →
      ∃ (d : ℕ) (ξ : Representation ℂ K (Fin d → ℂ)) (ι : (Fin d → ℂ) →ₗ[ℂ] (Fin m → ℂ)),
        Function.Injective ι ∧ LinearMap.range ι = S ∧ (∀ k v, V k (ι v) = ι (ξ k v)) ∧ ξ.IsIrreducible ∧
        GlobalTheory.PRep.IsSmooth ξ

def SchurInjectiveFromIrreducible : Prop :=
  ∀ (K : Type) [Group K] (d : ℕ) (ξ : Representation ℂ K (Fin d → ℂ)), ξ.IsIrreducible →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) (g : (Fin d → ℂ) →ₗ[ℂ] W), g ≠ 0 →
      (∀ k v, g (ξ k v) = ρ k (g v)) → Function.Injective g

end UpperTheory.NonzeroTypeTheory
