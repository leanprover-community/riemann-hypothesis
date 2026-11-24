module

public import GroundTheory.LocalFields.MaximalUnramified
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

noncomputable section

open IntermediateField Topology Filter

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.LocalField.Abstract

namespace FormalGroup

section UnramifiedTower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]


variable (K Ω) in
def unramifiedTowerRoot (k : ℕ) : Ω :=
  Classical.choose (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))

theorem isPrimitiveRoot_unramifiedTowerRoot (k : ℕ) :
    IsPrimitiveRoot (unramifiedTowerRoot K Ω k) (Nat.card 𝓀[K] ^ (k + 1).factorial - 1) := by
  unfold unramifiedTowerRoot
  exact Classical.choose_spec (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))


variable (K Ω) in
def unramifiedTower (k : ℕ) : IntermediateField K Ω := K⟮unramifiedTowerRoot K Ω k⟯

theorem isUnramifiedSubextension_unramifiedTower (k : ℕ) :
    IsUnramifiedSubextension (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).1

theorem finrank_unramifiedTower (k : ℕ) :
    Module.finrank K (unramifiedTower K Ω k) = (k + 1).factorial :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).2

theorem le_unramifiedTower_of_isUnramifiedSubextension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) {k : ℕ} (hk : Module.finrank K E ≤ k + 1) :
    E ≤ unramifiedTower K Ω k := by
  have := hE.1
  exact hE.le_adjoin (Nat.factorial_ne_zero _)
    (Nat.dvd_factorial Module.finrank_pos hk) (isPrimitiveRoot_unramifiedTowerRoot k)

theorem unramifiedTower_le_maximalUnramifiedExtension (k : ℕ) :
    unramifiedTower K Ω k ≤ maximalUnramifiedExtension K Ω :=
  (isUnramifiedSubextension_unramifiedTower k).le_maximalUnramifiedExtension

theorem exists_mem_unramifiedTower {x : Ω} (hx : x ∈ maximalUnramifiedExtension K Ω) :
    ∃ k, x ∈ unramifiedTower K Ω k := by
  obtain ⟨E, hE, hxE⟩ := mem_maximalUnramifiedExtension_iff.mp hx
  exact ⟨Module.finrank K E, le_unramifiedTower_of_isUnramifiedSubextension hE (Nat.le_succ _) hxE⟩

instance (k : ℕ) : IsGalois K (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_unramifiedTower k).isGalois

end UnramifiedTower

section MaxUnramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}


variable [IsGalois K Ω]

end MaxUnramified

end FormalGroup

end GroundTheory.LocalField
