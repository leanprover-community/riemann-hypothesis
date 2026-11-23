module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.CokerTors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.L1MapDomainLeAndL1FaceDSingleLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.QuotientsEquivOfKerEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport
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

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.base :
    ∀ (G X Y : Type) [Group G] [MulAction G X] (M : Rep ℤ G) (e : permRep G X ⟶ M)
      (d : (Y →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ)) (A b : ℕ), Function.Surjective e.hom → Function.Exact d e.hom →
      OrbLe G X A → 1 ≤ b → (∀ y, l1 (d (Finsupp.single y 1)) ≤ b) →
      TorsLe (groupHomology M 0) (b ^ A) := by
  intro G X Y _ _ M e d A b hsurj hex hA hb hd
  set S : Set (X →₀ ℤ) := Set.range (fun y => d (Finsupp.single y 1)) with hS
  have hspan : Submodule.span ℤ S = LinearMap.range d := by
    have h1 : S = d '' Set.range (fun y : Y => Finsupp.single y (1 : ℤ)) := by
      rw [hS, ← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, ← Submodule.map_top]
    congr 1
    have := (Finsupp.basisSingleOne (R := ℤ) (ι := Y)).span_eq
    rw [Finsupp.coe_basisSingleOne] at this
    exact this
  have hker : ∀ f : X →₀ ℤ, e.hom f = 0 ↔ f ∈ Submodule.span ℤ S := by
    intro f
    rw [hspan, LinearMap.mem_range]
    exact (hex f).trans Set.mem_range
  obtain ⟨φ⟩ := hZero G X M e S hsurj hker
  have hL : ∀ x ∈ Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel G X)) '' S, l1 x ≤ b := by
    rintro x ⟨s, ⟨y, rfl⟩, rfl⟩
    exact (l1_mapDomain_le_and_l1_faceD_single_le.1 _ _ _ _).trans (hd y)
  have hT := cokerTors (MulAction.orbitRel.Quotient G X) A b _ hA hb hL
  exact transport.1 _ _ φ.symm _ hT
