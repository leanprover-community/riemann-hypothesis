module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkApply_dc_congr {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (K K' : Subgroup G) {x y : G}
    (h : MulAction.orbit K (x : G ⧸ K') = MulAction.orbit K (y : G ⧸ K')) :
    dc ρ K K' x = dc ρ K K' y := by
  unfold dc
  rw [h]

private theorem hkApply_orbit {G : Type} [Group G] (K K' : Subgroup G) (x : G) {a b : G} (ha : a ∈ K) (hb : b ∈ K') :
    MulAction.orbit K ((a * x * b : G) : G ⧸ K') = MulAction.orbit K (x : G ⧸ K') := by
  have h1 : ((a * x * b : G) : G ⧸ K') = (⟨a, ha⟩ : K) • (x : G ⧸ K') := by
    rw [QuotientGroup.mk_mul_of_mem _ hb]
    rfl
  rw [h1, MulAction.orbit_smul]

theorem UpperTheory.V.AlgebraTools.hkApply :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (K K' : Subgroup G) (x : G), FinOrb K K' x → (∀ v : fixd ρ K', (hk2 ρ K K' x v : M) = dc ρ K K' x v) ∧ (∀ s : Finset G, (∀ y ∈ s, (y : G ⧸ K') ∈ MulAction.orbit K (x : G ⧸ K')) → (∀ q ∈ MulAction.orbit K (x : G ⧸ K'), ∃! y, y ∈ s ∧ (y : G ⧸ K') = q) → ∀ v : fixd ρ K', (hk2 ρ K K' x v : M) = ∑ y ∈ s, ρ y v) ∧ ∀ a ∈ K, ∀ b ∈ K', hk2 ρ K K' (a * x * b) = hk2 ρ K K' x := by
  intro A G M _ _ _ _ ρ K K' x hfin
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.Hi.dcSum A G M ρ K K' x hfin
  have hv : ∀ v : fixd ρ K', (hk2 ρ K K' x v : M) = dc ρ K K' x v := by
    intro v
    unfold hk2
    rw [dite_eq_left h2]
    rfl
  refine ⟨hv, fun s hs hu v => ?_, fun a ha b hb => ?_⟩
  · rw [hv, h1 s hs hu v v.2]
  · have h := hkApply_dc_congr ρ K K' (hkApply_orbit K K' x ha hb)
    unfold hk2
    rw [h]
