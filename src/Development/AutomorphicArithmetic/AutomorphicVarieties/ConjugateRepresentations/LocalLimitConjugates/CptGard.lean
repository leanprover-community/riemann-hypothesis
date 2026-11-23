module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.DmTest
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.IsOpenMapVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OrbConv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OrbLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
private theorem summable_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {u v : G → ℂ} (hu : HasCompactSupport u)
    (hv : HasCompactSupport v) (x : G) : Summable fun γ : Γ => GlobalTheory.AutomorphicL2Unitary.conv μ u v (γ * x) := by
  obtain ⟨N, hN⟩ := (locInt G Γ μ).2 _ (IsCompact.mul hu hv)
  refine summable_of_hasFiniteSupport ((Set.finite_of_encard_le_coe (hN x)).subset fun γ hγ => ?_)
  by_contra hn
  refine hγ ?_
  have h0 : (fun y => u y * v (y⁻¹ * ((γ : G) * x))) = 0 := by
    funext y
    by_contra hy
    exact hn ⟨y, subset_tsupport u (left_ne_zero_of_mul hy), y⁻¹ * ((γ : G) * x),
      subset_tsupport v (right_ne_zero_of_mul hy), mul_inv_cancel_left _ _⟩
  simp only [GlobalTheory.AutomorphicL2Unitary.conv, h0]
  simp

theorem UpperTheory.V.Cj.H.cptGard :
    UpperTheory.V.Cj.H.CptGard := by
  intro E _ _ _ a μ _ _ φ hl hi C hC hs
  obtain ⟨f, hf, hφ⟩ := orbLift E a φ hl hi C hC hs
  obtain ⟨k, u, v, huv, hsum⟩ := dmTest E a μ f hf
  have hc : ∀ ψ : Sm E a, IsTest ψ → Continuous ψ.1 := fun ψ h => ((testOps E a ψ).1 h.2).1
  choose h hh using fun i => orbConv (GA E a) (latticeGL E a) μ (u i).1 (v i).1 (hc _ (huv i).1) (huv i).1.1
    (hc _ (huv i).2) (huv i).2.1
  have e : φ = ∑ i, (⟨cv (v i).1 (h i).toL2, cvSm E a μ (v i) (huv i).2 _⟩ : Sm E a) := by
    apply Subtype.ext
    rw [hφ, hsum, Submodule.coe_sum]
    funext x
    simp only [Finset.sum_apply, ← hh, GlobalTheory.AutomorphicL2Unitary.orbitSum]
    exact Summable.tsum_finsetSum fun i _ => summable_conv _ μ (huv i).1.1 (huv i).2.1 x
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨v i, (h i).toL2, (huv i).2, rfl⟩
