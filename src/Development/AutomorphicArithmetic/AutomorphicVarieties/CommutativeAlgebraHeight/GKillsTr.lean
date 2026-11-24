module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinEGma
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GmaKills
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.g_kills_tr :
    ∀ {n h : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → MultFree χ h → 1 ≤ n → ∀ y : MonoidAlgebra B G, D.Kills y ↔ ∀ g : G, D.tr (MonoidAlgebra.single g 1 * y) = 0 := by
  intro n h B G _ _ _ _ _ _ _ _ _ _ D χ hc hred hmf hn y
  obtain ⟨DE, π, e, hpull, hgma, -, -, -, -, -⟩ := finE_gma D χ hc hred hmf ∅ (by simp)
  have hsurj : Function.Surjective (D.toQuot ∅) := RingCon.mkₐ_surjective _
  have htq : ∀ w, DE.tr (D.toQuot ∅ w) = D.tr w := by
    intro w
    rw [← (d_toDet D w).2.2.1]
    show (-1) ^ 1 * (DE.chi _).coeff (n - 1) = (-1) ^ 1 * (D.toDet.chi w).coeff (n - 1)
    rw [← hpull, (d_pull DE (D.toQuot ∅)).1 w]
  obtain ⟨t, ht⟩ := (d_tr D.toDet).1 hn
  rw [← (d_toDet D y).2.2.2, ← (d_ker _ y).1]
  constructor
  · intro hy g
    have hk : D.toQuot ∅ y ∈ DE.ker := by
      rw [← hpull] at hy
      exact ((d_pull DE _).2.2.2 hsurj).1 y hy
    rw [← htq, map_mul]
    exact (gma_kills DE e hn hgma _).1 hk _
  · intro H
    have hk : D.toQuot ∅ y ∈ DE.ker := by
      rw [gma_kills DE e hn hgma]
      intro q
      obtain ⟨w, rfl⟩ := hsurj q
      rw [← map_mul, htq, ← (d_toDet D _).2.2.1, ← ht]
      refine MonoidAlgebra.induction_on (motive := fun w => t (w * y) = 0) w ?_ ?_ ?_
      · intro m
        rw [ht, (d_toDet D _).2.2.1]
        exact H m
      · intro a b ha hb
        rw [add_mul, map_add (f := _), ha, hb, add_zero]
      · intro r a ha
        rw [smul_mul_assoc, map_smul, ha, smul_zero]
    rw [← hpull]
    exact (d_pull DE _).2.1 y hk
