module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem mem_locSp_of_natCast_smul_mem {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N' : ℕ} (L' : Submodule (𝓞 E) (Fin N' → E)) (z : Fin N' → E) (s : ℕ) (hs : IsUnit (s : W))
    (hz : (s : E) • z ∈ L') : (fun k => ρ (z k)) ∈ locSp W ρ L' := by
  obtain ⟨u, hu'⟩ := hs
  have hmem : (fun k => ρ (((s : E) • z) k)) ∈ locSp W ρ L' := Submodule.subset_span ⟨_, hz, rfl⟩
  have e : (fun k => ρ (z k)) = ((↑u⁻¹ : W)) • (fun k => ρ (((s : E) • z) k)) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Algebra.smul_def]
    rw [← mul_assoc, ← map_natCast (algebraMap W K) s, ← hu', ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

theorem locSp_maps_of_unit_smul {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N N' : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E))
    (A : Matrix (Fin N') (Fin N) E) (s : ℕ) (hs : IsUnit (s : W)) (hA : ∀ x ∈ L, (s : E) • (A *ᵥ x) ∈ L') :
    ∀ z ∈ locSp W ρ L, (A.map ρ) *ᵥ z ∈ locSp W ρ L' := by
  intro w hw
  have h : locSp W ρ L ≤ (locSp W ρ L').comap (((A.map ρ).mulVecLin).restrictScalars W) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show (A.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ L'
    have e : (A.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((A *ᵥ x) k) := by
      funext k
      exact (RingHom.map_mulVec ρ A x k).symm
    rw [e]
    exact mem_locSp_of_natCast_smul_mem W K ρ L' _ s hs (hA x hx)
  exact h hw

end GlobalTheory.TwV

end
