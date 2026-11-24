module

public import Formalism.HermitianLattices.StatementMass
public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MassBasicAux

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

theorem massBasic_sum_cast (h : V →ₗ⋆[K] V →ₗ[K] K)
    (s : Finset (Submodule (RingOfIntegers K) V)) :
    (((∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) =
      Formalism.ThetaLiftIndependence.latLift h s (fun _ => 1) (fun _ => 1) := by
  simp [Formalism.ThetaLiftIndependence.latLift, Formalism.ThetaLiftIndependence.latWt]

theorem massBasic_mass_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V)
    (hs : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    mass h L = ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ := by
  unfold mass
  rw [dite_eq_left hs]

theorem massBasic_self_mem_genus (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V)
    (hL : Submodule.IsFullLattice K L) : L ∈ genus h L := by
  rw [genus, Set.mem_setOf_eq]
  refine ⟨hL, ?_⟩
  intro p _
  refine ⟨1, (isom h).one_mem, ?_⟩
  ext x
  simp [gmap]

end MassBasicAux

theorem massBasic :
    ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
      (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
      (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
      ∀ L : Submodule (RingOfIntegers K) V, Submodule.IsFullLattice K L →
        (∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s) ∧
        (∀ s, Formalism.ThetaLiftIndependence.IsClassReps h L s →
          mass h L = ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹) ∧
        0 < mass h L := by
  intro K V _ _ _ _ _ _ _ _ h hh hpos L hL
  obtain ⟨hex, hwt, -⟩ := Formalism.ThetaLiftIndependence.classRepsDefinite K V h hh hpos L hL.toIsLattice
  refine ⟨hex, fun s hs => ?_, ?_⟩
  · rw [massBasic_mass_eq h L hex]
    have e := Formalism.ThetaLiftIndependence.latLiftIndep K V h L (fun _ => 1) (fun _ => 1)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs
    rw [← massBasic_sum_cast, ← massBasic_sum_cast] at e
    exact_mod_cast e
  · rw [massBasic_mass_eq h L hex]
    obtain ⟨hmem, huniq⟩ := hex.choose_spec
    obtain ⟨N, ⟨hN, -⟩, -⟩ := huniq L (massBasic_self_mem_genus h L hL)
    apply Finset.sum_pos
    · intro M hM
      obtain ⟨n, hn, hnw⟩ := hwt M (hmem M hM)
      have hc : Nat.card (Formalism.ThetaLiftIndependence.autL h M) = n := by
        simp only [Formalism.ThetaLiftIndependence.latWt] at hnw
        exact_mod_cast inv_inj.mp hnw
      rw [hc]
      exact inv_pos.mpr (by exact_mod_cast hn)
    · exact ⟨N, hN⟩

end Formalism.HermitianLatticesTheory
