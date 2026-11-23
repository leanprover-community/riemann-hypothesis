module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem growth_bound_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g r J _ R x u hspan hb
  choose C k hC using hb
  have hsingle : ∀ m : Fin r, ∃ a : J → ℝ, ∑ i, a i • u i = Pi.single m 1 := by
    intro m
    have hmem : (Pi.single m (1:ℝ) : Fin r → ℝ) ∈ Submodule.span ℝ (Set.range u) := by
      rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  choose a ha using hsingle
  refine ⟨∑ m, ∑ i, |a m i| * max (C i) 0, ∑ i, k i, ?_⟩
  intro s hs
  have h1 : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hpow : ∀ i, (1 + ‖s‖) ^ (k i) ≤ (1 + ‖s‖) ^ (∑ j, k j) := fun i =>
    pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
  have hm : ∀ m, ‖x s m‖ ≤ (∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
    intro m
    have hid : x s m = ∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m' := by
      have e := congrFun (ha m)
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hc : ∀ m', ∑ i, ((a m i : ℂ) * (u i m' : ℂ)) • x s m'
          = (((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℝ) : ℂ) • x s m' := by
        intro m'
        rw [← Finset.sum_smul]
        congr 1
        have h2 := e m'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
        rw [← h2]; push_cast; rfl
      rw [Finset.sum_congr rfl (fun m' _ => hc m')]
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · intro h; exact absurd (Finset.mem_univ m) h
    rw [hid]
    calc ‖∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖
        ≤ ∑ i, ‖(a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖ := norm_sum_le _ _
      _ ≤ ∑ i, |a m i| * (max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j)) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ C i * (1 + ‖s‖) ^ (k i) := hC i s hs
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (k i) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j) :=
              mul_le_mul_of_nonneg_left (hpow i) (le_max_right _ _)
      _ = _ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have hnn : ∀ m, 0 ≤ ∑ i, |a m i| * max (C i) 0 := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ => hnn m) (by positivity))).2 fun m => ?_
  calc ‖x s m‖ ≤ _ := hm m
    _ ≤ (∑ m, ∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum (f := fun m => ∑ i, |a m i| * max (C i) 0)
        (fun j _ => hnn j) (Finset.mem_univ m)

end GlobalTheory
