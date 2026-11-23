module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfPairField

open Module

theorem eq_zero_of_mem_of_flip_ker {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (φ : V →ₗ[K] W →ₗ[K] K) (A : Submodule K V) (B : Submodule K W)
    (hdim : finrank K A + finrank K B ≤ finrank K W)
    (h : ∀ y, (∀ x ∈ A, φ x y = 0) → y ∈ B) :
    ∀ x ∈ A, φ x = 0 → x = 0 := by
  intro x hx hφx
  set T : W →ₗ[K] Module.Dual K A := (φ.domRestrict A).flip with hT
  have hker : LinearMap.ker T ≤ B := by
    intro y hy
    apply h y
    intro a ha
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) ⟨a, ha⟩
    simpa [hT] using this
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have hkb := Submodule.finrank_mono hker
  have hdA : finrank K (Module.Dual K A) = finrank K A := Subspace.dual_finrank_eq
  have htop : LinearMap.range T = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (LinearMap.range T)
    omega
  have hx0 : (⟨x, hx⟩ : A) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro f
    obtain ⟨y, rfl⟩ : f ∈ LinearMap.range T := htop ▸ Submodule.mem_top
    simp [hT, hφx]
  simpa using congrArg Subtype.val hx0

end GlobalTheory.PerfPairField

open Module in
theorem GlobalTheory.PerfPairField.isPerfPair_of_kernel_conditions : ∀ (k : Type) [Field k] (M N : Type 1) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [FiniteDimensional k M] [FiniteDimensional k N] (F : Submodule k M) (F' : Submodule k N) (g : ℕ), Module.finrank k M = 2 * g → Module.finrank k N = 2 * g → Module.finrank k F = g → Module.finrank k F' = g → ∀ φ : Module.Dual k M →ₗ[k] Module.Dual k N →ₗ[k] k, (∀ x, (∀ y ∈ F'.dualAnnihilator, φ x y = 0) → x ∈ F.dualAnnihilator) → (∀ y, (∀ x ∈ F.dualAnnihilator, φ x y = 0) → y ∈ F'.dualAnnihilator) → φ.IsPerfPair := by
  intro k _ M N _ _ _ _ _ _ F F' g hM hN hF hF' φ h1 h2
  have eM := Subspace.finrank_add_finrank_dualAnnihilator_eq F
  have eN := Subspace.finrank_add_finrank_dualAnnihilator_eq F'
  have dM : finrank k (Module.Dual k M) = 2 * g := by rw [Subspace.dual_finrank_eq, hM]
  have dN : finrank k (Module.Dual k N) = 2 * g := by rw [Subspace.dual_finrank_eq, hN]
  apply LinearMap.IsPerfPair.of_injective
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hA : x ∈ F.dualAnnihilator := h1 x (fun y _ => by simp [hx])
    exact GlobalTheory.PerfPairField.eq_zero_of_mem_of_flip_ker φ F.dualAnnihilator F'.dualAnnihilator
      (by omega) h2 x hA hx
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hB : y ∈ F'.dualAnnihilator := h2 y (fun x _ => by
      have := LinearMap.congr_fun hy x
      simpa using this)
    exact GlobalTheory.PerfPairField.eq_zero_of_mem_of_flip_ker φ.flip F'.dualAnnihilator F.dualAnnihilator
      (by omega) (fun x hx => h1 x (fun y hy => by simpa using hx y hy)) y hB hy
