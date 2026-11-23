module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanImageDenominators
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image {A F M N : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M) (y : N)
    (hy : y ∈ Submodule.span F (φ '' T)) :
    ∃ d : A, d ≠ 0 ∧ ∃ w ∈ Submodule.span A T, d • y = φ w :=
  _root_.UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image φ T y hy

theorem UpperTheory.V.Pa.Det.spanInt :
    ∀ {K ι : Type} [Field K] {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) (PowerSeries K)) (S : Set ι), Submodule.span (FractionRing (PowerSeries K)) ((fun i => (r i).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) '' S) = Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a → ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ, (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) (r '' S) := by
  intro K ι _ n a r S h Z hZ
  let φ : Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[PowerSeries K]
      Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K)) :=
    (Algebra.linearMap (PowerSeries K) (FractionRing (PowerSeries K))).mapMatrix
  have hφ : ∀ Y, φ Y = Y.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) := fun _ => rfl
  have hinj : Function.Injective φ :=
    Matrix.map_injective (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hmem : φ Z ∈ Submodule.span (FractionRing (PowerSeries K)) (φ '' (r '' S)) := by
    rw [Set.image_image]
    simp only [hφ]
    rw [h]
    intro i j
    refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
    have : Z i j = 0 := (Submodule.mem_bot _).1 ((hZ i j).2 hij)
    simp [this]
  obtain ⟨d, hd, w, hw, e⟩ := UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image φ _ _ hmem
  rw [← map_smul] at e
  have e' := hinj e
  obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd
    (PowerSeries.X_irreducible (R := K))
  refine ⟨s, ?_⟩
  have : (PowerSeries.X : PowerSeries K) ^ s • Z = (↑u⁻¹ : PowerSeries K) • w := by
    rw [← e', smul_smul, Units.inv_mul_cancel_left]
  rw [this]
  exact Submodule.smul_mem _ _ hw
