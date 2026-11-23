module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X
open scoped Pointwise

theorem UpperTheory.V.X.So.cobPlace :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (O : Type) [CommRing O] (θ : G k Ω →* Oˣ) (z : G k Ω → O), Coc θ z → ∀ (v : HeightOneSpectrum (𝓞 k)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → CobOn θ z (Dec (F := k) A) → CobOn θ z (Dec (F := k) A') := by
  intro k Ω _ _ _ _ _ O _ θ z hz v A A' hA hA' hcob
  obtain ⟨a, ha, m, hm⟩ := hcob
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_over hA hA'
  refine ⟨a, ha, (θ g : O) * m - a * z g, ?_⟩
  intro h hh
  obtain ⟨h0, hh0, rfl⟩ : ∃ h0 ∈ Dec (F := k) A, h = g * h0 * g⁻¹ := by
    refine ⟨g⁻¹ * h * g, ?_, by group⟩
    rw [mem_Dec] at hh ⊢
    rw [mul_smul, mul_smul, hh, inv_smul_smul]
  have e := hm h0 hh0
  have hz1 : z 1 = 0 := by
    have h11 := hz 1 1
    rw [one_mul, map_one, Units.val_one, one_mul] at h11
    linear_combination -h11
  have hinv : (θ g : O) * z g⁻¹ = - z g := by
    have h2 := hz g g⁻¹
    rw [mul_inv_cancel, hz1] at h2
    linear_combination -h2
  have hθ : θ (g * h0 * g⁻¹) = θ h0 := by
    rw [map_mul, map_mul, map_inv, mul_comm (θ g), mul_inv_cancel_right]
  rw [hθ, hz (g * h0) g⁻¹, hz g h0, map_mul, Units.val_mul]
  linear_combination (θ g : O) * e + a * (θ h0 : O) * hinv
