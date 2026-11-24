module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.twChOps :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {R : Type} [CommRing R] [IsLocalRing R] (γ : F.G₀ →* Rˣ), TwCh F γ → (∀ m : ℕ, TwCh F (γ ^ m)) ∧ TwCh F γ⁻¹ ∧ ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (e : R →+* R'), IsLocalHom e → TwCh F (pushCh e γ) := by
  intro l _ F R _ _ γ hγ
  have hq : ∀ g, Ideal.Quotient.mk (maximalIdeal R) (γ g : R) = 1 := fun g => by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hγ.red g
  refine ⟨fun m => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩, ⟨hγ.toAnti.mono ?_, ?_, ?_⟩,
    fun R' _ _ e he => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩⟩
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  · intro N
    have hc := (hγ.cont N).comp (fun x => x ^ m)
    convert hc using 1
    funext g
    simp [Function.comp]
  · intro g
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    simp [hq g]
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  · intro N
    have hc := (hγ.cont N).comp Ring.inverse
    convert hc using 1
    funext g
    have hu : Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R) =
        ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N) : R →* R ⧸ maximalIdeal R ^ N) (γ g) : _)) := rfl
    simp only [Function.comp_apply]
    rw [hu, Ring.inverse_unit, Units.coe_map_inv]
    rfl
  · intro g
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    have h2 := congrArg (Ideal.Quotient.mk (maximalIdeal R)) (γ g).inv_mul
    rw [map_mul, hq g, mul_one, map_one] at h2
    simpa using h2
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [pushCh, hg]
  · intro N
    have hle : maximalIdeal R ^ N ≤ Ideal.comap e (maximalIdeal R' ^ N) := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr (fun x hx => Ideal.mem_comap.mpr (map_nonunit e x hx))) N
    have hc := (hγ.cont N).comp (Ideal.quotientMap _ e hle)
    convert hc using 1
    funext g
    simp [pushCh, Ideal.quotientMap_mk]
  · intro g
    have h3 := map_nonunit e _ (hγ.red g)
    simpa [pushCh] using h3
