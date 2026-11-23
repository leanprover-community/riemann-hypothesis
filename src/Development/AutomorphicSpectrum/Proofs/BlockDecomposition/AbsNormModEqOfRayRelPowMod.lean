module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClass
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.RayFacts

theorem absNorm_span_modEq_one {F : Type} [Field F] [NumberField F] (l m : ℕ) {a : 𝓞 F} (ha : a ≠ 0)
    (ha1 : a - 1 ∈ powMod F l m) (hpos : ∀ σ : F →+* ℝ, 0 < σ (a : F)) :
    Ideal.absNorm (Ideal.span {a}) ≡ 1 [MOD l ^ m] := by
  have hn : 0 < Algebra.norm ℤ a := by
    have h := GlobalTheory.RayRootOfUnity.norm_pos_of_pos_real (x := (a : F)) (by simpa using ha) hpos
    rw [← Algebra.coe_norm_int] at h
    exact_mod_cast h
  have hc := GlobalTheory.Mem.RayNorm.norm_cast_eq F (l ^ m) (x := a) (y := 1) (by
    have e : ((l ^ m : ℕ) : 𝓞 F) = (l : 𝓞 F) ^ m := by push_cast; rfl
    rw [e]
    exact ha1)
  rw [map_one, Int.cast_one] at hc
  have h2 := congrArg (Int.cast : ℤ → ZMod (l ^ m)) (Int.natAbs_of_nonneg hn.le)
  rw [Int.cast_natCast] at h2
  rw [← ZMod.natCast_eq_natCast_iff, Ideal.absNorm_span_singleton, h2, hc, Nat.cast_one]

theorem absNorm_modEq_of_rayRel_powMod : ∀ (F : Type) [Field F] [NumberField F] (l m : ℕ) (I J : Ideal (𝓞 F)),
    RayRel F (powMod F l m) I J → Ideal.absNorm I ≡ Ideal.absNorm J [MOD l ^ m] := by
  intro F _ _ l m I J h
  obtain ⟨a, b, ha, hb, ha1, hb1, hσ, he⟩ := h
  have h1 := absNorm_span_modEq_one l m ha ha1 fun σ => (hσ σ).1
  have h2 := absNorm_span_modEq_one l m hb hb1 fun σ => (hσ σ).2
  have h3 := congrArg Ideal.absNorm he
  rw [map_mul, map_mul] at h3
  calc Ideal.absNorm I = 1 * Ideal.absNorm I := (one_mul _).symm
    _ ≡ Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm I [MOD l ^ m] := h1.symm.mul_right _
    _ = Ideal.absNorm (Ideal.span {b}) * Ideal.absNorm J := h3
    _ ≡ 1 * Ideal.absNorm J [MOD l ^ m] := h2.mul_right _
    _ = Ideal.absNorm J := one_mul _

end GlobalTheory.CompanionTheory.RayFacts
