module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.RamificationInertia.Inertia
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open Pointwise

namespace GlobalTheory

theorem isFrob_restrictScalars_of_prime_absNorm :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (Z : IntermediateField F Ω) [NumberField Z] (w : HeightOneSpectrum (𝓞 Z))
      (v : HeightOneSpectrum (𝓞 F)), w.asIdeal.LiesOver v.asIdeal →
      (Ideal.absNorm w.asIdeal).Prime → ∀ B : ValuationSubring Ω, IsPlaceOver (F := Z) B w →
      ∀ σ : G Z Ω, IsFrob B (normV w) σ →
        Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal ∧ IsPlaceOver (F := F) B v ∧
          IsFrob (F := F) B (normV v) (σ.restrictScalars F) := by
  intro F Ω _ _ _ _ _ Z _ w v hwv hp B hB σ hσ
  have hn : Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := by
    have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    have h1 := Nat.Prime.eq_one_of_pow (h ▸ hp)
    rw [h1, pow_one] at h
    exact h
  refine ⟨hn, fun x => ?_, ?_, fun x hx => ?_⟩
  · have h := hB (algebraMap (𝓞 F) (𝓞 Z) x)
    rw [← Ideal.mem_of_liesOver w.asIdeal v.asIdeal x] at h
    exact h
  · have h : σ • B = B := hσ.1
    show (σ.restrictScalars F) • B = B
    ext x
    conv_rhs => rw [← h]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  · have e : normV v = normV w := by
      simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hn
    rw [e]
    exact hσ.2 x hx

end GlobalTheory
