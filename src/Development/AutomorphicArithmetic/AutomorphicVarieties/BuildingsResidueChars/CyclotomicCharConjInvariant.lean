module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.cyclotomic_char_conj_invariant :
    UpperTheory.V.Af.Sol.CycConj := by
  intro F Ω _ _ _ _ _ l _ c hc
  obtain ⟨j, hj⟩ := hc
  haveI : CharZero Ω := j.charZero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero⟩
  have hinv : ∀ (x : Ω) (m : ℕ), m ≠ 0 → x ^ m = 1 → c x = x⁻¹ := by
    intro x m hm hx
    apply j.injective
    rw [hj, map_inv₀]
    have hn : ‖j x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hx, map_one]) hm
    have hs : Complex.normSq (j x) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn]; norm_num
    rw [Complex.inv_def, hs]; simp
  set g : Ω ≃+* Ω := MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G F Ω) Ω c with hg
  have hcyc : cyclotomicCharacter Ω l g = -1 := by
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow]
    have hk : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime l).ne_zero⟩
    rw [← modularCyclotomicCharacter.unique Ω _ g (c := -1)]
    · simp
    · intro t ht
      have ht' : (t : Ω) ^ (l ^ n) = 1 := by
        rw [mem_rootsOfUnity] at ht
        simpa using congrArg Units.val ht
      have hdvd : l ^ n ∣ (-1 : ZMod (l ^ n)).val + 1 := by
        rw [← ZMod.natCast_eq_zero_iff]; push_cast; simp
      obtain ⟨m, hm⟩ := hdvd
      have hne : (t : Ω) ≠ 0 := t.ne_zero
      have key : (t : Ω) ^ (-1 : ZMod (l ^ n)).val = (t : Ω)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, hm, pow_mul, ht', one_pow]
      rw [key]
      exact hinv _ (l ^ n) (NeZero.ne _) ht'
  show Units.map _ (ReciprocityTheory.Gal.cycZ F Ω l c) = -1
  have : ReciprocityTheory.Gal.cycZ F Ω l c = -1 := hcyc
  rw [this]
  ext; simp
