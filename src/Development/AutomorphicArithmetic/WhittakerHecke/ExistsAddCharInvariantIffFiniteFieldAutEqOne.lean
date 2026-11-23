module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.AddChar
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

theorem UpperTheory.exists_addChar_invariant_iff_finiteField_aut_eq_one :
    ∀ (K : Type) [Field K] [Finite K] (f : RingAut K), ∃ ψ : Multiplicative K →* ℂˣ, ∀ m : ℤ,
        (∀ x : K, ψ (Multiplicative.ofAdd ((f ^ m) x)) = ψ (Multiplicative.ofAdd x)) ↔ f ^ m = 1 := by
  intro K _ _ f
  classical
  haveI hp : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  haveI : NeZero (ringChar K) := ⟨hp.out.ne_zero⟩
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := Kˣ)
  let T : K →ₗ[ZMod (ringChar K)] ZMod (ringChar K) := Algebra.trace (ZMod (ringChar K)) K
  let χ : AddChar K ℂ :=
    ((ZMod.stdAddChar (N := ringChar K)).compAddMonoidHom T.toAddMonoidHom).mulShift (b : K)
  have hχ : ∀ x : K, χ x = ZMod.stdAddChar (T ((b : K) * x)) := fun x => rfl
  refine ⟨χ.toMonoidHom.toHomUnits, fun m => ⟨fun h => ?_, fun h x => by rw [h]; rfl⟩⟩
  generalize f ^ m = g at h ⊢
  have h1 : ∀ x : K, T ((b : K) * g x) = T ((b : K) * x) := by
    intro x
    apply ZMod.injective_stdAddChar
    rw [← hχ, ← hχ]
    exact congrArg Units.val (h x)
  have hT : ∀ y : K, T (g y) = T y := by
    intro y
    let e : K ≃ₐ[ZMod (ringChar K)] K := AlgEquiv.ofRingEquiv (f := g) (fun c => by
      have := RingHom.ext_zmod ((g : K →+* K).comp (algebraMap (ZMod (ringChar K)) K))
        (algebraMap (ZMod (ringChar K)) K)
      exact DFunLike.congr_fun this c)
    exact Algebra.trace_eq_of_algEquiv e y
  have h2 : g (b : K) = (b : K) := by
    by_contra hne
    have hne' : (b : K) - g (b : K) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0).symm
    obtain ⟨y, hy⟩ := FiniteField.trace_to_zmod_nondegenerate K hne'
    apply hy
    obtain ⟨x, rfl⟩ := g.surjective y
    change T (((b : K) - g b) * g x) = 0
    rw [sub_mul, map_sub, h1, ← map_mul, hT, sub_self]
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hb (Units.mk0 x hx))
    have hxn : x = (b : K) ^ n := by
      rw [← Units.val_zpow_eq_zpow_val, hn]; rfl
    rw [hxn, map_zpow₀, h2]
    rfl
