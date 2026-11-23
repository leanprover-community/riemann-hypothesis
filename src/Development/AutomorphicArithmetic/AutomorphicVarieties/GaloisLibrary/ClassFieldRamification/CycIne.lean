module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cycIne :
    ∀ (N : ℕ) [NeZero N] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C] (ζ : C) (p : ℕ), p.Prime → IsPrimitiveRoot ζ N → ∀ w : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ w.asIdeal → ∀ (σ : Gal(C/ℚ)) (a : ℕ), σ ζ = ζ ^ a → (σ ∈ w.asIdeal.inertia Gal(C/ℚ) ↔ a ≡ 1 [MOD ordCompl[p] N]) ∧ (σ ∈ MulAction.stabilizer Gal(C/ℚ) w.asIdeal ↔ ∃ i : ℕ, a ≡ p ^ i [MOD ordCompl[p] N]) := by
  intro N _ C _ _ _ ζ p hp hζ w hw σ a hσ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := w.isPrime
  haveI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
        (Nat.prime_iff_prime_int.1 hp)).isMaximal (by simpa using hp.ne_zero)
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
    simpa using hw
  have hne : NeZero (ordCompl[p] N) := ⟨(Nat.ordCompl_pos p (NeZero.ne N)).ne'⟩
  have hmem : ∀ H : Subgroup Gal(C/ℚ), σ ∈ H ↔ IsCyclotomicExtension.Rat.galEquivZMod N C σ ∈
      H.map (IsCyclotomicExtension.Rat.galEquivZMod N C).toMonoidHom := fun H =>
    (Subgroup.mem_map_iff_mem (f := (IsCyclotomicExtension.Rat.galEquivZMod N C).toMonoidHom)
      (IsCyclotomicExtension.Rat.galEquivZMod N C).injective).symm
  have ha : ((IsCyclotomicExtension.Rat.galEquivZMod N C σ : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) := by
    have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N C σ hζ.pow_eq_one
    rw [hσ, (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val] at h
    exact h.symm
  have hb : ((ZMod.unitsMap (Nat.ordCompl_dvd N p) (IsCyclotomicExtension.Rat.galEquivZMod N C σ) :
      (ZMod (ordCompl[p] N))ˣ) : ZMod (ordCompl[p] N)) = (a : ZMod (ordCompl[p] N)) := by
    rw [ZMod.unitsMap_val, ha, ZMod.cast_natCast (Nat.ordCompl_dvd N p)]
  constructor
  · rw [hmem, KStar.Ram.map_inertia_eq p, KStar.Ram.inertiaUnits, MonoidHom.mem_ker, Units.ext_iff, hb,
      ← ZMod.natCast_eq_natCast_iff, Nat.cast_one, Units.val_one]
  · rw [hmem, KStar.Ram.map_stabilizer_eq p, KStar.Ram.decompUnits, Subgroup.mem_comap,
      ← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]
    refine exists_congr fun i => ?_
    rw [Units.ext_iff, hb, ← ZMod.natCast_eq_natCast_iff, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime, Nat.cast_pow, eq_comm]
