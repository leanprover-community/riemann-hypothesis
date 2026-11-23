module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Imports
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Formalism.GaloisCohomology.Statement
public import Mathlib.FieldTheory.Galois.Infinite
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.radExists :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) [NeZero n] (ζ : Ω) (η z : G K Ω → ZMod n), IsPrimitiveRoot ζ n → (∀ g : G K Ω, g ζ = ζ ^ (η g).val) → IsLocallyConstant z → (∀ g h, z (g * h) = z g + η g * z h) →
    ∃ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a ∧ ∀ g : G K Ω, g β = ζ ^ (z g).val * β := by
  intro K Ω _ _ _ _ _ n _ ζ η z hζ hη hz hc
  have hmod : ∀ m : ℕ, ζ ^ (m % n) = ζ ^ m := fun m => (pow_eq_pow_mod m hζ.pow_eq_one).symm
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  obtain ⟨β, hβ0, hβ⟩ := UpperTheory.V.Kum.h90 K Ω (fun g => ζ ^ (z g).val)
    (hz.comp fun x : ZMod n => ζ ^ x.val) (fun g => pow_ne_zero _ hζ0) (fun g h => by
      show ζ ^ (z (g * h)).val = ζ ^ (z g).val * g (ζ ^ (z h).val)
      rw [hc, ZMod.val_add, hmod, pow_add, ZMod.val_mul, hmod, map_pow, hη, ← pow_mul])
  haveI : IsGalois K Ω := {}
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g (β ^ n) = β ^ n := fun g => by
    rw [map_pow, hβ g, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β ^ n)).2 hfix
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact pow_ne_zero n hβ0 ha.symm
  exact ⟨β, Units.mk0 a ha0, ha.symm, hβ⟩
