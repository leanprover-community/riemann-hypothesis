module

public import ReciprocityTheory.Hypotheses.GalCohDefs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_dual :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [Module (ZMod (l ^ 1)) k] (Γ : Type) [Group Γ] (μ : Γ →* (ZMod (l ^ 1))ˣ) (ρ : Representation (ZMod (l ^ 1)) Γ k) (g : Γ) (c : k), (∀ m, ρ g m = c * m) → c ≠ ZMod.castHom (dvd_pow_self l one_ne_zero) k (μ g) → H0 (twDual μ ρ) = ⊥ := by
  intro l _ k _ _ _ Γ _ μ ρ g c hc hne
  set a : k := ZMod.castHom (dvd_pow_self l one_ne_zero) k (μ g) with ha
  rw [eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_bot]
  have h : twDual μ ρ g φ = φ := hφ g
  have hne' : c - a ≠ 0 := sub_ne_zero.mpr hne
  have hsmul : ∀ m : k, a * m = ((μ g : ZMod (l ^ 1))) • m := by
    intro m
    rw [ha, ZMod.castHom_apply, ZMod.cast_eq_val, ← nsmul_eq_mul,
      ← Nat.cast_smul_eq_nsmul (ZMod (l ^ 1)), ZMod.natCast_zmod_val]
  have hinv : ∀ m : k, ρ g⁻¹ (ρ g m) = m := by
    intro m
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let ψ : k →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) := φ
  have key : ∀ m : k, ψ ((c - a) * m) = 0 := by
    intro m
    have h1 : (twDual μ ρ g φ) (ρ g m) = φ (ρ g m) := by rw [h]
    rw [twDual_apply, hinv, hc] at h1
    change (μ g : ZMod (l ^ 1)) * ψ m = ψ (c * m) at h1
    rw [sub_mul, map_sub, hsmul, map_smul, ← h1, smul_eq_mul, sub_self]
  apply LinearMap.ext
  intro x
  have hx : x = (c - a) * ((c - a)⁻¹ * x) := by
    rw [← mul_assoc, mul_inv_cancel₀ hne', one_mul]
  change ψ x = 0
  rw [hx, key]
