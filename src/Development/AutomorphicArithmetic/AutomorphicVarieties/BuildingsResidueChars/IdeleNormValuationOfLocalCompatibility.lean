module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
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

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.ideleNorm_valuation_of_local_compatibility :
    UpperTheory.V.Af.Bc.NormLoc → UpperTheory.V.Af.Bc.NormVal := by
  intro hN
  unfold UpperTheory.V.Af.Bc.NormLoc at hN
  unfold UpperTheory.V.Af.Bc.NormVal
  intro E _ _ _ χ w f hf hχ
  set u := HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w with hu
  have hunr : ∀ x : (HeightOneSpectrum.adicCompletion _ u)ˣ, IsUnitAt u x → χ.loc u x = 1 := by
    unfold HChar.UnrAt at hχ
    exact hχ
  have hloc : ∀ x : (HeightOneSpectrum.adicCompletion E w)ˣ,
      ((compNorm E) χ).loc w x = (χ : Ideles _ →* ℂˣ) (ideleNorm E (localIdele E w x)) := fun x => rfl
  have hlocF : ∀ y : (HeightOneSpectrum.adicCompletion _ u)ˣ,
      χ.loc u y = (χ : Ideles _ →* ℂˣ) (localIdele _ u y) := fun y => rfl
  constructor
  · unfold HChar.UnrAt
    intro x hx
    obtain ⟨y, hy, hv⟩ := hN E w x
    rw [hloc, hy, ← hlocF]
    apply hunr
    unfold IsUnitAt at hx ⊢
    rw [hv f hf, hx, one_pow]
  · have hvw : ((compNorm E) χ).val w = ((compNorm E) χ).loc w (atFin w (unif w)) := rfl
    have hvu : χ.val u = χ.loc u (atFin u (unif u)) := rfl
    have hpw : IsUnifAt w (atFin w (unif w)) := Classical.choose_spec (exists_unif w)
    have hpu : IsUnifAt u (atFin u (unif u)) := Classical.choose_spec (exists_unif u)
    unfold IsUnifAt at hpw hpu
    obtain ⟨y, hy, hv⟩ := hN E w (atFin w (unif w))
    rw [hvw, hvu, hloc, hy, ← hlocF, ← map_pow]
    have hone : χ.loc u (y * ((atFin u (unif u)) ^ f)⁻¹) = 1 := by
      apply hunr
      unfold IsUnitAt
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow,
        hv f hf, hpw, hpu, mul_inv_cancel₀]
      exact pow_ne_zero _ (by simp)
    rw [map_mul, map_inv, mul_inv_eq_one] at hone
    exact hone
