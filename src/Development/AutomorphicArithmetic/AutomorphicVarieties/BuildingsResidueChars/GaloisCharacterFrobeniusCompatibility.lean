module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
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

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.galois_character_frobenius_compatibility :
    UpperTheory.V.Af.Sol.CharFrob := by
  intro F Ω _ _ _ _ _ l _ ι χ μ hχ
  obtain ⟨_, art, a, hart, _, hL⟩ := hχ
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (l : 𝓞 F) ∉ v.asIdeal := by
    have hne : Ideal.span {(l : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hne).subset ?_)
    intro v hv
    simp only [Set.mem_setOf_eq, not_not] at hv ⊢
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  filter_upwards [GlobalTheory.GalChar.unr_ae χ, hl] with v hu hv
  refine ⟨hu, fun A hA => ⟨(GlobalTheory.HeckeGal.IsLAdicOf.unr_iff hart hL (Or.inl hv) hA).2 hu, fun σ hσ => ?_⟩⟩
  have h := GlobalTheory.HeckeGal.IsLAdicOf.frob_unr hart hL (Or.inl hv) hu hA hσ
  rw [map_inv, Units.val_inv_eq_inv_val, h, inv_inv, RingEquiv.apply_symm_apply]
