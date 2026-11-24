module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightSpaceFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KStableHighestWeightVector
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Regular.Flat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

theorem UpperTheory.V.CA.cpl_cm :
    ∀ (S R : Type) [CommRing S] [IsLocalRing S] [CommRing R] [IsLocalRing R] [Algebra S R], IsCplAt (maximalIdeal S) R → IsCM S → IsCM R ∧ DimFormula R ∧ DimFormula S ∧ ringKrullDim R = ringKrullDim S := by
  intro S R _ _ _ _ _ hR hS
  haveI : IsNoetherianRing S := hS.1
  haveI : IsNoetherianRing R := hR.noeth
  haveI : Module.Flat S R := (c3a (maximalIdeal S) hR).1
  have hdim : ringKrullDim R = ringKrullDim S := by
    have h := (c3c (maximalIdeal S) hR).1 ⊥
    rw [Ideal.map_bot] at h
    unfold dimAt at h
    rw [Ideal.map_bot] at h
    have hu : (maximalIdeal S).primeCompl ≤ IsUnit.submonoid S := fun x hx =>
      IsLocalRing.notMem_maximalIdeal.mp hx
    have e : S ≃+* Localization.AtPrime (maximalIdeal S) :=
      (IsLocalization.atUnits S (maximalIdeal S).primeCompl hu).toRingEquiv
    rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R), h,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_eq_of_ringEquiv e.symm]
  have hcomap : Ideal.comap (algebraMap S R) (maximalIdeal R) = maximalIdeal S := by
    simpa using hR.comap_pow 1
  have hRCM : IsCM R := by
    obtain ⟨-, n, hn, rs, hlen, hmem, hreg⟩ := hS
    have hmem' : ∀ r ∈ rs.map (algebraMap S R), r ∈ maximalIdeal R := by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      have : a ∈ Ideal.comap (algebraMap S R) (maximalIdeal R) := by
        rw [hcomap]
        exact hmem a ha
      exact this
    refine ⟨inferInstance, n, hdim.trans hn, rs.map (algebraMap S R), by simp [hlen], hmem', ?_⟩
    exact (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem').mpr
      hreg.toIsWeaklyRegular.of_flat
  exact ⟨hRCM, fun p _ => hRCM.height_add_ringKrullDim_quotient p,
    fun p _ => hS.height_add_ringKrullDim_quotient p, hdim⟩
