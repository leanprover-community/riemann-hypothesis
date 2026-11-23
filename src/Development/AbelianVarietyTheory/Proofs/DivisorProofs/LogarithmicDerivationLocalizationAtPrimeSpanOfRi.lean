module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem logDerivation_atPrime_span : ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (I : Ideal A) (n : ℕ) (b : Fin n → Derivation ℤ A A), (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∀ D' : Derivation F R R, (∀ f ∈ I.map (algebraMap A R), D' f ∈ I.map (algebraMap A R)) → ∃ c : Fin n → R, ∀ a : A, D' (algebraMap A R a) = ∑ j, c j * algebraMap A R (b j a) := by
  intro F A R _ _ _ _ _ _ _ _ _ P _ _ I n b hb D' hD'
  classical

  have hloc : IsLocalizedModule P.primeCompl (Algebra.linearMap A R) :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have : Module.FinitePresentation A Ω[A⁄F] := Module.finitePresentation_of_finite _ _
  let Dc : Derivation F A R := D'.compAlgebraMap A
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    P.primeCompl (Algebra.linearMap A R) Dc.liftKaehlerDifferential
  let D₀ : Derivation F A A := h.compDer (KaehlerDifferential.D F A)
  have hD₀ : ∀ y : A, algebraMap A R (D₀ y) = algebraMap A R (s : A) * D' (algebraMap A R y) := by
    intro y
    have := congrArg (fun φ => φ (KaehlerDifferential.D F A y)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
      LinearMap.smul_apply, Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    simpa [D₀, Dc] using this

  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian I : I.FG)
  have hgen : ∀ g ∈ G, ∃ t ∈ P.primeCompl, t * D₀ g ∈ I := by
    intro g hg
    have hgI : g ∈ I := hG ▸ Ideal.subset_span hg
    have : algebraMap A R (D₀ g) ∈ I.map (algebraMap A R) := by
      rw [hD₀]
      exact Ideal.mul_mem_left _ _ (hD' _ (Ideal.mem_map_of_mem _ hgI))
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl R I _).mp this
  choose! tg htgP htgI using hgen
  let t' : A := ∏ g ∈ G, tg g
  have ht'P : t' ∈ P.primeCompl := by
    have := prod_mem (S := P.primeCompl) (t := G) (f := tg) (fun g hg => htgP g hg)
    simpa [t'] using this
  let D₁ : Derivation ℤ A A := t' • (D₀.restrictScalars ℤ)
  have hD₁ : ∀ x, D₁ x = t' * D₀ x := fun x => by simp [D₁, smul_eq_mul]
  have hkill : ∀ c, D₁ (algebraMap F A c) = 0 := fun c => by
    rw [hD₁, Derivation.map_algebraMap, mul_zero]
  have hkeep : ∀ f ∈ I, D₁ f ∈ I := by
    intro f hf
    rw [← hG] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rw [hD₁]
      have hd : tg x ∣ t' := Finset.dvd_prod_of_mem _ hx
      obtain ⟨k, hk⟩ := hd
      rw [hk, mul_comm (tg x) k, mul_assoc]
      exact Ideal.mul_mem_left _ _ (htgI x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
    | smul a x hxs hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ ?_)
      rw [hG] at hxs; exact hxs
  obtain ⟨c, hc⟩ := hb D₁ hkill hkeep

  have hu : IsUnit (algebraMap A R (t' * s)) :=
    IsLocalization.map_units R (⟨t' * s, P.primeCompl.mul_mem ht'P s.2⟩ : P.primeCompl)
  refine ⟨fun j => hu.unit⁻¹ * algebraMap A R (c j), fun a => ?_⟩
  have e1 : algebraMap A R (D₁ a) = ∑ j, algebraMap A R (c j) * algebraMap A R (b j a) := by
    rw [hc]
    have : ∀ (s : Finset (Fin n)), (∑ j ∈ s, c j • b j) a = ∑ j ∈ s, c j * b j a := by
      intro s; induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, Derivation.add_apply, ih, Derivation.smul_apply, smul_eq_mul]

    rw [this, map_sum]; simp only [map_mul]
  have e2 : algebraMap A R (D₁ a) = algebraMap A R (t' * s) * D' (algebraMap A R a) := by
    rw [hD₁, map_mul, hD₀, map_mul, mul_assoc]
  rw [e2] at e1
  have : D' (algebraMap A R a) = (hu.unit⁻¹ : Rˣ) * ∑ j, algebraMap A R (c j) * algebraMap A R (b j a) := by
    rw [← e1, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  rw [this, Finset.mul_sum]
  simp only [mul_assoc]

end GlobalTheory
