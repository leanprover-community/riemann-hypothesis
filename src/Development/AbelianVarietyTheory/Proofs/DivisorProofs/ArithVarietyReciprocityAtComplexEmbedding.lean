module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithReciprocityNoCommonDivisorProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySideEqGenericFibrePullbackStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixRec

theorem injective_of_finite_int {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (σ : k →+* ℂ) : Function.Injective σ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  intro a ha
  have : a ∈ RingHom.ker σ := ha
  rwa [hker, Ideal.mem_bot] at this

theorem exists_extension {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (K : Type) [Field K] [Algebra k K] [IsFractionRing k K] (σ : k →+* ℂ) :
    ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
  ⟨IsFractionRing.lift (A := k) (K := K) (injective_of_finite_int σ),
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := K) (injective_of_finite_int σ) x).symm⟩

theorem side_symm : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP k _ X _ _ p e h σ
  haveI := h.isDomain
  haveI := h.finite
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra k K), IsFractionRing k K :=
    ⟨FractionRing k, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨τ, hτ⟩ := exists_extension K σ
  subst hτ
  intro L M N s hs t ht hcod
  obtain ⟨G, j, q, hp⟩ : ∃ (G : Scheme.{0}) (j : G ⟶ X) (q : G ⟶ Sp K),
      IsPullback j q p (spMap (algebraMap k K)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, hcoh, -⟩ :=
    GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) h
  obtain ⟨s', hs', hsl, hsm, hslog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk M s hs hgen
  obtain ⟨t', ht', htl, htm, htlog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk N t ht hgen
  have hcod' : ∀ z : G, Order.coheight z = 1 → z ∈ nonzeroLocus s' ∨ z ∈ nonzeroLocus t' := by
    intro z hz
    rw [hsl, htl]
    exact hcod (j z) ((hcoh z).trans hz)
  have hrec := GlobalTheory.T.arithReciprocity_noCommonDivisor_projective hP K G q τ e hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ)
    (N.bc hp.w τ) s' hs' t' ht' hcod'
  have e1 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ hsm N L (M.logSec s) (N.logSec t)
  have e2 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ htm M L (N.logSec t) (M.logSec s)
  have hsf : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hslog
  have htf : (N.bc hp.w τ).logSec t' = fun y => N.logSec t (bcPt hp.w τ y) := funext htlog
  rw [hsf, htf] at hrec
  exact e1.symm.trans (hrec.trans e2)

end GlobalTheory.MixRec
