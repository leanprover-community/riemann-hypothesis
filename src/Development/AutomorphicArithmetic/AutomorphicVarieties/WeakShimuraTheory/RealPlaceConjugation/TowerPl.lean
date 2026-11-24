module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical Pointwise

theorem UpperTheory.V.Ws.exists_injective_places_above_l_of_tower :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), ∃ pl : T.ι → HeightOneSpectrum (𝓞 T.F), Function.Injective pl ∧ ∀ v, IsPlaceOver (T.pl v) (pl v) ∧ ((l : ℕ) : 𝓞 T.F) ∈ (pl v).asIdeal := by
  intro Ω _ _ _ l _ c D T
  haveI := T.nF
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨_, hex, hne, _⟩ := UpperTheory.V.Kum.placeDict T.F Ω
  have hpl : ∀ v, ∃ w : HeightOneSpectrum (𝓞 T.F), IsPlaceOver (T.pl v) w :=
    fun v => hex _ (hne _ l (Fact.out : l.Prime).ne_zero (T.ovl v))
  choose pl hpl using hpl
  refine ⟨pl, ?_, fun v => ⟨hpl v, ?_⟩⟩
  · intro v w hvw
    have h1 := hpl v
    have h2 := hpl w
    rw [hvw] at h1
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver h1 h2
    obtain ⟨u, _, huniq⟩ := T.cover (T.pl w) (T.ovl w)
    have hv : v = u := by
      apply huniq v
      refine ⟨σ, fun x => ?_⟩
      rw [← hσ]
      exact ValuationSubring.smul_mem_pointwise_smul_iff
    have hw : w = u := by
      apply huniq w
      exact ⟨1, fun x => Iff.rfl⟩
    rw [hv, hw]
  · apply (hpl v (l : 𝓞 T.F)).1
    simpa using T.ovl v
