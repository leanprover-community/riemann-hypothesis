module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain

theorem UpperTheory.V.Af.Tw.unrAE :
    UpperTheory.V.Af.Tw.UnrAE := by
  unfold UpperTheory.V.Af.Tw.UnrAE
  intro F L _ _ _ _ _
  letI := FractionRing.liftAlgebra (𝓞 F) (FractionRing (𝓞 L))
  haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) := inferInstance
  have hD0 : differentIdeal (𝓞 F) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 L)
  have hfin := Ideal.finite_factors (R := 𝓞 L) (I := differentIdeal (𝓞 F) (𝓞 L)) hD0
  rw [Filter.eventually_cofinite]
  refine (hfin.image (HeightOneSpectrum.under (𝓞 F))).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  unfold UpperTheory.V.Af.Tw.Unr at hv
  push_neg at hv
  obtain ⟨w, rfl, he⟩ := hv
  refine ⟨w, ?_, rfl⟩
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤
      w.asIdeal := Ideal.map_comap_le
  have h2 : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤
      w.asIdeal ^ 2 := by
    by_contra h
    exact he (Ideal.ramificationIdx'_spec (by rwa [pow_one]) h)
  haveI := (HeightOneSpectrum.under (𝓞 F) w).isMaximal
  have hdvd := pow_sub_one_dvd_differentIdeal (A := 𝓞 F) (P := w.asIdeal) (e := 2)
    (hp := (HeightOneSpectrum.under (𝓞 F) w).ne_bot) (hP := Ideal.dvd_iff_le.mpr h2)
  simpa using hdvd
