module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.BaseHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory.ColumnField

theorem conj_notMem_inertia (D : D7) (X : Fields) (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal := by
  intro hall
  let φ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE
  let P' : Ideal (𝓞 D.host.E) := P.asIdeal.comap (φ.symm : 𝓞 D.host.E →+* 𝓞 X.E)
  have hmax : P'.IsMaximal :=
    have := P.isMaximal
    Ideal.comap_isMaximal_of_surjective _ φ.symm.surjective
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host P' hmax
  have hcoe : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (φ y) = s.iE (algebraMap (𝓞 X.E) X.E y) := fun _ => rfl
  have e : φ.symm t = X.conjO (φ.symm θ) := by
    apply φ.injective
    apply RingOfIntegers.ext
    rw [RingEquiv.apply_symm_apply]
    change algebraMap (𝓞 D.host.E) D.host.E t = algebraMap (𝓞 D.host.E) D.host.E (φ (X.conjO (φ.symm θ)))
    rw [hcoe, h1]
    change _ = s.iE (star (algebraMap (𝓞 X.E) X.E (φ.symm θ)))
    rw [hs.2, ← hcoe, RingEquiv.apply_symm_apply]
  apply h2
  change φ.symm (θ - t) ∈ P.asIdeal
  rw [map_sub, e, ← neg_sub]
  exact P.asIdeal.neg_mem (hall _)

theorem ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok →
    ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  intro D X s hX hs v
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsGalois X.F X.E := inferInstance
  have := v.isMaximal
  obtain ⟨Q, hQ, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 X.E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 X.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hun := hX.unram_of_inertia (conj_notMem_inertia D X s hs) P
  have hcomap : Q.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) = v.asIdeal := (Ideal.over_def Q v.asIdeal).symm
  have hun' : ¬ v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 2 := by
    rw [← hcomap]
    exact hun
  have h1 : v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 1 := by
    rw [pow_one, Ideal.map_le_iff_le_comap, hcomap]
  have he : v.asIdeal.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec h1 hun'
  have := hQ.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (X.E ≃ₐ[X.F] X.E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
  exact he

end GlobalTheory.ColumnField
