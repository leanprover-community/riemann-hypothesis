module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.tCover :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → Smooth (eP B j) ∧ Surjective (eP B j) := by
  intro K _ W Z Y q i π D d B T j r hsq
  refine ⟨?_, ?_⟩
  · have hloc : IsZariskiLocalAtSource @Smooth.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
    unfold eP
    exact IsZariskiLocalAtSource.sigmaDesc fun p => inferInstance
  · refine ⟨fun x => ?_⟩
    have hx : r x ∈ i ⁻¹ᵁ (⨆ α, B.V α) := B.cover (Set.mem_univ (r x))
    have hx' : i (r x) ∈ (⨆ α, B.V α) := hx
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    have h3 : π (j x) = i (r x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq.w]
    have h4 : j x ∈ π ⁻¹ᵁ B.V α := by
      change π (j x) ∈ B.V α
      rw [h3]; exact hα
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp ((B.c α).C_cover h4)
    let p : B.ι × Fin d := (α, k)
    have hp : x ∈ oT B j p := hk
    let y : (oT B j p : Scheme.{0}) := ⟨x, hp⟩
    have hc : tI B j p ≫ eP B j = (oT B j p).ι := by
      unfold tI eP
      exact Sigma.ι_desc _ _
    refine ⟨tI B j p y, ?_⟩
    have hy : (tI B j p ≫ eP B j) y = x := by
      rw [hc]
      rfl
    rw [← Scheme.Hom.comp_apply]
    exact hy
