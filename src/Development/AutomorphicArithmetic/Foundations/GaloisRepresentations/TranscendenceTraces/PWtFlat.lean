module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtFlat_of :
    WtClopen → MultSum → MultBC → MultOpen → WtFlat := by
  intro hC hS hB hO Z S p _ _ _
  refine hC p (mult p) fun A W hW => ?_
  have : IsFinite A.r := A.finite
  have : Flat A.r := MorphismProperty.of_isPullback A.pb ‹_›
  have : LocallyOfFinitePresentation A.r := MorphismProperty.of_isPullback A.pb ‹_›
  let O : A.V.Opens := ⟨W, hW.isOpen⟩
  have : IsClosedImmersion O.ι :=
    IsClosedImmersion.of_isPreimmersion O.ι (by rw [O.range_ι]; exact hW.isClosed)
  have hm : mult (O.ι ≫ A.r) = (mult A.r).comap O.ι := hO O.ι A.r
  have hm' : mult A.r = (mult p).comap A.v := hB A.v A.r p A.u A.pb
  refine ⟨fun u => (((O.ι ≫ A.r).finrank u : ℕ) : ℤ), ?_, ?_⟩
  · exact (Scheme.Hom.isLocallyConstant_finrank (O.ι ≫ A.r)).comp _
  · intro Ω _ _ x
    have h1 := hS (O.ι ≫ A.r) Ω x
    refine h1.symm.trans ?_
    change ∑ᶠ z ∈ fib (O.ι ≫ A.r) x, mult (O.ι ≫ A.r) Ω z = _
    refine finsum_mem_eq_of_bijOn (fun z => z ≫ O.ι) ⟨?_, ?_, ?_⟩ ?_
    · intro z hz
      refine ⟨?_, ?_⟩
      · change (z ≫ O.ι) ≫ A.r = x
        rw [Category.assoc]; exact hz
      · change pt (z ≫ O.ι) ∈ W
        rw [pt_comp]; exact (pt z).2
    · intro z _ z' _ e
      exact (cancel_mono O.ι).1 e
    · rintro z ⟨hz, hzW⟩
      have hr : Set.range z ⊆ Set.range O.ι := by
        rw [O.range_ι]
        rintro _ ⟨t, rfl⟩
        rw [pt_eq]; exact hzW
      refine ⟨IsOpenImmersion.lift O.ι z hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩
      change _ ≫ O.ι ≫ A.r = x
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact hz
    · intro z _
      rw [hm, hm']
      simp [Wt.comap]
