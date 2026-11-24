module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def IsUnimodularLC (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] : Prop :=
  IsTopologicalGroup G ∧ T2Space G ∧ LocallyCompactSpace G ∧ SecondCountableTopology G ∧
    BorelSpace G ∧ (∃ μ : Measure G, μ.IsHaarMeasure) ∧
    ∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant

def IsDiscreteWithDomains {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (Γ : Subgroup G) : Prop :=
  Countable Γ ∧ DiscreteTopology Γ ∧
    ∀ μ : Measure G, μ.IsHaarMeasure →
      ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ IsFundamentalDomain Γ 𝓕 μ

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratPts (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA R σ J) := HFinIn R σ J

def UnimodularOver (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  IsUnimodularLC (HA R σ J) ∧
    ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsUnimodularLC (Hstab R σ J x)

end Points

def AdelicUnitaryHaar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      UnimodularOver (AF F) σ J ∧ UnimodularOver (Ainf F) σ J ∧ UnimodularOver (Af F) σ J ∧
      (∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J) ∧
      IsDiscreteWithDomains (ratPts (AF F) σ J) ∧
      ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 →
        IsDiscreteWithDomains (HstabFin (AF F) σ J x)

theorem isUnimodularLC_of_commGroup (G : Type) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] : IsUnimodularLC G :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun _ _ => inferInstance⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
