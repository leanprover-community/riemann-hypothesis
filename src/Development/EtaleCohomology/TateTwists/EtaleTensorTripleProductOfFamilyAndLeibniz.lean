module

public import Development.EtaleCohomology.TateTwists.EtaleTensorPairProductAssociative
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L),
    ∃ m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U,
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) ∧
      ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U),
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) →
      (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
      ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.map (L.d w (w + 1)) (m U s t w h a b) = m U (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) a) b +
          s.negOnePow • m U s (t + 1) (w + 1) (by omega) a (Sec.map (K.d t (t + 1)) b)

theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_of_family_and_leibniz (hfam : LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists)
    (hleib : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz) : LateralTheory.EtaleFoundations.EtaleTensorPairProductAssociative := by
  intro R _ I J K T T3 τ τ' hτ _ M L μ' ν'
  obtain ⟨m, hnat, heq⟩ := hfam R τ hτ μ' ν'
  refine ⟨⟨m, hnat, hleib R τ hτ μ' ν' m hnat heq⟩, ?_⟩
  intro U s t u st tu w h1 h2 h3 h4 a b c
  exact heq U s t u st tu w h1 h2 h3 h4 a b c
