module

public import Development.EtaleCohomology.TateTwists.EtaleTensorAcyclicOfFlatBounded
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

namespace LateralTheory.EtaleFoundations

def EtaleShortComplexExactIffLocallySurjectiveOnKernel : Prop :=
  ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔
    ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b

def EtaleTensorComplexLocallyExactOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (T.sc w).X₂ U), Sec.map (T.sc w).g y = 0 →
      Loc U fun V g => ∃ x : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f x = Sec.res g y

theorem etale_tensor_complex_acyclic_of_locally_exact_flat (hE : EtaleShortComplexExactIffLocallySurjectiveOnKernel) (hS : EtaleTensorComplexLocallyExactOfFlatBounded) :
    EtaleTensorAcyclicOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC w
  have hCl := fun s => (hE R (C.sc s)).1 (hC s)
  exact (hE R (T.sc w)).2 (hS R a b τ hτ hJ hCl w)

end LateralTheory.EtaleFoundations
