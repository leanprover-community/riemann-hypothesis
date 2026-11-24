module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

def CycC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n →
      (∀ sat inf, IsCusp (F := K) n sat inf → RegInf n inf → (∃ η : HChar K, IsNormChar M η ∧ SelfTw sat η) ∨
        ∃ sat' inf', IsCusp (F := M) n sat' inf' ∧ WeakBC sat sat' ∧ ∀ τ m, inf (τ.comp (algebraMap K M)) m → inf' τ m) ∧
      (∀ sat' inf', IsCusp (F := M) n sat' inf' → RegInf n inf' →
        (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) →
          ∃ B, sat' w B ∧ sat' w' B) →
        ∃ sat inf, IsCusp (F := K) n sat inf ∧ WeakBC sat sat' ∧ ∀ τ m, inf' τ m → inf (τ.comp (algebraMap K M)) m) ∧
      ∀ sat inf sat' inf', IsCusp (F := K) n sat inf → IsCusp (F := M) n sat' inf' → WeakBC sat sat' →
        ∀ sat₁ inf₁, IsCusp (F := K) n sat₁ inf₁ → WeakBC sat₁ sat' → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧
          ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, η.UnrAt v ∧ ∃ B, sat v B ∧ sat₁ v (B.map (· * η.val v))

end UpperTheory.V.Z.Bc
