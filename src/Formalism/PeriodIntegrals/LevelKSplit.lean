module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
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

namespace PI.LevelKSplit

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def IsProdNH {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] (K N H : Subgroup (HA R σ J))
    (μK : Measure K) (μN : Measure N) (μH : Measure H) : Prop :=
  ∀ f : HA R σ J → ENNReal, Measurable f →
    ∫⁻ k, f (k : HA R σ J) ∂μK = ∫⁻ m, ∫⁻ h, f ((m : HA R σ J) * (h : HA R σ J)) ∂μH ∂μN

def Adapted {r : ℕ} (P : Frame E M r) (ΛX ΛW ΛY : Set (Fin M → E)) : Prop :=
  (∀ x ∈ ΛX, x ∈ Submodule.span E (Set.range P.e)) ∧
  (∀ y ∈ ΛY, y ∈ Submodule.span E (Set.range P.f)) ∧
  (∀ w ∈ ΛW, ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0)

def LevelS : Prop :=
  IsHermND σ J → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ∀ ΛX ΛW ΛY : Set (Fin M → E), Adapted F E σ M J P ΛX ΛW ΛY →
    ∀ μN : Measure (Nsub (Af F) σ J P), μN.IsHaarMeasure →
    ∀ μH : Measure (Hsub (Af F) σ J P), μH.IsHaarMeasure →
    AllSome (fun μS : Measure (Ssub (Af F) σ J P) => μS.IsHaarMeasure ∧
      IsProdNH F E σ M J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) μS μN μH)
      fun μS =>
      μS {s | (s : HA (Af F) σ J) ∈ KS σ J P (ΛX ∪ ΛW ∪ ΛY)} =
        μN {m | (m : HA (Af F) σ J) ∈ NO σ J P (ΛX ∪ ΛW ∪ ΛY)} *
        μH {h | (h : HA (Af F) σ J) ∈ KH σ J P (ΛX ∪ ΛW ∪ ΛY)}

end Ext

def ForAllCM (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      P F E σ M J

def LevelSAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => LevelS F E σ M J

end PI.LevelKSplit
