module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def OverPF (p : ℕ) (v : HeightOneSpectrum (𝓞 H.F)) : Prop := ((p : ℕ) : 𝓞 H.F) ∈ v.asIdeal

def PvSet (𝔭 : HeightOneSpectrum (𝓞 H.K)) (v : HeightOneSpectrum (𝓞 H.F)) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {w | w ∈ aboveF (L := H.E) H.F v ∧ w.under (𝓞 H.K) = 𝔭}

structure PlacesOverCommonPrime where

  pK : HeightOneSpectrum (𝓞 H.K)

  pK' : HeightOneSpectrum (𝓞 H.K)
  pK_over : ((H.pde : ℕ) : 𝓞 H.K) ∈ pK.asIdeal
  pK'_over : ((H.pde' : ℕ) : 𝓞 H.K) ∈ pK'.asIdeal

  P : ∀ v : HeightOneSpectrum (𝓞 H.F), OverPF H H.pde v → HeightOneSpectrum (𝓞 H.E)

  P' : ∀ v : HeightOneSpectrum (𝓞 H.F), OverPF H H.pde' v → HeightOneSpectrum (𝓞 H.E)

  P_mem : ∀ v hv, P v hv ∈ PvSet H pK v
  P'_mem : ∀ v hv, P' v hv ∈ PvSet H pK' v

structure ClsRepK where
  rep : ClassGroup (𝓞 H.K) → (nonZeroDivisors (Ideal (𝓞 H.K)))
  rep_cls : ∀ c, ClassGroup.mk0 (rep c) = c

variable {H}

def idK (p : ℕ) : Ideal (𝓞 H.K) := Ideal.span {((p : ℕ) : 𝓞 H.K)}

def PrimeToPl (𝔞 : Ideal (𝓞 H.K)) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ¬ 𝔞 ≤ (v.under (𝓞 H.K)).asIdeal

end Formalism.L2.Host
