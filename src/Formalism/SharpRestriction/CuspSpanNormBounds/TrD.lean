module

public import Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousCjIT
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

@[expose] public section

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {k r : ℕ}

def trD (L : LocBessel k r) (κ τ : ℝ) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1) : LocBessel k r where
  ε := L.ε
  lam := L.lam
  hlam := L.hlam
  z := (τ : ℂ) • L.z
  z' := (τ : ℂ) • L.z'
  hz := hz
  hz' := hz'
  u := L.u
  u' := L.u'
  Hs := L.Hs
  σ := L.σ
  hσ := L.hσ
  Wp := L.Wp
  π := fun x => L.π (cjI k r κ τ x)
  hπ := hπ
  Wq := L.Wq
  π' := fun x => L.π' (cjI k r κ τ x)
  hπ' := hπ'
  c := (κ : ℂ) * L.c
  μW := L.μW.map (cjT k r κ τ)
  μW' := L.μW'.map (cjT k r κ τ)
  hμW := hμW
  hμW' := hμW'
  κN := κN₁

end Formalism.MainNotions.FrameBoundFromBesselTorus
