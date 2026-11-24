module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial NumberField
open scoped Classical

namespace GlobalTheory.FixedPlaceSplit

theorem host_conj_conj (D : Formalism.BasicNotions.D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem isSplitPl_of_not_isConjPl (D : Formalism.BasicNotions.D7) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (h : ¬ Formalism.BasicNotions.IsConjPl D.host w w) : Formalism.BasicNotions.IsSplitPl D.host w := by
  by_contra hs
  apply h
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    by_contra hy
    apply hs
    refine ⟨x, hx, fun y' hy' => ?_⟩
    have : y' = y := by
      apply RingOfIntegers.ext
      exact hy'.trans hxy.symm
    rwa [this]
  intro x y hxy
  refine ⟨key x y hxy, key y x ?_⟩
  rw [hxy, host_conj_conj]

theorem isSplitPl_plGw : ∀ (D : Formalism.BasicNotions.D7) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.BasicNotions.IsSplitPl D.host (D.naut.plGw k v) :=
  fun D k v => isSplitPl_of_not_isConjPl D _ (D.naut.plGw_nconj k v v)

end GlobalTheory.FixedPlaceSplit
