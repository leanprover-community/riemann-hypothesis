module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexMinimalPrimesContract
public import Mathlib.RingTheory.Flat.Basic
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
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Stability

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem mvPolynomial_int_complex_flat (σ : Type) :
    Module.Flat (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℤ (MvPolynomial σ ℤ) ℂ (MvPolynomial σ ℂ)
    (Algebra.IsPushout.out (R := ℤ) (S := MvPolynomial σ ℤ) (R' := ℂ) (S' := MvPolynomial σ ℂ))

theorem algebraMap_mvPolynomial_int_complex (σ : Type) :
    algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) = MvPolynomial.map (Int.castRingHom ℂ) := by
  rw [MvPolynomial.algebraMap_def]
  congr 1

theorem ComplexMinimalPrimesContract.proof : ComplexMinimalPrimesContract.Statement := by
  intro σ _ P hP Q hQ
  have := hP
  have hflat := mvPolynomial_int_complex_flat σ
  have hAlg := algebraMap_mvPolynomial_int_complex σ
  have : Q.IsPrime := hQ.1.1
  have hPQ : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q := hQ.1.2
  have hle : P ≤ Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
    Ideal.map_le_iff_le_comap.mp hPQ
  have : (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have : Q.LiesOver (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) :=
    ⟨by rw [Ideal.under, Ideal.comap, hAlg]; rfl⟩
  obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (R := MvPolynomial σ ℤ) (p := P)
      (q := Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) Q hle
  have hQ'P : Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
    have := hQ'over.over
    rw [Ideal.under, hAlg] at this
    exact this.symm
  have hmapQ' : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q' :=
    Ideal.map_le_iff_le_comap.mpr hQ'P.ge
  have hQQ' : Q ≤ Q' := hQ.2 ⟨hQ'prime, hmapQ'⟩ hQ'Q
  rw [← le_antisymm hQ'Q hQQ']
  exact hQ'P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
