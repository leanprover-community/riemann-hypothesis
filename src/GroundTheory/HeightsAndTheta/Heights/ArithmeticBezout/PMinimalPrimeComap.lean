module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMinimalPrimeComap
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem MinimalPrimeComap.flat (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) :
    letI := σ.toAlgebra
    letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
    Module.Flat (MvPolynomial ι K) (MvPolynomial ι L) := by
  letI := σ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have h : Algebra.IsPushout K (MvPolynomial ι K) L (MvPolynomial ι L) := inferInstance
  exact Module.Flat.isBaseChange K (MvPolynomial ι K) L (MvPolynomial ι L) h.out

theorem MinimalPrimeComap.proof : MinimalPrimeComap.Statement := by
  intro K L _ _ σ ι I hI P hP
  letI := σ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have := MinimalPrimeComap.flat K L σ ι
  have halg : algebraMap (MvPolynomial ι K) (MvPolynomial ι L) = MvPolynomial.map σ := rfl
  have : P.IsPrime := hP.1.1
  have hle : I ≤ P.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hP.1.2
  by_contra hne
  have hlt : I < P.under (MvPolynomial ι K) := lt_of_le_of_ne hle (fun h => hne h.symm)
  have : (P.under (MvPolynomial ι K)).IsPrime := Ideal.IsPrime.under _ _
  have : P.LiesOver (P.under (MvPolynomial ι K)) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQI⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := I) P hlt
  have hIQ : I.map (MvPolynomial.map σ) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, ← halg, ← Ideal.under_def, ← hQI.over]
  exact (not_le_of_gt hQP) (hP.2 ⟨hQ, hIQ⟩ hQP.le)

end GroundTheory.Heights₂.Heights
