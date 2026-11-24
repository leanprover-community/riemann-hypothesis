module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def extC (𝔭 : Ideal (MvPolynomial σ ℚ)) : Ideal (MvPolynomial σ ℂ) :=
  Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭

theorem comap_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  let _ : Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) := MvPolynomial.algebraMvPolynomial
  have hflat : Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
    BaseChangeC.flat_mvPolynomial_rat_complex
  have hQp : Q.IsPrime := hQ.1.1
  have hle : 𝔭 ≤ Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) := Ideal.map_le_iff_le_comap.mp hQ.1.2
  have hPp : (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have hlo : Q.LiesOver (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))) := ⟨rfl⟩
  obtain ⟨Q', hQ'le, hQ'p, hQ'lo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hle
  have hQ'over : Q'.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := hQ'lo.over.symm
  have hmapQ' : extC 𝔭 ≤ Q' := by
    unfold extC
    rw [Ideal.map_le_iff_le_comap, hQ'over]
  have hEq : Q = Q' := le_antisymm (hQ.2 ⟨hQ'p, hmapQ'⟩ hQ'le) hQ'le
  subst hEq
  exact hQ'over

theorem ringKrullDim_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have hQp : Q.IsPrime := hQ.1.1
  have hh := BaseChangeC.height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ
  have h1 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [hh] at h1
  exact BaseChangeC.withBot_enat_cancel h1 h2

end ReciprocityTheory.AnForm.R
