module

public import Mathlib.Algebra.MvPolynomial.Eval
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatB
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial IntegerToRational

variable {σ : Type} [Fintype σ]

noncomputable def extQ (P : Ideal (MvPolynomial σ ℤ)) : Ideal (MvPolynomial σ ℚ) :=
  Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P

theorem extQ_spec (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0) :
    (extQ P).IsPrime ∧ (extQ P).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P ∧
      ringKrullDim (MvPolynomial σ ℚ ⧸ extQ P) + 1 = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hP' : ChZero P := hP
  haveI hI : (extQ P).IsPrime := map_isPrime P hP'
  refine ⟨hI, comap_map_eq P hP', ?_⟩
  have h1 := coheight_eQ_add_one_le (⟨P, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ ℤ)) hP'
  have h2 : Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ ℤ)) ≤
      Order.coheight (eQ ⟨P, inferInstance⟩ hP') + 1 :=
    Order.coheight_le fun s hs => length_le_coheight_eQ s _ hs hP'
  have heq : Order.coheight (eQ ⟨P, inferInstance⟩ hP') + 1 =
      Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ ℤ)) :=
    le_antisymm h1 h2
  have hE : (⟨extQ P, hI⟩ : PrimeSpectrum (MvPolynomial σ ℚ)) = eQ ⟨P, inferInstance⟩ hP' := rfl
  rw [ringKrullDim_quotient_eq_coheight (extQ P), ringKrullDim_quotient_eq_coheight P, hE, ← heq]
  norm_cast

end ReciprocityTheory.AnForm.R
