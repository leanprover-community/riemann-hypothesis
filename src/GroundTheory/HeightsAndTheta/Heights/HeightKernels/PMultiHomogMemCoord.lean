module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace MultiHomogMemCoordinate

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mapDomain_fst_eq (m : (Σ k, ι k) →₀ ℕ) (a : K → ℕ) (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    Finsupp.mapDomain Sigma.fst m = Finsupp.equivFunOnFinite.symm a := by
  ext k
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [hm]
  · intro b _ hb
    simp [hb]
  · simp

theorem cone_monomial (y : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (a : K → ℕ)
    (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    mConeMap y (monomial m c) =
      C (aeval y (monomial m c)) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  have hX : (monomial (Finsupp.mapDomain Sigma.fst m) (1 : Ω) : MvPolynomial K Ω) =
      m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e := by
    rw [← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]
    simp only [map_pow, rename_X]
  rw [← mapDomain_fst_eq m a hm, hX]
  simp only [mConeMap, aeval_monomial, mul_pow, Finsupp.prod_mul, MvPolynomial.algebraMap_apply, map_finsuppProd,
    map_pow, map_mul]
  ring

theorem cone_eq (y : (Σ k, ι k) → Ω) (g : MRing ι) (a : K → ℕ) (hg : IsMultiHomog g a) :
    mConeMap y g = C (aeval y g) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]

  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m hm => cone_monomial y m _ a (hg m hm)

end MultiHomogMemCoordinate


open MultiHomogMemCoordinate in
theorem MultiHomogMemCoord.proof : MultiHomogMemCoord.Statement := by
  intro K _ ι _ Ω _ y g a hg
  rw [mCoordIdeal, RingHom.mem_ker, cone_eq y g a hg, C_mul_monomial, mul_one,
    monomial_eq_zero]

end GroundTheory.Heights₂.Heights
