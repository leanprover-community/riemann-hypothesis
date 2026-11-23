module

public import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
public import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PairEvaluation
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc

private theorem coeff_mul_eq_zero_of_order_two_of_degree_le_two {σ k : Type} [CommRing k] (j : ℕ) (q a : MvPolynomial σ k)
    (ha : ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff a e = 0) :
    ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff (q * a) e = 0 := by
  classical
  intro e he
  rw [MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h2 : x.2.degree ≤ e.degree := by
    rw [← hx, map_add (f := _)]; exact Nat.le_add_left _ _
  rw [ha x.2 (lt_of_le_of_lt h2 he), mul_zero]

private theorem coeff_eq_zero_of_mem_span_X_pow_of_degree_lt {σ k : Type} [CommRing k] :
    ∀ (j : ℕ) (P : MvPolynomial σ k), P ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ j →
      ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff P e = 0 := by
  classical
  intro j
  induction j with
  | zero => intro P _ e he; exact absurd he (Nat.not_lt_zero _)
  | succ j ih =>
    let K : Ideal (MvPolynomial σ k) :=
      { carrier := {P | ∀ e : σ →₀ ℕ, e.degree < j + 1 → AddMonoidAlgebra.coeff P e = 0}
        add_mem' := fun {a b} ha hb e he => by rw [MvPolynomial.coeff_add, ha e he, hb e he, add_zero]
        zero_mem' := fun e _ => by simp
        smul_mem' := fun c a ha => coeff_mul_eq_zero_of_order_two_of_degree_le_two (j + 1) c a ha }
    have hle : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ (j + 1) ≤ K := by
      rw [pow_succ, Ideal.mul_le]
      intro r hr s hs
      refine Submodule.span_induction (p := fun s _ => r * s ∈ K) ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨i, rfl⟩
        show ∀ e : σ →₀ ℕ, e.degree < j + 1 → AddMonoidAlgebra.coeff (r * MvPolynomial.X i) e = 0
        intro e he
        rw [MvPolynomial.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [MvPolynomial.coeff_X']
        split_ifs with hxi
        · have hx1 : x.1.degree + 1 = e.degree := by
            rw [← hx, map_add (f := _), ← hxi, Finsupp.degree_single]
          rw [ih r hr x.1 (by omega), zero_mul]
        · rw [mul_zero]
      · rw [mul_zero]; exact K.zero_mem
      · intro a b _ _ ha hb; rw [mul_add]; exact K.add_mem ha hb
      · intro c a _ ha; rw [smul_eq_mul, mul_left_comm]; exact K.mul_mem_left c ha
    exact fun P hP => hle hP

theorem pderiv_eq_zero_of_jet_pow_sub : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d : ℕ) (F f : MvPowerSeries (Fin 1 × Fin d) k), (∀ q, MvPowerSeries.pderiv (R := k) q f = 0) → (∀ m, ∃ v : Jet k (Fin 1 × Fin d) m, psJet m F = v ^ p - psJet m f) → ∀ q, MvPowerSeries.pderiv (R := k) q F = 0 := by
  intro k _ p _ _ d F f hf hF q
  classical
  ext e
  obtain ⟨v, hv⟩ := hF (e.degree + 1)
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hmem : psTrunc (e.degree + 1) F + psTrunc (e.degree + 1) f - P ^ p ∈
      orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), map_pow]
    have h1 : psJet (e.degree + 1) F =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) F) := rfl
    have h2 : psJet (e.degree + 1) f =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) f) := rfl
    rw [← h1, ← h2, hv]; ring
  have hdeg : (e + Finsupp.single q 1).degree < e.degree + 1 + 1 := by
    rw [map_add (f := _), Finsupp.degree_single]; omega
  have hz := coeff_eq_zero_of_mem_span_X_pow_of_degree_lt (e.degree + 1 + 1) _ hmem (e + Finsupp.single q 1) hdeg
  have hbd : ∀ i, (e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i ≤ (e + Finsupp.single q 1).degree := by
    intro i
    exact Finsupp.le_degree i _
  have hin : e + Finsupp.single q 1 ∈ degLE (e.degree + 1) := by
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · refine ⟨fun i => ⟨(e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i, ?_⟩, ?_⟩
      · have := hbd i
        rw [map_add (f := _), Finsupp.degree_single] at this
        omega
      · ext i; simp
    · show (e + Finsupp.single q 1).degree ≤ e.degree + 1
      rw [map_add (f := _), Finsupp.degree_single]
  have htr : ∀ g : MvPowerSeries (Fin 1 × Fin d) k,
      AddMonoidAlgebra.coeff (psTrunc (e.degree + 1) g) (e + Finsupp.single q 1) =
        MvPowerSeries.coeff (e + Finsupp.single q 1) g := by
    intro g
    simp [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hin]
  have hpow : MvPowerSeries.pderiv (R := k) q ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k) = 0 := by
    rw [MvPolynomial.coe_pow, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have hG : MvPowerSeries.pderiv (R := k) q F = MvPowerSeries.pderiv (R := k) q
      (F + f - ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k)) := by
    rw [map_sub, map_add (f := _), hf q, hpow, add_zero, sub_zero]
  rw [hG, MvPowerSeries.coeff_pderiv, map_zero, map_sub, map_add (f := _), MvPolynomial.coeff_coe, ← htr F, ← htr f,
    ← MvPolynomial.coeff_add, ← MvPolynomial.coeff_sub, hz, zero_mul]

end GlobalTheory.CompanionTheory.Ar.Coc
