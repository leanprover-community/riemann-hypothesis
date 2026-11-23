module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormDvd.proof (h₁ : NormFormEmbeddings.Statement) (h₂ : LinearFormPrime.Statement)
    (h₃ : MapDvdDescent.Statement) : NormFormDvd.Statement := by
  intro K L _ _ _ _ _ _ n η t P hgen ht hdvd
  classical
  apply h₃ K (AlgebraicClosure K) (Fin n)
  rw [h₁ K L (AlgebraicClosure K) n η]
  set θ : (L →ₐ[K] AlgebraicClosure K) → MvPolynomial (Fin n) (AlgebraicClosure K) :=
    fun σ => ∑ m, X m * C (σ (η m)) with hθ

  have hev : ∀ σ, eval (fun m => algebraMap K (AlgebraicClosure K) (t m)) (θ σ) = 1 := by
    intro σ
    have h := congrArg σ ht

    simp only [map_sum, map_one, Algebra.smul_def, map_mul, AlgHom.commutes] at h

    simpa [hθ, map_sum, mul_comm] using h

  have hcoord : ∀ σ m, eval (Pi.single m 1) (θ σ) = σ (η m) := by
    intro σ m
    simp [hθ, Pi.single_apply]
  have hprime : ∀ σ, Prime (θ σ) := by
    intro σ
    refine h₂ (AlgebraicClosure K) n (fun m => σ (η m)) ?_
    intro h0
    have h := hev σ
    have hz : θ σ = 0 := by simp only [hθ]; simp [funext_iff] at h0; simp [h0]
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hdiv : ∀ σ, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro σ
    obtain ⟨Q, hQ⟩ := hdvd
    refine ⟨map (σ : L →+* AlgebraicClosure K) Q, ?_⟩
    have h := congrArg (map (σ : L →+* AlgebraicClosure K)) hQ
    rw [map_map, AlgHom.comp_algebraMap, map_mul] at h
    rw [h]
    congr 1

    simp [hθ, map_sum]
  have hinj : ∀ a b, θ a ∣ θ b → a = b := by
    intro a b hab
    obtain ⟨u, hu⟩ := (hprime a).associated_of_dvd (hprime b) hab
    obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
    rw [hc] at hu
    have h1 := congrArg (eval (fun m => algebraMap K (AlgebraicClosure K) (t m))) hu
    rw [eval_mul, hev, hev, eval_C, one_mul] at h1
    rw [h1, C_1, mul_one] at hu
    refine AlgHom.ext_of_adjoin_eq_top hgen ?_
    rintro _ ⟨m, rfl⟩
    rw [← hcoord a m, ← hcoord b m, hu]
  have key : ∀ s : Finset (L →ₐ[K] AlgebraicClosure K),
      ∏ σ ∈ s, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      obtain ⟨R, hR⟩ := ih
      have h := hdiv a
      rw [hR] at h
      rcases (hprime a).dvd_or_dvd h with h' | h'
      · exfalso
        obtain ⟨b, hb, hab⟩ := ((hprime a).dvd_finsetProd_iff _).1 h'
        exact ha (by rw [hinj a b hab]; exact hb)
      · obtain ⟨S, hS⟩ := h'
        exact ⟨S, by rw [hR, hS]; ring⟩
  exact key Finset.univ

end GroundTheory.Heights₂.Heights
