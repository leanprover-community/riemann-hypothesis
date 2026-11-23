module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.SSDirect
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.M.SSD

section LI

variable {σ τ K : Type} [Field K] [DecidableEq σ] (e : τ → σ) (he : Function.Injective e)

def decode (M : Finset (σ →₀ ℕ)) : MvPolynomial σ K →ₗ[K] (M → MvPolynomial τ K) where
  toFun Q := fun β => kap _ (F_inj e he 0 (β : σ →₀ ℕ)) Q
  map_add' Q Q' := by funext β; exact kap_add _ _ Q Q'
  map_smul' c Q := by funext β; exact kap_smul _ _ c Q

theorem decode_gen (M : Finset (σ →₀ ℕ)) (hM : ∀ β ∈ M, ∀ x, β (e x) = 0) (y : MvPolynomial τ K) (β : M) :
    decode e he M (rename e y * monomial (β : σ →₀ ℕ) 1) = Pi.single β y := by
  funext γ
  have h1 : rename e y * monomial (β : σ →₀ ℕ) (1 : K) = monomial 0 1 * rename e y * monomial (β : σ →₀ ℕ) 1 := by
    rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_mul]
  have hg : ∀ w ∈ (monomial (β : σ →₀ ℕ) (1 : K)).support, ∀ x, w (e x) = 0 := by
    intro w hw x
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial] at hw
    split_ifs at hw with h
    · rw [← h]
      exact hM _ β.2 x
    · exact absurd rfl hw
  show kap _ (F_inj e he 0 (γ : σ →₀ ℕ)) (rename e y * monomial (β : σ →₀ ℕ) 1) = (Pi.single β y : M → MvPolynomial τ K) γ
  rw [h1, kap_gen e he 0 (γ : σ →₀ ℕ) (hM _ γ.2) y _ hg, MvPolynomial.coeff_monomial, Pi.single_apply]
  by_cases h : γ = β
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'.symm))]
    exact zero_smul K y

include he in
theorem li_rename_mon (M : Finset (σ →₀ ℕ)) (hM : ∀ β ∈ M, ∀ x, β (e x) = 0) {ι : Type} (b : ι → MvPolynomial τ K)
    (hb : LinearIndependent K b) :
    LinearIndependent K (fun q : (Σ _ : M, ι) => rename e (b q.2) * monomial ((q.1 : σ →₀ ℕ)) 1) := by
  apply LinearIndependent.of_comp (decode e he M)
  have h1 : (decode e he M) ∘ (fun q : (Σ _ : M, ι) => rename e (b q.2) * monomial ((q.1 : σ →₀ ℕ)) 1) =
      (Finsupp.linearEquivFunOnFinite K (MvPolynomial τ K) M) ∘
        (fun q : (Σ _ : M, ι) => Finsupp.single q.1 (b q.2)) := by
    funext q
    simp only [Function.comp_apply, Finsupp.linearEquivFunOnFinite_single]
    exact decode_gen e he M hM (b q.2) q.1
  rw [h1]
  first
  | exact (Finsupp.linearIndependent_single (fun _ : M => b) (fun _ => hb)).map' _ (LinearEquiv.ker _)
  | exact (Finsupp.linearIndependent_single (f := fun _ : M => b) (fun _ => hb)).map' _ (LinearEquiv.ker _)
  | exact (Finsupp.linearIndependent_single (v := fun _ : M => b) (fun _ => hb)).map' _ (LinearEquiv.ker _)



theorem li_mul_left {ι : Type} (F : MvPolynomial σ K) (hF : F ≠ 0) (v : ι → MvPolynomial σ K) (hv : LinearIndependent K v) :
    LinearIndependent K (fun i => F * v i) := by
  have hinj : Function.Injective (LinearMap.mulLeft K F) := by
    intro a c h
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at h
    exact mul_left_cancel₀ hF h
  have hfun : (fun i => F * v i) = (LinearMap.mulLeft K F) ∘ v := by
    funext i
    rw [Function.comp_apply, LinearMap.mulLeft_apply]
  rw [hfun]
  exact hv.map' _ (LinearMap.ker_eq_bot.mpr hinj)

end LI

end Formalism.MainNotions.G.SymmetricFormBlocks

end
