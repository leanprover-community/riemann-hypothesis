module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
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
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
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

@[expose] public section

namespace Bl.general_b_fact_third_variant

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] {Ψ : Finset.{0} (RingHom.{0, 0} E Complex)},
  (∀ (σ : RingHom.{0, 0} E Complex),
      Iff (Membership.mem.{0, 0} Ψ σ) (Not (Membership.mem.{0, 0} Ψ (NumberField.ComplexEmbedding.conjugate.{0} σ)))) →
    ∀ (x : Module.Free.ChooseBasisIndex.{0, 0} Int (NumberField.RingOfIntegers.{0} E) → Real),
      (∀ (τ : RingHom.{0, 0} E Complex),
          Membership.mem.{0, 0} Ψ τ →
            Eq.{1}
              (Finset.sum.{0, 0} Finset.univ.{0}
                fun (k : Module.Free.ChooseBasisIndex.{0, 0} Int (NumberField.RingOfIntegers.{0} E)) ↦
                HMul.hMul.{0, 0, 0} (Complex.ofReal (x k))
                  (DFunLike.coe.{1, 1, 1} τ
                    (NumberField.RingOfIntegers.val.{0}
                      (DFunLike.coe.{1, 1, 1} (NumberField.RingOfIntegers.basis.{0} E) k))))
              0) →
        Eq.{1} x 0 := by
  intro E _ _ Ψ hΨ x hx
  have hall : ∀ σ : RingHom E Complex, (Finset.univ.sum fun k =>
      (Complex.ofReal (x k)) * σ (NumberField.RingOfIntegers.val
        (NumberField.RingOfIntegers.basis E k))) = 0 := by
    intro σ
    by_cases hσ : σ ∈ Ψ
    · exact hx σ hσ
    · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ Ψ := by
        by_contra hc
        exact hσ ((hΨ σ).mpr hc)
      have h2 := congrArg (starRingEnd Complex) (hx _ hc)

      rw [map_sum, map_zero] at h2
      simpa only [map_mul, Complex.conj_ofReal, NumberField.ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_conj] using h2
  have hli := (NumberField.canonicalEmbedding.latticeBasis E).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  funext k
  have h3 := hli (fun k => Complex.ofReal (x k)) (by
    funext σ
    rw [Finset.sum_apply]
    simp only [NumberField.canonicalEmbedding.latticeBasis_apply, Pi.smul_apply,
      NumberField.canonicalEmbedding.apply_at, NumberField.integralBasis_apply, smul_eq_mul,
      Pi.zero_apply]
    exact hall σ) k
  exact_mod_cast h3

end Bl.general_b_fact_third_variant
