module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLimitPowersIntegralAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryGlueIdempotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentDivisibleCongruent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.MaxLevelLift

theorem exists_intG_cong : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (N : ℕ)
    (g : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det →
      ∃ k : GA D N, k ∈ intG D N ∧ ∀ i j : Fin N,
        ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D ((g i j : 𝓞 D.host.E) : D.host.E) ∈ hatId D 𝔪 := by
  intro D 𝔪 _ hcop N g hg
  have hcc : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z
  have e : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by rw [smul_smul, hcc, one_smul]
  have hdet : (g.map (Ideal.Quotient.mk 𝔪)).det = Ideal.Quotient.mk 𝔪 g.det :=
    ((Ideal.Quotient.mk 𝔪).map_det g).symm
  rw [hdet] at hg
  obtain ⟨v, hv⟩ := hg.exists_right_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq] at hv
  have key : inc D ((g.det * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • D.host.conj • 𝔪) := by
    rw [e]
    exact AddSubgroup.subset_closure ⟨g.det * u - 1, hv, 1, one_mem _, by simp⟩
  obtain ⟨f, hf, w, hw, hff, hfs, hfw, h1f⟩ :=
    GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit GlobalTheory.AlgIntIdem.idem D (D.host.conj • 𝔪)
      (by rw [e, sup_comm]; exact hcop) _ _ key
  rw [e] at h1f
  obtain ⟨k, hk, hkc⟩ := GlobalTheory.GlueUnitary.glue_unitary D 𝔪 N g f w hf hw hff hfs hfw h1f
  refine ⟨k⁻¹, inv_mem hk, fun i j => ?_⟩
  have := neg_mem (hkc i j)
  rwa [Matrix.sub_apply, neg_sub, Matrix.map_apply] at this

end GlobalTheory.MaxLevelLift
