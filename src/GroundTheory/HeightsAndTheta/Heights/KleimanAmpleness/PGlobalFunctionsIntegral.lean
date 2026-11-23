module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GlobalFunctionsIntegralSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

theorem GlobalFunctionsIntegral.proof : GlobalFunctionsIntegral.Statement := by
  intro k _ K _ _ N y a hy ha
  classical

  have key : ∀ i : Fin (N + 1), ∃ (e : ℕ) (f : MvPolynomial (Fin (N + 1)) k),
      f.IsHomogeneous e ∧ a * y i ^ e = aeval y f := by
    intro i
    by_cases hi : y i = 0
    · exact ⟨1, 0, isHomogeneous_zero _ _ _, by simp [hi]⟩
    · obtain ⟨f, s, e, hs, hf, hse, hrep⟩ := ha i hi
      obtain ⟨n, rfl⟩ := exists_eq_X_pow_of_mem_monos_single hs
      have hne : (X i ^ n : MvPolynomial (Fin (N + 1)) k) ≠ 0 := pow_ne_zero _ (X_ne_zero i)
      have hn : n = e := (isHomogeneous_X_pow i n).inj_right hse hne
      subst hn
      refine ⟨n, f, hf, ?_⟩
      have hyn : y i ^ n ≠ 0 := pow_ne_zero _ hi
      rw [hrep, map_pow, aeval_X, div_mul_cancel₀ _ hyn]
  choose e f hf hrel using key
  set E := ∑ i, e i with hE
  let M : Submodule k K :=
    (homogeneousSubmodule (Fin (N + 1)) k E).map (aeval y : MvPolynomial (Fin (N + 1)) k →ₐ[k] K).toLinearMap
  refine isIntegral_of_smul_mem_submodule M ?_ ((homogeneousSubmodule_fg (Fin (N + 1)) k E).map _) a ?_
  ·
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine (Submodule.ne_bot_iff M).mpr ⟨y i ^ E, ⟨X i ^ E, ?_, by simp⟩, pow_ne_zero _ hi⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X_pow i E)
  ·
    rintro _ ⟨g, hg, rfl⟩
    have hgE : g.IsHomogeneous E := (mem_homogeneousSubmodule _ _).mp hg

    rw [smul_eq_mul, AlgHom.toLinearMap_apply, g.as_sum, map_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hmE : m.degree = E := by
      by_contra h
      exact mem_support_iff.mp hm (hgE.coeff_eq_zero h)
    have hsum : ∑ i, e i ≤ ∑ i, m i := by
      rw [← hE, ← hmE, Finsupp.degree_eq_sum]
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    set m' := m - Finsupp.single i (e i) with hm'
    have hsplit : m' + Finsupp.single i (e i) = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
    have hdeg : m'.degree + e i = E := by
      rw [← hmE, ← hsplit, map_add (f := _), Finsupp.degree_single]
    refine ⟨monomial m' (AddMonoidAlgebra.coeff g m) * f i, ?_, ?_⟩
    · refine (mem_homogeneousSubmodule _ _).mpr ?_
      rw [← hdeg]
      exact (isHomogeneous_monomial _ rfl).mul (hf i)
    · have hmono : (monomial m (AddMonoidAlgebra.coeff g m) : MvPolynomial (Fin (N + 1)) k) =
          monomial m' (AddMonoidAlgebra.coeff g m) * X i ^ e i := by
        rw [X_pow_eq_monomial, monomial_mul, mul_one, hsplit]
      rw [AlgHom.toLinearMap_apply, map_mul, ← hrel i, hmono, map_mul, map_pow, aeval_X]
      ring

end

end GroundTheory.Heights₂.Heights.Kleiman
