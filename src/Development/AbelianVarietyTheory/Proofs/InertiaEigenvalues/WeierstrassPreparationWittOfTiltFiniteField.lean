module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem weierstrass_prep_not_dvd_l : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : (Wq l a)⟦X⟧), ¬ (l : (Wq l a)⟦X⟧) ∣ g →
    ∃ (P : Polynomial (Wq l a)) (U : (Wq l a)⟦X⟧), IsUnit U ∧ P.Monic ∧
      (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) ∧ g = U * (P : (Wq l a)⟦X⟧) := by
  intro l _ a _ g hg
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have hsurj : Function.Surjective (WittVector.constantCoeff (p := l) (R := Fq l a)) :=
    fun x => ⟨WittVector.teichmuller l x, by simp⟩
  have hm : IsLocalRing.maximalIdeal (Wq l a) = Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff]
    haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact (IsLocalRing.eq_maximalIdeal this).symm
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (Wq l a)) (Wq l a) := hm ▸ inferInstance
  have hg' : g.map (IsLocalRing.residue (Wq l a)) ≠ 0 := by
    intro h0
    apply hg
    apply dvd_of_map_eq_zero l a g
    ext n
    have h1 : IsLocalRing.residue (Wq l a) (coeff n g) = 0 := by
      simpa using congrArg (coeff n) h0
    rw [IsLocalRing.residue_eq_zero_iff, hm, ← WittVector.ker_constantCoeff, RingHom.mem_ker] at h1
    simpa using h1
  obtain ⟨f, h, H⟩ := g.exists_isWeierstrassFactorization hg'
  refine ⟨f, h, H.isUnit, H.isDistinguishedAt.monic, fun i hi => ?_, ?_⟩
  · have := H.isDistinguishedAt.mem hi
    rw [hm] at this
    exact Ideal.mem_span_singleton.1 this
  · rw [H.eq_mul, mul_comm]

end GlobalTheory
