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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KinfFin

theorem seq_add_pow {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) (m k : ℕ) :
    ϖ.seq (m + k) ^ l ^ k = ϖ.seq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, ϖ.seq_succ, ih]

theorem adjoin_mono {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) :
    Monotone fun n => IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine IntermediateField.adjoin_simple_le_iff.2 ?_
  have : ϖ.seq m ^ e = (ϖ.seq (m + k) ^ e) ^ l ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, seq_add_pow]
  rw [this]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _

theorem Kinf_eq_iSup {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) :
    ϖ.Kinf = ⨆ n, IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  rw [PiSys.Kinf, ← IntermediateField.biSup_adjoin_simple, iSup_range]

theorem exists_mem_of_mem_Kinf {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) {x : Om l}
    (hx : x ∈ ϖ.Kinf) : ∃ n, x ∈ IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  rw [Kinf_eq_iSup, ← SetLike.mem_coe,
    IntermediateField.coe_iSup_of_directed (adjoin_mono ϖ).directed_le, Set.mem_iUnion] at hx
  exact hx

theorem main : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (ϖ : PiSys l e) (F : IntermediateField ℚ_[l] (Om l)),
    FiniteDimensional ℚ_[l] F → F ≤ ϖ.Kinf → ∃ n : ℕ, F ≤ IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  intro l _ e ϖ F hF hle
  classical
  let b := Module.finBasis ℚ_[l] F
  choose N hN using fun i => exists_mem_of_mem_Kinf ϖ (hle (b i).2)
  refine ⟨Finset.univ.sup N, fun x hx => ?_⟩
  change ((⟨x, hx⟩ : F) : Om l) ∈ _
  rw [← b.sum_repr ⟨x, hx⟩, IntermediateField.coe_sum]
  refine sum_mem fun i _ => ?_
  rw [IntermediateField.coe_smul]
  refine IntermediateField.smul_mem _ ?_
  exact adjoin_mono ϖ (Finset.le_sup (f := N) (Finset.mem_univ i)) (hN i)

end GlobalTheory.KinfFin
