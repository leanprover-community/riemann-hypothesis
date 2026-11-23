module

public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
public import Development.AutomorphicArithmetic.WeightCongruences.ExistsShiftWeightCongruenceLtTorsionOrder
public import Development.AutomorphicArithmetic.WeightCongruences.ProdCmTypeEqNormAndWeightCongruenceOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions

namespace UpperTheory.Mu

variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (eT : ι ≃ R.Psi)

theorem mu_one : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => 1) := (UpperTheory.prod_cmType_eq_norm_and_weightCongruence_one R H ι eT).2

theorem mu_const (c : ℤ) : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => c) := (mu_one H eT).const c

theorem prod_emb_zpow {z : H.E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) (c : ℤ) :
    ∏ τ, H.emb ((eT τ : R.Psi) : R.GG) z ^ c = 1 := mu_const H eT c z hz

theorem prod_emb {z : H.E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ∏ τ, H.emb ((eT τ : R.Psi) : R.GG) z = 1 := by
  simpa using prod_emb_zpow H eT hz 1

theorem muq_of_parallel {a : ι → ℤ} (ha : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) a) {e : ι → ℚ} (c : ℤ)
    (he : ∀ τ, e τ = a τ + c) : MUQ (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) e :=
  ⟨fun τ => a τ + c, fun τ => by rw [he]; push_cast; rfl, ha.add_const (mu_one H eT) c⟩

theorem exists_shift [DecidableEq ι] (a : ι → ℤ) (τ₀ : ι) : ∃ s : ℕ, s < Units.torsionOrder H.E ∧
    MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun τ => a τ + if τ = τ₀ then (s : ℤ) else 0) :=
  UpperTheory.exists_shift_weightCongruence_lt_torsionOrder H.E ℂ ι _ a τ₀

end UpperTheory.Mu
