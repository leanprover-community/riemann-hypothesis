module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAwayCpt

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlobalTheory.DenAway

theorem exists_nat_mul_integral_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)), IsCompact Q →
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ := by
  intro p _ Q hQ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun x hx v => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hxa' : (m a : AfP p) * x ∈ intAfP p := hxa
  have e : ((∏ a ∈ t, m a : ℕ) : AfP p) * x = (k : AfP p) * ((m a : AfP p) * x) := by
    rw [hk, Nat.cast_mul]; ring
  rw [e, eval_natCast_mul]
  exact mul_mem (natCast_mem v.1 k) (hxa' v)

end GlobalTheory.DenAwayCpt
