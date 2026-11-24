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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem MapDvdDescent.proof : MapDvdDescent.Statement := by
  classical
  intro K Ω _ _ _ σ f g ⟨G, hG⟩
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.mpr (algebraMap K Ω).injective)
  have hπa : ∀ a : K, π (algebraMap K Ω a) = a := fun a => by
    simpa using LinearMap.congr_fun hπ a
  have hπm : ∀ (a : K) (y : Ω), π (algebraMap K Ω a * y) = a * π y := fun a y => by
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

  let Φ : MvPolynomial σ K := ∑ s ∈ G.support, monomial s (π (AddMonoidAlgebra.coeff G s))
  have hΦ : ∀ s, AddMonoidAlgebra.coeff Φ s = π (AddMonoidAlgebra.coeff G s) := fun s => by
    simp only [Φ, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, map_zero]
  refine ⟨Φ, ?_⟩
  ext s
  have h1 := congrArg (fun P => π (AddMonoidAlgebra.coeff P s)) hG

  simp only [coeff_map, hπa, coeff_mul, map_sum, hπm] at h1
  rw [h1, coeff_mul]
  exact Finset.sum_congr rfl fun x _ => by rw [hΦ]

end GroundTheory.Heights₂.Heights
