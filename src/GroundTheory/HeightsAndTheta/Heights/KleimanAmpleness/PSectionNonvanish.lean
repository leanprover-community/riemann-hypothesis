module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionNonvanishSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropTerm
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem SectionNonvanish.proof : SectionNonvanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hpp _ hle ⟨i, hi⟩ D hD
  have hxi : x i ≠ 0 := fun h0 =>
    hi (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i)).mpr (by rw [aeval_X, h0])))
  refine not_forall_not.mp fun hcon => ?_
  let I : Chart x := singleChart hxi
  have hsec : ∀ s ∈ D.toSubSystem.secs, s ∈ idealMod pp I * D.toSubSystem.sub I := by
    intro s hs
    by_contra hs'
    refine hcon s ⟨hs, I, ?_⟩
    rwa [SubSystem.twist_sub_eq_mul_of_line]
  obtain ⟨P, hP⟩ := D.invertible I
  have hsub : D.toSubSystem.sub I ≤ idealMod pp I * D.toSubSystem.sub I := by
    rw [← hD I, Submodule.span_le]
    intro s hs
    rw [hD I]
    exact hsec s hs
  have hone : (1 : Submodule (chartRing k x I) Ω) ≤ idealMod pp I :=
    calc (1 : Submodule (chartRing k x I) Ω) = D.toSubSystem.sub I * P := hP.symm
      _ ≤ idealMod pp I * D.toSubSystem.sub I * P := mul_le_mul' hsub le_rfl
      _ = idealMod pp I := by rw [mul_assoc]; erw [hP]; rw [mul_one]
  have h1 : (1 : Ω) ∈ idealMod pp I := hone (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  refine SectionCount.Drop.Term.one_not_mem_idealMod hpp hle (I := I) (fun j hj => ?_) h1
  obtain rfl : j = i := Finset.mem_singleton.mp hj
  exact hi

end

end GroundTheory.Heights₂.Heights.Kleiman
