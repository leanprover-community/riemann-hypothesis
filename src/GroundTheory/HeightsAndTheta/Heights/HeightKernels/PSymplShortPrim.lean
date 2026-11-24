module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplShortPrim

lemma intVec_smul {ι : Type} (m : ℤ) (w : ι → ℤ) : intVec (m • w) = (m : ℝ) • intVec w := by
  funext i
  simp [intVec]

lemma qf_smul {ι : Type} [Fintype ι] (Y : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    qf Y (c • x) = c ^ 2 * qf Y x := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

end PSymplShortPrim


open PSymplShortPrim in
theorem SymplShortPrim.proof : SymplShortPrim.Statement := by
  intro ι _ _ G hG v w m hvw hv hmin
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hwR : intVec w ≠ 0 := by
    intro h
    apply hw
    funext i
    have := congrFun h i
    simpa [intVec] using this
  have hq : 0 < qf G (intVec w) := by
    have := hG.dotProduct_mulVec_pos hwR
    simpa [qf] using this
  have hle := hmin w hw
  rw [hvw, intVec_smul, qf_smul] at hle
  have hm2 : ((m : ℝ)) ^ 2 ≤ 1 := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hm2' : m ^ 2 ≤ 1 := by exact_mod_cast hm2
  have habs : |m| ≤ 1 := (sq_le_one_iff_abs_le_one m).mp hm2'
  rw [abs_le] at habs
  omega

end GroundTheory.Heights₂.Heights
