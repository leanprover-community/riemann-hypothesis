module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeDpowClosedOfHyp
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHc

theorem subsingleton_Bk_zero (l : ℕ) [Fact l.Prime] : Subsingleton (Lat.Bk l 0) := by
  refine Ideal.Quotient.subsingleton_iff.2 ?_
  rw [pow_zero, Ideal.span_singleton_one]

theorem hc_k : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ),
    Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  intro l _ M k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro x _ n
    haveI := subsingleton_Bk_zero l
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact GlobalTheory.CompanionTheory.LatDP.dpClosed _ _ l M k (GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk)

end GlobalTheory.CompanionTheory.LatCHc
