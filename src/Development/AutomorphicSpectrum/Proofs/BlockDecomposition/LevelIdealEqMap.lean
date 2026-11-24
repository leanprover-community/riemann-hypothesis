module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem lev_IB_eq_map {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : (lev h k).IB = (lev h k).I.map (lev h k).ι := by
  have key : IB (fk l k) (xi0 l) = (I (fk l k) (xi0 l) l M).map (ι (fk l k) (xi0 l) l M) := by
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨⟩
      have hm : ofW (fk l k) (xi0 l) l M (xi0 l) ∈ I (fk l k) (xi0 l) l M := by
        show ι (fk l k) (xi0 l) l M (ofW (fk l k) (xi0 l) l M (xi0 l)) ∈ IB (fk l k) (xi0 l)
        rw [ι_ofW]
        exact Ideal.subset_span rfl
      have := Ideal.mem_map_of_mem (ι (fk l k) (xi0 l) l M) hm
      rwa [ι_ofW] at this
    · exact Ideal.map_comap_le
  exact key

end GlobalTheory.CompanionTheory.LatC
