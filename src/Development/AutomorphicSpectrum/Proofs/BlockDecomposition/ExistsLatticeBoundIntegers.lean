module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetGenerators
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerMemLatticeSubBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PadicIntMemSub
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCOK

theorem exists_uniform_mem_sub : ∀ (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K),
      Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K _
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.LocalIntegers.exists_finset_generators l K
  choose c hc using GlobalTheory.T.integer_mem_lattice_sub_bound l K
  refine ⟨2 * s.sup c, fun k a => ?_⟩
  obtain ⟨d, hd⟩ := hs a
  have h1 : Lat.kP l K a = ∑ i ∈ s, algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (d i : ℚ_[l])) *
      Lat.kP l K i := by
    have h2 : Lat.kP l K a = algClToBdR l (((a : K) : PadicAlgCl l)) := rfl

    rw [h2, hd, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    rfl

  rw [h1, map_sum]
  refine Subring.sum_mem _ fun i hi => ?_
  rw [map_mul]
  exact Subring.mul_mem _ (GlobalTheory.CompanionTheory.LatCZp.padicInt_mem_sub l _ k (d i))
    (hc i _ k (Nat.mul_le_mul_left 2 (Finset.le_sup hi)))

end GlobalTheory.CompanionTheory.LatCOK
