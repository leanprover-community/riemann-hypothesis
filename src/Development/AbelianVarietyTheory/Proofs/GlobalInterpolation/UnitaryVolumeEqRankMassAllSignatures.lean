module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureConditionStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolEqMassSelfDualRankGeTwoStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeNegativeDefiniteEqOppositeStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem vol_eq_massI_all_sig : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK →
    (∀ τ, W.sig τ = (P, Q)) → D.vol W = massI D (P + Q) := by
  intro D hT h2 W P Q hW hs
  have hv : DefiniteVolumeEqMass D := mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
    (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D)
  have hrk : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hs D.host.φ₀] at this
    exact this.symm
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    rw [← hrk]
    exact hv W hW (fun τ => by rw [hs τ, hrk]; rfl)
  · by_cases h2r : 2 ≤ P + Q
    · exact GlobalTheory.T.vol_eq_mass_selfDual_rank_ge_two D hT h2 hv W P Q hW hs h2r
    · have hP : P = 0 := by omega
      have hQ1 : Q = 1 := by omega
      subst hP hQ1
      have e1 : D.vol W = D.vol (GlobalTheory.NegSpace.neg W) :=
        GlobalTheory.T.volume_negativeDefinite_eq_opposite D hT W 1 hW hs
      have hN : (GlobalTheory.NegSpace.neg W).SigOK := GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition _ W hW
      have e2 : D.vol (GlobalTheory.NegSpace.neg W) = massI D (GlobalTheory.NegSpace.neg W).rank :=
        hv _ hN (fun τ => by rw [GlobalTheory.NegSpace.neg_sig, hs τ, GlobalTheory.NegSpace.neg_rank, hrk])
      rw [e1, e2, GlobalTheory.NegSpace.neg_rank, hrk]

end GlobalTheory.Glob
