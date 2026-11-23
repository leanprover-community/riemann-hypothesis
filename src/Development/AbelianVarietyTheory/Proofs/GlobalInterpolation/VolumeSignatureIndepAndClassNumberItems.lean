module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndepStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanksStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignaturesStatement
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

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem volSigIndep_and_classItemsAt_of_massRatioUnderVolume (hU : ∀ D : D7, Formalism.MainNotions.RT.MassRatioUnderVolume D) :
    ∀ D : D7, VolSigIndep D ∧ ClassItemsAt D (D.sp.Y 0).rank := by
  intro D
  refine ⟨?_, GlobalTheory.T.hermitianClassNumberItems_all_ranks D _⟩
  have key := GlobalTheory.T.adelicQuotientVolume_eq_of_signature_rank_indep (fun D hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr => by
    have h2 : Conclusion2 D := volumeMass_of_unfolding D (hU D hT)
    rw [GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures D hT h2 W P Q hW hs, GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures D hT h2 W₀ P₀ Q₀ hW₀ hs₀]
    have e1 := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    have e2 := Formalism.BasicNotions.sig_sum W₀ hW₀ D.host.φ₀
    rw [hs] at e1
    rw [hs₀] at e2
    simp only at e1 e2
    rw [e1, e2, hr])
  exact key D

end GlobalTheory.Glob
