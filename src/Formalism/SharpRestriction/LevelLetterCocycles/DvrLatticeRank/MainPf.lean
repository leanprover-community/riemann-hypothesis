module

public import Formalism.SharpRestriction.LevelLetterCocycles.FontExAll
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionHypothesis
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ClassMapPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionHolds
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExtPfMultVEqZero
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobeniusSpanDecomposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GamPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.KapPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.OneGenPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.QuotPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankBounds
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankLinkProof
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfZetaO
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3mixlinkPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3uplinkPfOf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniformiserRingOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.WLocal
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfLeafLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.NormAHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem lifting_theorem_of_uniform_link (hU1L : FirstFrameOfModels) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C :=
  local_theorem_of_leaf_lemmas generator_bound_of_hypotheses lift_bound_of_hypotheses DvdPf.dvdCondition quotient_jumps_subset normR_holds
    uniformiser_ring_of_hypotheses ExtPf.ext_pf w_pf kerlam2_pf ninlam_pf gradNCondition frobPiNCondition gamPiCondition
    OneGenPf.onegen_pf univlink_pf invLiftCondition ClassMapPf.classmap_pf frame_pf modelflink_pf
    exponent_recursion_holds modell_pf modelqlink_pf hU1L kappi_pf RankLink.rank_link_holds
    (RankBounds.u2rank_of_ring u2ring_pf) DescentValuation.down_of_models (u3uplink_pf_of w_pf) u3mixlink_pf

end Formalism.MainNotions.N.Ln34

end
