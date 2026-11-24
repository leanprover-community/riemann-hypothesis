module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DoublingMethodOfEisensteinFacts
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

section
namespace GlobalTheory.PrimIn
theorem twisted_siegel_weil_identity_of_formula :
    GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite →
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 →
    GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable →
    _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems := by
  intro q1 q2 q3 q4 q5 q6 q7 sw e1 e2 q10 q11 q12 q14
  exact ⟨q1, q2, q3, q4, q5, q6, q7, sw, _root_.GlobalTheory.T.doubling_zeta_of_eisenstein_facts q2 e1 e2, q10, q11, q12,
    GlobalTheory.weilRepresentationUnitaryPair, q14⟩
end GlobalTheory.PrimIn
end

section

theorem _root_.GlobalTheory.T.twisted_siegel_weil_identity : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems := by
  first | exact @_root_.GlobalTheory.PrimIn.twisted_siegel_weil_identity_of_formula | exact _root_.GlobalTheory.PrimIn.twisted_siegel_weil_identity_of_formula | (intros; apply _root_.GlobalTheory.PrimIn.twisted_siegel_weil_identity_of_formula <;> assumption)
end
