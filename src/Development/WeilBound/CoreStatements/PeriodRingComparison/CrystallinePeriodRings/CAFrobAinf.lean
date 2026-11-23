module

public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.EqZeroOfPMulEqZero
public import Development.WeilBound.CoreStatements.PeriodRingComparison.AinfAlgebraMaps.CAAlgebraMapGOC
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open GroundTheory.PAdicHodge
namespace Cmp6
variable (l : ℕ) [Fact l.Prime]

theorem cA_frob_ainf (w : Reformulated.AutPerF.Ainf l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.frob l (OC l) (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) w)) =
      ACris.phi (K := ℂ_[l]) (p := l) (cA l (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) w)) := by
  rw [Reformulated.AutPerF.Acris.frob_algebraMap, cA_algebraMap, cA_algebraMap]
  have h : Formalism.Per6.ainfMap l (WittVector.frobenius w) =
      WittVector.frobenius (Formalism.Per6.ainfMap l w) := by
    ext n
    simp [Formalism.Per6.ainfMap, WittVector.map_coeff, WittVector.coeff_frobenius_charP]
  rw [ACris.phi_algebraMap]
  exact congrArg (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)) h

theorem cA_frob (x : Reformulated.AutPerF.Acris l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.frob l (OC l) x) = ACris.phi (K := ℂ_[l]) (p := l) (cA l x) := by
  have h : (cA l).toRingHom.comp (Reformulated.AutPerF.Acris.frob l (OC l)) =
      (ACris.phi (K := ℂ_[l]) (p := l)).comp (cA l).toRingHom := by
    refine Reformulated.AutPerF.Acris.hom_ext fun a => ?_
    have := zero_ext l
      (F := ((cA l).toRingHom.comp (Reformulated.AutPerF.Acris.frob l (OC l))).comp
        (algebraMap (Reformulated.AutPerF.AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l))))
      (G := ((ACris.phi (K := ℂ_[l]) (p := l)).comp (cA l).toRingHom).comp
        (algebraMap (Reformulated.AutPerF.AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l))))
      (fun w => by
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply]
        exact cA_frob_ainf l w) a
    simpa only [RingHom.comp_apply] using this
  exact RingHom.congr_fun h x

end Cmp6
