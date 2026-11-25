module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

abbrev OC : Type := ↥(PadicComplexInt l)
abbrev NC : Type := ↥(normInteger ℂ_[l])

abbrev e : OC l ≃+* NC l := Formalism.Per6.intEquiv l

/-- Functoriality of `Acris` applied to the two presentations of the integers of `ℂ_[l]`. -/
def cA : Reformulated.AutPerF.Acris l (OC l) ≃+* ACris.ACris ℂ_[l] l :=
  RingEquiv.ofRingHom (Reformulated.AutPerF.Acris.map l (e l).toRingHom)
    (Reformulated.AutPerF.Acris.map l (e l).symm.toRingHom)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.id_apply, Reformulated.AutPerF.Acris.map_map,
        show (e l).toRingHom.comp (e l).symm.toRingHom = RingHom.id _ from
          RingHom.ext fun y => (e l).apply_symm_apply y, Reformulated.AutPerF.Acris.map_id])
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.id_apply, Reformulated.AutPerF.Acris.map_map,
        show (e l).symm.toRingHom.comp (e l).toRingHom = RingHom.id _ from
          RingHom.ext fun y => (e l).symm_apply_apply y, Reformulated.AutPerF.Acris.map_id])

theorem cA_apply (x : Reformulated.AutPerF.Acris l (OC l)) :
    cA l x = Reformulated.AutPerF.Acris.map l (e l).toRingHom x := rfl

end Cmp6
