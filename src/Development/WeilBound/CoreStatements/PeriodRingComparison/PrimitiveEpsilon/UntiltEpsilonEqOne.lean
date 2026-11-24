module

public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
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

theorem untilt_tiltMap (x : Reformulated.AutPerF.Tilt l (OC l)) :
    PreTilt.untilt (Formalism.Per6.tiltMap l x) = e l (PreTilt.untilt x) := by
  rw [← tiltMap_eq]
  exact Reformulated.AutPerF.Tilt.untilt_map (e l).toRingHom x

theorem untilt_epsilon_eq_one : PreTilt.untilt (PositivityTheory.LocInh.εO l) = (1 : OC l) := by
  apply (e l).injective
  rw [← untilt_tiltMap, PositivityTheory.LocInh.εO, PositivityTheory.LocInh.tiltMap_tiltInv, map_one]
  exact untilt_epsilon

def eps0 : Reformulated.AutPerF.tateModule l (OC l) := ⟨PositivityTheory.LocInh.εO l, untilt_epsilon_eq_one l⟩

theorem tiltMap_epsilon : Formalism.Per6.tiltMap l (eps0 l).1 = epsilon l := (PositivityTheory.LocInh.tiltMap_tiltInv l _)

theorem epsilon_isPrimitive : Reformulated.AutPerF.IsPrimitive (eps0 l) := by
  unfold Reformulated.AutPerF.IsPrimitive
  intro h
  have hne : PreTilt.untilt ((frobeniusEquiv (PreTilt (NC l) l) l).symm (epsilon l)) ≠ 1 := by
    rw [epsilon, AInf.frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]
    intro h
    exact rootSeq_one_ne_one (congrArg Subtype.val h)
  apply hne
  have h1 : Formalism.Per6.tiltMap l ((frobeniusEquiv (Reformulated.AutPerF.Tilt l (OC l)) l).symm (eps0 l).1) =
      (frobeniusEquiv (PreTilt (NC l) l) l).symm (epsilon l) := by
    rw [RingHom.map_frobeniusEquiv_symm, tiltMap_epsilon]
  rw [← h1, untilt_tiltMap, h, map_one]

end Cmp6
