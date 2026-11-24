module

public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
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

theorem tiltMap_eq : Reformulated.AutPerF.Tilt.map l (e l).toRingHom = Formalism.Per6.tiltMap l := by
  refine RingHom.ext fun x => Reformulated.AutPerF.Tilt.ext fun n => ?_
  rw [Reformulated.AutPerF.Tilt.coeff_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  change _ = Formalism.Per6.modPEquiv l (PreTilt.coeff n x)
  rw [← ha, Ideal.quotientMap_mk]
  rfl

theorem ainfMap_eq : Reformulated.AutPerF.Ainf.map l (e l).toRingHom = Formalism.Per6.ainfMap l := by
  rw [Reformulated.AutPerF.Ainf.map, tiltMap_eq]
  rfl

theorem acrisNHom_algebraMap (y : Reformulated.AutPerF.AcrisZero l (NC l)) :
    acrisNHom l (algebraMap _ (Reformulated.AutPerF.Acris l (NC l)) y) =
      algebraMap (ACris.ACrisZero ℂ_[l] l) (ACris.ACris ℂ_[l] l) (zeroEquiv l y) :=
  Reformulated.AutPerF.adicMap_algebraMap _ _ _ _ y

theorem zeroEquiv_algebraMap (a : Reformulated.AutPerF.Ainf l (NC l)) :
    zeroEquiv l (algebraMap _ (Reformulated.AutPerF.AcrisZero l (NC l)) a) =
      algebraMap (AInf ℂ_[l] l) (ACris.ACrisZero ℂ_[l] l) a := rfl

theorem acrisN_algebraMap_ainf (a : Reformulated.AutPerF.Ainf l (NC l)) :
    acrisN l (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.Acris l (NC l)) a) =
      algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) a := by
  rw [IsScalarTower.algebraMap_apply (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AcrisZero l (NC l))
    (Reformulated.AutPerF.Acris l (NC l))]
  change acrisNHom l _ = _
  rw [acrisNHom_algebraMap, zeroEquiv_algebraMap,
    IsScalarTower.algebraMap_apply (AInf ℂ_[l] l) (ACris.ACrisZero ℂ_[l] l) (ACris.ACris ℂ_[l] l)]

theorem cA_algebraMap (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cA l (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a) =
      algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Formalism.Per6.ainfMap l a) := by
  rw [cA_apply, Reformulated.AutPerF.Acris.map_algebraMap, ainfMap_eq]
  exact acrisN_algebraMap_ainf l _

end Cmp6
