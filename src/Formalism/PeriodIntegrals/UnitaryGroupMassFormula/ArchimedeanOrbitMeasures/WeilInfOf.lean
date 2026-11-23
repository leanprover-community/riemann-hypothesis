module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AinfValueOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem weilInf_of (hH : HtotInf) : WeilInf := by
  intro D X hb FdN FdN' u u' hX f hf s hs
  obtain ⟨e1, e2, e3⟩ := hH X hb FdN FdN' u u' hX
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  haveI : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have hL : Measure.IsMulLeftInvariant ((X.measW u').μHinf : Measure (MulAction.stabilizer
      (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u'))))) :=
    (X.measW_norm u').2.1.toIsMulLeftInvariant
  have h0 : (X.measW u').μHinf Set.univ ≠ 0 := by rw [e1]; exact e2.ne'
  have hfin : (X.measW u').μHinf Set.univ ≠ ⊤ := by rw [e1]; exact e3.ne
  exact PI.AprimeInfA.unfold_stab (G := HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')))
    (PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _)
    X.measG.μGinf (X.measW u').μHinf hL h0 hfin f hf s hs

end PI.AprimeInfW
