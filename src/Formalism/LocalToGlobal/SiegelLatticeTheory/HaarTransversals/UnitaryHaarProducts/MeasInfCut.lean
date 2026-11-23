module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
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

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.MeasInf

def toInfL (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I) (s : I.Ginf) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J :=
  (Formalism.L2.SG.Measures.splitA I.cm.sig I.J (Formalism.L2.SG.AdBridge.toHA I hb (s, 1))).1

def InfTransfer : Prop :=
  ∀ (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (T : I.F), (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r).IsStd I.cm.sig I.J T →
    ∀ muN muH : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) muN →
      IsHaarOnSet I (Hset I (Set.range e ∪ Set.range f ∪ {z})) muH →
      ∃ (μNinf : Measure (Formalism.L2.SG.Sub.Nsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
          (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r)))
        (μHinf : Measure (Formalism.L2.SG.Sub.Hsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
          (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r))),
        μNinf.IsHaarMeasure ∧ μHinf.IsHaarMeasure ∧
        Formalism.L2.SG.Measures.amb μNinf = muN.map (toInfL I hb) ∧ Formalism.L2.SG.Measures.amb μHinf = muH.map (toInfL I hb)

end Formalism.L2.SG.Pf.MeasInf
