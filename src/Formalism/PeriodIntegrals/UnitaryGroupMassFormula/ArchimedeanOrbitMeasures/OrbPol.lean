module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInf
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

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def cTI {D : D7} (X : HidaSetting D) (a : MfI X) : MfI X :=
  Matrix.transpose (a.map (sigR (Ainf X.B.I.F) X.B.I.cm.sig))

def RmulFacts : Prop := ∀ {D : D7} (X : HidaSetting D),
    (∀ a : MfI X, Measurable (rmulT X a)) ∧ (∀ a b : MfI X, ∀ Y, rmulT X a (rmulT X b Y) = rmulT X (b * a) Y) ∧
    (∀ (g : GI X) (a : MfI X) (Y : TupI X), g • rmulT X a Y = rmulT X a (g • Y)) ∧
    (∀ (a : MfI X) (Y : TupI X), gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X a Y) =
      cTI X a * gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y * a) ∧
    (∀ a b : MfI X, cTI X (a * b) = cTI X b * cTI X a) ∧ cTI X 1 = 1 ∧
    (∀ K : Set (TupI X), IsCompact K → MeasurableSet K) ∧ (∀ a : MfI X, Continuous (rmulT X a))

def NearFacts : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∀ T ∈ Ω₁, IsUnit (a T) ∧
      ∀ Y : TupI X, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = (T : Matrix _ _ _) → Y ∈ IndI X

def FibAllT : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ T : HmI X, InvI X (fibInf T) ∧ LFI X (fibInf T)

end PI.AprimeInfW
