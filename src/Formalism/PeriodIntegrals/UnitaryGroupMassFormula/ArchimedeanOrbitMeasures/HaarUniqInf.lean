module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushCut
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

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

abbrev GI {D : D7} (X : HidaSetting D) : Type := HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J

def sect {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (y : TupI X) : GI X := by
  classical
  exact if h : ∃ g : GI X, orbM X u' g = y then h.choose else 1

theorem sect_spec {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (y : TupI X) (hy : ∃ g : GI X, orbM X u' g = y) :
    orbM X u' (sect X u' y) = y := by
  classical
  simp only [sect, dif_pos hy]
  exact hy.choose_spec

def kerI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (y : TupI X) : Measure (GI X) :=
  Measure.map (fun h : (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) => sect X u' y * (h : GI X))
    (X.measW u').μHinf

def KerMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → Measurable (kerI X u')

def HaarUniqInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ m : Measure (GI X), (∀ g : GI X, m.map (fun x => g * x) = m) → (∀ C : Set (GI X), IsCompact C → m C < ⊤) →
      ∃ c : ENNReal, c ≠ ⊤ ∧ m = c • X.measG.μGinf

def RegI : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    Measurable (orbM X u') ∧ (∀ g : GI X, Measurable (fun y : TupI X => g • y)) ∧
    (∀ g : GI X, Measurable (fun x : GI X => g * x)) ∧
    (∀ t : GI X, Measurable (fun h : (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) => t * (h : GI X))) ∧
    (∀ C : Set (GI X), IsCompact C → MeasurableSet C ∧ IsCompact (orbM X u' '' C) ∧
      MeasurableSet (orbM X u' '' C)) ∧
    FbI X u' hT ⊆ Set.range (orbM X u') ∧ Set.range (orbM X u') ⊆ IndI X

end PI.AprimeInfW
