module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Lemmata.MiscLemmasB.Imports
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.HfinExistsMat
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ga_facts (V : HSp D) :
    IsTopologicalGroup (GA D V) ∧ T2Space (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
      SecondCountableTopology (GA D V) ∧ BorelSpace (GA D V) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram

theorem ae_facts : IsTopologicalRing (AE D) ∧ T2Space (AE D) ∧ LocallyCompactSpace (AE D) ∧
    SecondCountableTopology (AE D) ∧ BorelSpace (AE D) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.tens_facts (AF D.host.F) D.sp.cm.deg2

theorem gQDiscrete_holds : GQDiscrete D := fun V => G5.hfin_disc D.sp.cm.sig V.gram

theorem gQ_countable (V : HSp D) : Countable (GQ V) := G5.hfin_countable D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) := by
  obtain ⟨h1, -, -, -, h5⟩ := ga_facts D V
  infer_instance

theorem gfC_secondCountable (V : HSp D) : SecondCountableTopology (GfC V) := by
  obtain ⟨-, -, -, h4, -⟩ := ga_facts D V
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

theorem fundDomExists_holds : FundDomExists D := fun V => by
  obtain ⟨h1, -, -, h4, h5⟩ := ga_facts D V
  have := gQDiscrete_holds D V
  exact _root_.Bl.SecondBlockLemmaC.goal1 (GQ V)

end Formalism.IndefR.Eqv

end
