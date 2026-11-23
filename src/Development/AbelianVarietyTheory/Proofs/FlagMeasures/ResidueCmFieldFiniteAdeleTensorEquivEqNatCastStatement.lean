module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ResidueCmFieldFiniteAdeleTensorEquivEqNatCast
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.residue_cmFieldFiniteAdeleTensorEquiv_eq_natCast : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E) (ha : GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (m : ℕ), a ∈ ReciprocityTheory.Aut.ALint D.host.E → Valued.v (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) < 1 → Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩ = (m : Formalism.L2.DIV.kP s.w) := by
  first | exact @GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast | exact GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast | (intros; apply GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast <;> assumption)
