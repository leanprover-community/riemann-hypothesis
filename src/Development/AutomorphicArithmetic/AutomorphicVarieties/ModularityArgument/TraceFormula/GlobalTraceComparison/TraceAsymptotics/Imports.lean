module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import GroundTheory.LocalFields.PadicLogSeries
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

@[expose] public section

open GlobalTheory.CuspRep GlobalTheory.PRep

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.adm :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted := by
  intro E _ _ _ n w τ U hU
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have hadm := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (w.adicCompletion E) n τ.V τ.ρ τ.smooth τ.irred
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hsmall : FiniteDimensional ℂ (fixed τ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n))) :=
    hadm.2 _ (hU.inter ho) (hc.inter_left (U.isClosed_of_isOpen hU))
  have hle : fixed τ.ρ U ≤ fixed τ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n)) := fun v hv h => hv ⟨h.1, h.2.1⟩
  exact Submodule.finiteDimensional_of_le hle
