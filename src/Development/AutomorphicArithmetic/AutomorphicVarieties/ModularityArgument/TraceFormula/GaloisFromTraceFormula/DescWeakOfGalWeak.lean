module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.GalWeakOfCuspU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescWeak
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CsdDisc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CsdSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.NotTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OnePre
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OneSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OnlyOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.AbsInf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.PartNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.SigmaEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds
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

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.G UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.GlobalTraceComparison

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem descWeak_of_galWeak (hW : GalWeak 4) (hRun : RunTh) : UpperTheory.V.Z.Desc.DescWeak := by
  intro E _ _ _ hunr p _ S _ hsp _ n hn hn4 π hreg hd hsat
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  rcases hRun E hunr n hn1 π hreg hd (fun w hw => hsat w fun h => hw (hsp w h)) with h | ⟨D₁, h1, h2, h3, h4⟩
  · exact h
  obtain ⟨D, r, t, s, hno⟩ := preOf (partNorm absInf) csdSat Asm.places E n hn1 π hd D₁ h1 h2 h3 h4
  obtain ⟨D₀, hone, hr⟩ := onePre E n hn1 π hreg (csdDisc E n hn1 π hd)
  have hs := oneSat E n hn1 π D₀ hone
  have ht : D₀.ThetaStable := (csdSat E n hn1 π hd).mono fun w ⟨B, a, b⟩ => ⟨B, (hs w B).1 a, fun u hu => (hs u _).1 (b u hu)⟩
  obtain ⟨e, he⟩ := Rig.locRigid_holds E n D D₀ r hr (galStep_le hW E hunr n hn4 D D₀ r hr t ht
    (s.mono fun w hw hx => (hw hx).imp fun B hB => ⟨hB.1, (hs w B).1 hB.2⟩))
  exact absurd (onlyOne cuspOrTwo notTwo oneSat E n hn1 π D D₀ e r hone he) hno

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
