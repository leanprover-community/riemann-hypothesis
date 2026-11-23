module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSrcMemOrb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.GlobalHarmonicExistence.InvolutionIntegrals.IntegralCompInvol
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTranslAd
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

private theorem conj_of_central {G : Type} [Group G] (a b : G) (h : a⁻¹ * b ∈ Subgroup.center G) (t : G) :
    b * t * b⁻¹ = a * t * a⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp h t
  calc b * t * b⁻¹ = a * ((a⁻¹ * b) * t) * (a⁻¹ * b)⁻¹ * a⁻¹ := by group
    _ = a * (t * (a⁻¹ * b)) * (a⁻¹ * b)⁻¹ * a⁻¹ := by rw [hc]
    _ = a * t * a⁻¹ := by group

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.translF_pf :
    TranslF := by
  intro E _ _ _ n u hu
  have hz : (ratF E n u)⁻¹ * PhiU n (Af E) ∈ Subgroup.center (GL (Fin n) (Af E)) := by
    have h := GeneralLinearGroup.map_center_le (algebraMap E (Af E)) (translad_central E n u hu)
    rw [Subgroup.mem_comap, map_mul, map_inv, translad_map_PhiU] at h
    exact h
  have hc := conj_of_central (ratF E n u) (PhiU n (Af E)) hz
  refine ⟨fun g => ?_, ?_, PhiU n (Af E), ?_, fun g => (hc g).symm⟩
  · rw [← hc, Tw.thetaF_eq]
    exact thetaGL_eq n (Af E) _ g
  · rw [← GlobalTheory.EulerTw.Comm.thF_ratF, hu.1, hu.2, one_mul, map_inv]
  · refine Subgroup.mem_iInf.mpr fun w => ?_
    rw [Subgroup.mem_comap, translad_map_PhiU]
    exact GlobalTheory.ThetaSatake.phiU_mem _ n
