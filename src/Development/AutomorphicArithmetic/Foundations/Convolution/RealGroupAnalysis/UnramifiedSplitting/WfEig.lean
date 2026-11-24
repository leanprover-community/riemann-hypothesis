module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfEig
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
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.wfEig :
    ∀ (K : Type) [Field K] [NumberField K] (f : GL (Fin 2) (A K) → ℂ), Continuous f → (∀ γ g, f (ratGL K 2 γ * g) = f g) →
      (∀ b g, Wf f (gl (nU b) * g) = ψ (-b) * Wf f g) ∧ ∀ v B, EigAt v B f → EigAt v B (Wf f) := by
  intro K _ _ f hc hl
  exact ⟨(UpperTheory.ConvolutionTheory.R2.Pp.wfBasic K f ⟨hc, hl⟩).2.1, UpperTheory.ConvolutionTheory.R2.Pp.wfEig K f ⟨hc, hl⟩⟩
