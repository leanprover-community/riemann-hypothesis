module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentIntegralsPureTensorVanishOfLocal
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local : ∀ (D : D7) (V : HSp D) (𝔉 : IsoFlag V) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ)
    (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) →
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    (∀ (ν : Measure (NLoc 𝔉 v)) [ν.IsHaarMeasure] (x y : GLoc D.sp.cm.sig V.gram v),
      ∫ n : NLoc 𝔉 v, ff v (x * n * y) ∂ν = 0) →
    UnipIntegralsVanish 𝔉 (tensor D.sp.cm.sig V.gram fa ff) := by
  first | exact @GlobalTheory.TestConstTerm.unipIntegralsVanish_tensor | exact GlobalTheory.TestConstTerm.unipIntegralsVanish_tensor | (intros; apply GlobalTheory.TestConstTerm.unipIntegralsVanish_tensor <;> assumption)
