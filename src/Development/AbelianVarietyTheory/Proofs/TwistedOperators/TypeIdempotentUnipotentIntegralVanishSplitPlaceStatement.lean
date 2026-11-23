module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentUnipotentIntegralVanishSplitPlace
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


theorem _root_.GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (v : T.S) (a : ℕ), 0 < a → a < V.rank →
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank a) →
    ∀ 𝔉 : IsoFlag V, InConjParabolic (parAt 𝔉 (T.frame v)) a →
    ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v.1)) [μ.IsHaarMeasure] (φ : GLoc D.sp.cm.sig V.gram v.1 → ℂ),
      φ ∈ CcLoc D.sp.cm.sig V.gram v.1 → ∀ f : GLoc D.sp.cm.sig V.gram v.1 → ℂ,
      (f = GlobalTheory.AutomorphicL2Unitary.conv μ ((T.frame v).idem μ (T.τ v)) φ ∨ f = GlobalTheory.AutomorphicL2Unitary.conv μ φ ((T.frame v).idem μ (T.τ v))) →
    ∀ (ν : Measure (NLoc 𝔉 v.1)) [ν.IsHaarMeasure] (x y : GLoc D.sp.cm.sig V.gram v.1),
      Integrable (fun n : NLoc 𝔉 v.1 => f (x * n * y)) ν ∧ ∫ n : NLoc 𝔉 v.1, f (x * n * y) ∂ν = 0 := by
  first | exact @GlobalTheory.LocConst.unip_integral_vanish | exact GlobalTheory.LocConst.unip_integral_vanish | (intros; apply GlobalTheory.LocConst.unip_integral_vanish <;> assumption)
