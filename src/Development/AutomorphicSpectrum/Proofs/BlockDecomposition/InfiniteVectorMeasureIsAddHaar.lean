module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
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
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ)

noncomputable def rowInfEquiv : (Fin k → InfiniteAdeleRing E) ≃+ (Fin k → Cinf E) :=
  AddEquiv.piCongrRight fun _ => (infEq E).symm.toAddEquiv

theorem nuInf_isAddHaarMeasure : (nuInf E k).IsAddHaarMeasure := by
  have hc : Continuous (rowInfEquiv E k) :=
    continuous_pi fun i => (GASplit.continuous_infEq_symm E).comp (continuous_apply i)
  have hc' : Continuous (rowInfEquiv E k).symm :=
    continuous_pi fun i => (continuous_infEq E).comp (continuous_apply i)
  have hp : (Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact AddEquiv.isAddHaarMeasure_map _ (rowInfEquiv E k) hc hc'

end GlobalTheory.CompanionTheory.CutOff
