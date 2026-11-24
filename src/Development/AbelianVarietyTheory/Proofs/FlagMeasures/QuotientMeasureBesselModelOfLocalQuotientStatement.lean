module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientMeasureBesselModelOfLocalQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.quotientMeasure_besselModel_of_local_quotient : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)))) (ν.map (fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹))) := by
  first | exact @GlobalTheory.quotMeas_besselModel_of_quotLoc | exact GlobalTheory.quotMeas_besselModel_of_quotLoc | (intros; apply GlobalTheory.quotMeas_besselModel_of_quotLoc <;> assumption)
