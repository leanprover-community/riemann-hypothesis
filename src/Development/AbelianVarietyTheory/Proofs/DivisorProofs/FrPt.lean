module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare

variable {D : D7}

def frPt {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : D.what₂.Tau → Fin m → Fin n → ℂ :=
  fun τ => (B' τ * Matrix.of (Z τ) * (B τ)⁻¹ : Matrix (Fin m) (Fin n) ℂ)

def sqSum {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : ℝ := ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2

def gZ (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (Z : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  f (iotaW σ T S (frPt B B' Z)) * Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ)

def thY (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (δ : ℂ)
    (Y : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  gZ σ S T B B' f (δ⁻¹ • Y)

end GlobalTheory.VacRealForm
