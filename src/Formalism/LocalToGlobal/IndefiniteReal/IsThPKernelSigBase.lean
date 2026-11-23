module

public import Formalism.LocalRingCardinality.DataTheta
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


variable (D) in
def labLL (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

def labE (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ := σ.comp (labLL D τ)

theorem labE_base (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  have h := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) x)
  simpa [labE, labLL, tauE, Host.emb] using h

structure ArchLab (D : D7) where
  perm : D.what₂.Tau ≃ D.what₂.Tau
  side : Bool

def ArchLab.emb (A : ArchLab D) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  if A.side then tauE D (A.perm τ) else (starRingEnd ℂ).comp (tauE D (A.perm τ))

def IsLabOf (σ : D.what₂.LL →+* ℂ) (A : ArchLab D) : Prop := ∀ τ, labE σ τ = A.emb τ



variable (D) in
def LabExists : Prop := ∀ σ : D.what₂.LL →+* ℂ, ∃ A : ArchLab D, IsLabOf σ A




end Formalism.IndefR.Conj

end
