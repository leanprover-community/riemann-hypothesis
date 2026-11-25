module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)

def SiegelWeilFock (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank →
    (wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH φ)

end GlobalTheory.Core.Rk.IP

end
