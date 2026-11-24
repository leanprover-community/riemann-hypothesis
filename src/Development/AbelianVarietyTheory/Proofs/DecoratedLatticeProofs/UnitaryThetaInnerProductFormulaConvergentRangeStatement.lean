module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryThetaInnerProductFormulaConvergentRange
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

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.unitary_theta_innerProduct_formula_convergent_range : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : GlobalTheory.Core.Rk.IP.WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧ Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m ∧ petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
  first | exact @GlobalTheory.Core.Rk.IP.innerProduct_convergent | exact GlobalTheory.Core.Rk.IP.innerProduct_convergent | (intros; apply GlobalTheory.Core.Rk.IP.innerProduct_convergent <;> assumption)
