module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralUnramifiedPlacesUnionEqLocalFactors
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
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


theorem _root_.GlobalTheory.T.setIntegral_unramified_places_union_eq_local_factors : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ → ∀ s : ℂ, (A.rank : ℝ) < s.re → Integrable (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s) m → ∀ S₁ S₂ : Finset (FinPl D), Sf ⊆ S₁ → Disjoint S₁ S₂ → ∀ S₃ : Finset (FinPl D), (∀ u, u ∈ S₃ ↔ u ∈ S₁ ∨ u ∈ S₂) → ∫ g in openOff A LA S₃, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m = (∏ v ∈ S₂, GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s) * ∫ g in openOff A LA S₁, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
  first | exact @GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union | exact GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union | (intros; apply GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union <;> assumption)
