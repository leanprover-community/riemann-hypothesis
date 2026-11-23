module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.levelPlaces_integral_nonzero_constant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (B W H : HSp D) (o : OrthDec B W H) (χA χW : (AE D)ˣ →* Circle) (omB : WRep A B) (omW : WRep A W) (omH : WRep A H), IsWeilDatumO ψ A B χA χW omB → IsWeilDatumO ψ A W χA χW omW → IsWeilDatumO ψ A H χA 1 omH → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u ∈ A0 θ A cA, (∀ κ ∈ prin A β Z, ∀ g, u (g * κ) = u g) → ∀ (sW : RealMat W) (Φ : WO A W → ℂ), Occ ψ θ sW omW m β Z u Φ → ∀ f, IsThetaFunO ψ A H f → f ≠ 0 → (∀ κ ∈ prin A β Z, omH (κ, 1) f = f) → (∀ b ∈ GinfC A, omH (b, 1) f = f) → (∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef omH ν 𝓕 f f g = 0) → ∀ νB 𝓕B, IsCovolOne (ratL B A) νB 𝓕B → ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ, ∫ g in openOff A (frameLat A) (under Z), integrand omB m νB 𝓕B (frameLat A) a (o.boxT A Φ f) (o.boxT A Φ f) u u s g ∂m = C := by
  first | exact @GlobalTheory.Core.Rk.Exh.LocalConst.integral_const | exact GlobalTheory.Core.Rk.Exh.LocalConst.integral_const | (intros; apply GlobalTheory.Core.Rk.Exh.LocalConst.integral_const <;> assumption)
