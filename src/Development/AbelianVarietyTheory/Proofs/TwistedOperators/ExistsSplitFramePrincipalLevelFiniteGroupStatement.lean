module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitFramePrincipalLevelFiniteGroup
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.exists_splitFrame_principalLevel_finiteGroup : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → ∃ (a : GfC V) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ L.Pg) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ∀ v : S, ResF v.1 ≃+* kP (pl v).1), (∀ v ∉ S, ∀ k ∈ Kv V v, ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ levG V β (flag1L L)) ∧ ∀ (v : S) (k : Kv V v), ∃ g0 : G0 L.Pg L.r, IsLevelLift V β L g0 ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∧ (∀ PP, PP ≠ pl v → g0 PP = 1) ∧ ∀ i j : Fin L.r, (g0 (pl v)).1 i j = ρ v (((s v).red k).1 (i.cast h) (j.cast h)) := by
  first | exact @GlobalTheory.TrPtFrame.exists_splitFrame_levG | exact GlobalTheory.TrPtFrame.exists_splitFrame_levG | (intros; apply GlobalTheory.TrPtFrame.exists_splitFrame_levG <;> assumption)
