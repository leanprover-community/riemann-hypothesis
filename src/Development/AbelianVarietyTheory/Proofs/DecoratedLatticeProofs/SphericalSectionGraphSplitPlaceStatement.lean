module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSectionGraphSplitPlace
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
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)


theorem _root_.GlobalTheory.T.sphericalSection_graph_splitPlace : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (e : Gv A v ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)), IsSplitChart D.sp.cm.sig A.gram L h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin A.rank → ℤ) (t : GL (Fin A.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := A.rank), ∀ k₂ ∈ KGL w (n := A.rank), φ (ioAt A v (e.symm (k₁ * t * k₂))) = (((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV D.host.E w : ℂ) ^ (-((A.rank : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) := by
  first | exact @GlobalTheory.Core.Rk.KerSplit.sphSec_split | exact GlobalTheory.Core.Rk.KerSplit.sphSec_split | (intros; apply GlobalTheory.Core.Rk.KerSplit.sphSec_split <;> assumption)
