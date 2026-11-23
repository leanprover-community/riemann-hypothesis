module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtHeisenbergThetaSeries
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff


theorem _root_.GlobalTheory.T.hasDerivAt_heisenberg_thetaSeries : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ' : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ f' : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f' w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ' (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) f w) (f' w) 0 := by
  first | exact @GlobalTheory.Core.Rk.OntoDer.hasDerivAt_heisO_thetaSeries | exact GlobalTheory.Core.Rk.OntoDer.hasDerivAt_heisO_thetaSeries | (intros; apply GlobalTheory.Core.Rk.OntoDer.hasDerivAt_heisO_thetaSeries <;> assumption)
