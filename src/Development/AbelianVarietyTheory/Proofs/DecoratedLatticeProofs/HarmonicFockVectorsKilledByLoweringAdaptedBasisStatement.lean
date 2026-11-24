module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarmonicFockVectorsKilledByLoweringAdaptedBasis
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

theorem _root_.GlobalTheory.T.harmonicFockVectors_killed_by_lowering_adaptedBasis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), S.SigOK → T.SigOK → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → ∀ p : D.what₂.Tau → ℕ, (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsONBasis (gramAt D T τ) (cart M τ) (BT τ) (p τ)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ P : PolF D T.rank S.rank, (∀ τ, ∀ a b : Fin T.rank, p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) → GlobalTheory.RawLift.FockCoef.Killed om θ M (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P) := by
  first | exact @GlobalTheory.FockKillAdapted.killed_of_harmonic_adapted | exact GlobalTheory.FockKillAdapted.killed_of_harmonic_adapted | (intros; apply GlobalTheory.FockKillAdapted.killed_of_harmonic_adapted <;> assumption)
