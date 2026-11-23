module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilAction_negPair_pureTensor_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D (GlobalTheory.ChiGrid.negSp S) × GA D T →* Module.End ℂ (WO (GlobalTheory.ChiGrid.negSp S) T → ℂ)), IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ - (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → (∀ τ, IsFockVacAt (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) θ τ (cplxO (-1) 1) f) → ∀ g ∈ GinfC (GlobalTheory.ChiGrid.negSp S), ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ).map (starRingEnd ℂ)) (fun τ => ((((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  first | exact @GlobalTheory.FockRealNeg.om_pureTensorO_neg | exact GlobalTheory.FockRealNeg.om_pureTensorO_neg | (intros; apply GlobalTheory.FockRealNeg.om_pureTensorO_neg <;> assumption)
