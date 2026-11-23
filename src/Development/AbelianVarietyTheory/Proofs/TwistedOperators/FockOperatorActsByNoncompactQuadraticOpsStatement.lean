module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fock_operator_acts_by_noncompact_quadratic_ops : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ Gn : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (BT τ * YT * (BT τ)⁻¹ * u - u * (BS τ * YS * (BS τ)⁻¹)) f) ∧ ∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → (∀ g, IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ipO μ 𝓕 (Gn f) g = 0) → ∀ P, Gn (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT f (fockP τ (pS τ) (pT τ) YS YT P) := by
  first | exact @GlobalTheory.FockLieQuad.acts_by_fockP | exact GlobalTheory.FockLieQuad.acts_by_fockP | (intros; apply GlobalTheory.FockLieQuad.acts_by_fockP <;> assumption)
