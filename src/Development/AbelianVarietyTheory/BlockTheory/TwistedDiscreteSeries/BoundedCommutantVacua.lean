module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField
open GlobalTheory.Size (l2O)
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Defs

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W))

variable {V W}

variable (V W)

def IsVac (θ : InfFam D) (sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (sW τ)) f

end Defs

section Basic₂

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {θ : InfFam D}

theorem exists_isVac_ne_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) (sV τ)) (hW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) :
    ∃ f, IsVac ψ V W θ sV sW f ∧ f ≠ 0 := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ V W _ _ hV hW _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  have h := hf 1
  simp only [one_mul] at h
  exact ⟨f, ⟨h.1, h.2.2⟩, f0⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

end
