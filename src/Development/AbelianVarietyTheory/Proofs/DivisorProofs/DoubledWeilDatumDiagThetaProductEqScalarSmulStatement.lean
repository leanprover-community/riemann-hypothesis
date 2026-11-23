module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmul
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledWeilDatum_diag_thetaProduct_eq_scalar_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  first | exact @GlobalTheory.DblThetaRestrict.scalar | exact GlobalTheory.DblThetaRestrict.scalar | (intros; apply GlobalTheory.DblThetaRestrict.scalar <;> assumption)
