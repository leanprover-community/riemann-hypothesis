module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrChInv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.columnArrowKernel_real_eq_detChar_mul_fockKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (x : FinPt G (.top j)) (k : GA D (G.V (.top j))),
    k ∈ GinfC (G.V (.top j)) → ∀ (h : GA D (G.V (.top (j + 1)))),
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * k) h =
        (∏ τ, ((realIn W.θ S.N.fr (.top j) k τ : GL (Fin (G.V (.top j)).rank) ℂ) :
              Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^
                ((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift) *
            ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
              Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
          W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j
            (GlobalTheory.CompactHowe.substF
              (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
                Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((realIn W.θ S.N.fr (.top j) k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) :
                Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ)
              (GlobalTheory.AvgCol.frChInv W S.N j Q))))
            (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := by
  first | exact @GlobalTheory.ColKer.kerA_col_mul_real | exact GlobalTheory.ColKer.kerA_col_mul_real | (intros; apply GlobalTheory.ColKer.kerA_col_mul_real <;> assumption)
