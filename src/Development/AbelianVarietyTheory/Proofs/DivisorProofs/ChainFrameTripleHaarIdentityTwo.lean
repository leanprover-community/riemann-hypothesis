module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DefThetaNZ

section Darboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_zero {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd) (h : UA σ Wd.J) :
    M.I om 0 h = 0 := by
  simp [Model.I, theta, GlobalTheory.WeilM.thetaSum]

theorem I_smul' {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd) (c : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ Wd.J) : M.I om (c • Φ) h = c * M.I om Φ h := by
  simp only [Model.I, theta, map_smul, GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left,
    MeasureTheory.integral_const_mul]

theorem I_add' {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd)
    {Φ Ψ : (Fin n × Fin d → AF F) → ℂ} {h : UA σ Wd.J}
    (hΦ : MeasureTheory.IntegrableOn (fun g => theta om Φ g h) M.dom M.μ)
    (hΨ : MeasureTheory.IntegrableOn (fun g => theta om Ψ g h) M.dom M.μ)
    (hs : ∀ g, om (g, h) Φ ∈ GlobalTheory.WeilM.schA F _ ∧ om (g, h) Ψ ∈ GlobalTheory.WeilM.schA F _) :
    M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  unfold Model.I
  rw [← MeasureTheory.integral_add hΦ hΨ]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun g => ?_)
  show GlobalTheory.WeilM.thetaSum F (om (g, h) (Φ + Ψ)) = GlobalTheory.WeilM.thetaSum F (om (g, h) Φ) + GlobalTheory.WeilM.thetaSum F (om (g, h) Ψ)
  rw [map_add (f := _), GlobalTheory.WeilM.thetaSum_add F (hs g).1 (hs g).2]

end Darboux

end GlobalTheory.DefThetaNZ

namespace GlobalTheory.DefThetaNZ

open scoped Matrix

end GlobalTheory.DefThetaNZ
