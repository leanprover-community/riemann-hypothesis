module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section
namespace TestFunctionNorms
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.CoefModel
open Formalism.UG
open scoped ComplexOrder
namespace GlobalTheory.CompanionTheory.TestVal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Lat
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
end Lat
section Cast
variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
end Cast
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
theorem test_value_psi_finite_infinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPsiK ∧ InfPsiK := by
  intro _
  constructor
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w c u hu x
    exact pullback_fin_relation _ _ w c u hu x
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ σ c u x
    exact inf_aux _ _ σ c u x
end GlobalTheory.CompanionTheory.TestVal
end
end
end TestFunctionNorms
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.test_vector_value_factorization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPsiK ∧ InfPsiK := by
  exact @_root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite
end
end
