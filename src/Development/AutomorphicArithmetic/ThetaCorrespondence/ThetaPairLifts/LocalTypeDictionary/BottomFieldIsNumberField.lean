module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormBottom
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomSpannedByClassSums
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomSpannedByTwistedClassSums
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTwistedClassSumsAlgebraic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ClassSumKernelIsAlgebraic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.RowEx.BotField
theorem sums_mem_bottomField (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) {D : D7} {T : Type} [Finite T] {L : LevCh D T}
    {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (hL : L.Is μ₀) (hX : IsBottomTri W i j X) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ SumsIn W (algebraMap M ℂ) X := by
  obtain ⟨M₁, h₁, Ω, hΩ, e₁⟩ := field_of_gens (fun t h k => X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (_root_.GlobalTheory.T.bottom_spanned_by_classSums hP hI hL hX) (_root_.GlobalTheory.T.bottom_classSums_algebraic hP hI hL hX)
  obtain ⟨M₂, h₂, Ω', hΩ', e₂⟩ := field_of_gens (fun t h k => X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (_root_.GlobalTheory.T.bottom_spanned_by_twistedClassSums hP hI hL hX) (_root_.GlobalTheory.T.bottom_twistedClassSums_algebraic hP hI hL hX)
  refine ⟨M₁ ⊔ M₂, inferInstance, Ω, Ω', hΩ, hΩ', fun t h hh => ⟨fun k _ => ?_, fun k _ => ?_⟩⟩
  · exact ⟨⟨_, (le_sup_left : M₁ ≤ _) (e₁ t h hh k)⟩, rfl⟩
  · exact ⟨⟨_, (le_sup_right : M₂ ≤ _) (e₂ t h hh k)⟩, rfl⟩
end GlobalTheory.RowEx.BotField
theorem GlobalTheory.RowEx.bottomField_isNumberField : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → NFBot := by
  intro hP hI
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => by
    haveI : Finite T := hS.fin
    have hL : R.toLevCh.Is A.μ0 := hS.core.lev
    have hex : ∀ ij : Fin D.R.m × Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
        ∃ (A₁ A₂ WW : HSp D) (X : Tri T A₁ A₂ WW), IsBottomTri ch.W ij.1 ij.2 X ∧ SumsIn ch.W (algebraMap M ℂ) X := by
      intro ij
      obtain ⟨A₁, A₂, WW, X, hX⟩ := exists_bottomTri hL ch.G ch.W ij.1 ij.2
      obtain ⟨M, hM, hs⟩ := _root_.GlobalTheory.RowEx.BotField.sums_mem_bottomField hP hI hL hX
      exact ⟨M, hM, A₁, A₂, WW, X, hX, hs⟩
    choose M hM hB using hex
    haveI := hM
    refine ⟨⨆ ij, M ij, IntermediateField.finiteDimensional_iSup_of_finite, fun i j => ?_⟩
    obtain ⟨A₁, A₂, WW, X, hX, hs⟩ := hB (i, j)
    refine ⟨A₁, A₂, WW, X, hX, GlobalTheory.RowEx.BotField.sumsIn_mono hs ?_⟩
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨z, (le_iSup M (i, j) : M (i, j) ≤ _) z.2⟩, rfl⟩
  ⟩⟩
end
end
