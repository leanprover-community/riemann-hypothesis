module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormReadingEqGoodModelVectorEvaluationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodModelVectorEqClassSumBaseLevelStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypeFormReadingRightTranslateLiftStatement
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.RankOnto

theorem sumOnto_of_goodRange : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) → ∀ i, BaseTup Y i → SumOnto Y.Z.rd i := by
  intro D X E Y hG i hB j b x hx
  obtain ⟨w, hw, hrd⟩ := GlobalTheory.T.good_form_reading_eq_good_model_vector_evaluation D X E Y i j b x hx
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hT := GlobalTheory.T.good_type_form_reading_right_translate_lift D X E Y i j b x hx
  have hφ : (X.R.HW j (Formalism.IndefR.Links.sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ν i j b • Y.Z.rd i j b x := by
    rw [hrd, smul_smul, mul_inv_cancel₀ hν, one_smul]
  obtain ⟨F, hF, hsum⟩ := GlobalTheory.T.goodModelVector_eq_classSum_baseLevel D X E Y hG i hB j b w hw (fun u hu κ hκ g => by
    rw [hφ, Pi.smul_apply, Pi.smul_apply, hT u hu κ hκ g, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨(Y.Z.ν i j b)⁻¹ • F, Submodule.smul_mem _ _ hF, ?_⟩
  rw [map_smul, ← hsum, hrd]

end GlobalTheory.RankOnto
