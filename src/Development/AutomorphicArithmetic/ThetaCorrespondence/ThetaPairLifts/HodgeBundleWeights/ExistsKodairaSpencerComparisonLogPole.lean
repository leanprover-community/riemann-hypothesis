module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerMatrixEqZeroOffConjBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFilStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsConstantCechKodairaSpencerValue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerMapCompatibilities
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogPole
theorem exists_kodaira_spencer_comparison_log_pole : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c), ∃ s : ℚ, s ≠ 0 ∧ KSCompare TF s := by
  intro PP E _ _ _ H Dw l Xo c TF
  obtain ⟨s, hs0, hcore⟩ := _root_.GlobalTheory.T.cech_kodaira_spencer_class_constant PP
  refine ⟨s, hs0, ?_⟩
  intro U n e v hv D Θ hΘ K _ _ P hU hP y' hU' hy' hev
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, g, hπ, hπ', hi, hpol, hu, hbl, hrow, hA, hgA, hA', hgA', hL⟩ :=
    _root_.GlobalTheory.T.kodaira_spencer_map_compatibilities PP E H Dw l Xo c TF U D.1 K P hU y' hU' hy' hev
  have hC := GlobalTheory.T.cechDeformation_gluing_of_logKodairaSpencer E H Dw l Xo c TF U n e v hv D Θ hΘ K P hU hP y' hU' hy' hev A A' π π' i ub h hπ hπ' hi hu
  have hbal := GlobalTheory.T.cechKodairaSpencerMatrix_eq_zero_off_conj_blocks E H Dw l Xo c TF U n e v hv D Θ hΘ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK := hcore K A A' i h g hA hgA hA' hgA' _ hL ψ hpol n (fun a => ub (e.symm a).1 (e.symm a).2)
    (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) (fun a => (hbl _ _).1) hC
    (fun b => hb (e.symm b)) (fun b => hbl _ _)
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, ψ, ub, hb, hπ, hπ', hi, hpol, hu, fun σ k => hbl σ k,
    fun τ a => ?_⟩
  exact GlobalTheory.T.kodairaSpencerRow_of_kodairaSpencerValue_hodgeFil E H Dw K A A' i h hA ψ ub hb n e _ (s : K) (fun σ k => (hbl σ k).1)
    (fun a b hab => by simp only [Matrix.of_apply, hbal a b hab, map_zero]) hK τ.1 a (hrow τ a)
end GlobalTheory.LogPole
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.kodaira_spencer_comparison_along_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c), ∃ s : ℚ, s ≠ 0 ∧ KSCompare TF s := by
  exact @_root_.GlobalTheory.LogPole.exists_kodaira_spencer_comparison_log_pole
end
