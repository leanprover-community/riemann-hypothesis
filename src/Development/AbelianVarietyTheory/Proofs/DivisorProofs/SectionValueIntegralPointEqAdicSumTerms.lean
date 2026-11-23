module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoefficientSectionCoordinateRigStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorRigidificationAllLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationTermsRationalPointFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericPointIntegralSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointCongruentTermSumStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

theorem eval_at_integral : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))) (g' : GtPtF D.toPre (FractionRing V)) (l : FractionRing V), l ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g → IntTerm.Ext U.toUnifPre x h → GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.FrRel U.toUnifPre w₀ x e h l → ∃ w : Frm D.toPre (FractionRing V) 1 g'.b, w.IsGen ∧ IntTerm.IntFrm D.toPre g.b w l ∧ IntTerm.Lies U.toUnifPre w₀ g' w x e := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ x e h g g' l hl hF hExt hP hR
  obtain ⟨f, hf, hfv⟩ := hR
  obtain ⟨t, ht, htl⟩ := GlobalTheory.T.exists_integral_generator_rigidification_all_levels V hV D A G U.toUnifPre h g hF f hf
  have hφ : DegPre.lineφ D.toPre (FractionRing V) g'.b = fun i =>
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (![(η[D.toPre.P.A]).left, g.b.left] : Fin 2 → _) i := by
    funext i
    fin_cases i
    · exact Over.comp_left (f := toUnit (TF (R := V) (FractionRing V))) (g := η[D.toPre.P.A])
    · exact hP.1
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre (FractionRing V) g'.b)
    (ε' := DegPre.lineε 1) (by rw [hφ]; exact fun _ _ _ => rfl)
    (LB.pullGen D.toPre.P.L _ _ t (toUnit (TF (R := V) (FractionRing V))).left) (pullGen_isGen _ _ _ _ ht _)
  obtain ⟨w, hw, hwv⟩ := TorsionValue.exists_frm_scale w₁ hw₁ (inv_ne_zero hl)
  have hwt : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z l * (val w (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
    intro z J hJ
    rw [hwv z J hJ, hv₁ _ _ z J hJ, val_pull hJ, Category.id_comp, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq,
      GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, mul_inv_cancel₀ hl, map_one, _root_.one_mul]
  refine ⟨w, hw, ⟨t, ht, hwt⟩, ?_⟩
  intro k hk wk hwk hwkg s s' v hExp hVal
  obtain ⟨σ', hIso, n, c, σ, fs, hE, hσ, hs⟩ := hExp
  choose xs hxs using fun i => GlobalTheory.ExpansionValueZero.exists_coeff (A := V) U.LG.isLB (σ i) h.left
    (GeneratorPullback.powGen U.LG.L _ _ f k) (powGen_isGen _ _ _ _ hf k) (fun W _ q => by simp)
  have hxs' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) z J, Good U.LG.L z J →
      sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val :=
    fun i Z r z J hJ => (hxs i Z r z J hJ).trans (by rw [val_pow])
  choose a ha using fun i α => GlobalTheory.T.exists_integral_coefficient_section_coordinate_rig V D.toPre g t ht k α (fs i α)
  have hv := GlobalTheory.T.section_value_generic_point_integral_section V (maximalIdeal V) D A G U.toUnifPre w₀ x e h l f hExt hfv k s σ' hIso n c σ hσ xs hxs' v hVal
  have hwk' : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z (l ^ k) * (val wk (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ k).val := by
    intro z J hJ
    rw [hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hwt z J hJ, mul_pow,
      GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, map_pow]
  have hc := GlobalTheory.T.integral_combination_terms_rational_point_frame V D.toPre g g' hP t l hl k wk hwkg hwk' s' n c fs hs a ha
  have hI := admissibleBase_of_completeNormalLocalCharZero hV
  have key := EvalZero.sumF_comb hI (FractionRing V) Finset.univ (fun i => c i * (l ^ k)⁻¹) _ _ fun i =>
    EvalZero.sumF_map (maximalIdeal V) (FractionRing V) (a i) (xs i) fun e' =>
      GlobalTheory.T.section_value_integral_point_congruent_term_sum V (maximalIdeal V) D A G U.toUnifPre h g hF f t e' k (htl e') (σ i) (fs i) (hE i e') (xs i) (hxs' i)
        (a i) (ha i)
  have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl
  convert (preTransparency := .reducible) key using 1
  · funext α
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (a i α)) =
        (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (a i α) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      ← hc α, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
  · simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (xs i)) =
        (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (xs i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      ← hv, mul_comm v, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]

end GlobalTheory.Poinc.IntEval
