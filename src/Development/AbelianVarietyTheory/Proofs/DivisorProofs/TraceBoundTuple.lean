module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumLiftDatumSameHalfTranslateConjugatePlac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorEqUnitSmulCentralTranslatePlacePartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorThreeStepsConjugatePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVectorThreeStepDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlacesStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.BigOn.Exp.TupLe.Swap

theorem flat_gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧
    (princ B).vecFlat ψ = c • R.ωP i t (z⁻¹, 1) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid
  classical
  obtain ⟨eg, ea, et, fg, hA, heg, hea, het, hfg, hhA, hflat⟩ := GlobalTheory.T.flatVector_three_steps_conjugate_places D G Pl0 T0 A Ks R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid
  have hdisj : Disjoint (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) :=
    Finset.disjoint_filter_filter_not _ _ _
  have hun : keepPart (R := R) t (B.de.Q ∪ ψ.Q) ∪ flipPart (R := R) t (B.de.Q ∪ ψ.Q) = R.Q t :=
    Finset.filter_union_filter_not_eq _ _
  obtain ⟨gA, hgA, hvP⟩ := GlobalTheory.T.lift_vector_three_step_decomposition D G Pl0 T0 A Ks R F hC hQG i t hV _ _ hdisj hun eg ea et fg heg hea het hfg
  obtain ⟨zA, cA', hzA, hzA', hcA, hAeq⟩ := GlobalTheory.T.flatVector_eq_unit_smul_centralTranslate_placePart D G Pl0 T0 A Ks R F hC hQG i t hV _ (Finset.filter_subset _ _) eg ea fg heg hea hfg
  obtain ⟨zT, cT, -, hzT', hcT, hT⟩ := GlobalTheory.T.flatDatum_liftDatum_same_half_translate_conjugatePlaces D G Pl0 T0 A Ks R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid eg ea et fg hA heg hea het hfg hhA
  have e1 : hA = cA' • R.ωP i t (zA⁻¹, 1) gA := hAeq hA gA hhA hgA
  have hm := GlobalTheory.T.theta_half_moves_under_translate_other_places D G Pl0 T0 A Ks R F hC hQG i t hV _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj eg ea et fg gA _ _ zA cA'
    heg hea het hfg hgA hzA hcA.1 hvP
  rw [← e1] at hm
  have e2 := hT _ _ hflat hm
  refine ⟨zA * zT, cT * cA', suppAt_mul' hzA' hzT', GlobalTheory.BigOn.Exp.TupLe.unitOff_mul hcT hcA, ?_⟩
  rw [e2, map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_rev]

end GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.BigOn.Exp.TupLe


end GlobalTheory.BigOn.Exp.TupLe

end
