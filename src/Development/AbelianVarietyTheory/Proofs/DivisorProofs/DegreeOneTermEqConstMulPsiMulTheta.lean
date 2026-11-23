module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneFamilyTermEqPsiThetaValueCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementThetaTermIntegralPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorOfPsiCoordinateStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfIsUnitConstantClosedPointLocalRingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationConstantNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
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

namespace GlobalTheory.Poinc.IntTerm

theorem term_eq_const_psi_theta : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ : FractionRing V, ∀ (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → w.IsGen → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ a : V, l * coef s g' w mu = κ * algebraMap V (FractionRing V) (r * a) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit a) := by
  intro V _ _ _ D θ hθ s
  obtain ⟨c₀, hc₀, hc⟩ := GlobalTheory.T.psi_zero_mul_rigidification_constant_ne_zero V D
  obtain ⟨κ₀, hκ⟩ := GlobalTheory.T.degreeOneFamily_term_eq_psi_thetaValue_character V D θ hθ s
  refine ⟨κ₀ / c₀, fun g g' w l hpull hw hint mu r hr => ?_⟩
  obtain ⟨gam, hgam, vgam⟩ := GlobalTheory.T.exists_integralGenerator_of_psiCoordinate V D mu r hr
  obtain ⟨a, ha, hu⟩ := GlobalTheory.T.exists_base_element_theta_term_integralPoint V D θ g g' w l hpull hint mu gam hgam
  refine ⟨a, ?_, fun h => GlobalTheory.T.isUnit_of_isUnit_constant_closedPoint_localRing V a (hu h)⟩
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB z
  have e₁ := hκ g' w hw mu z J hJ
  have e₂ := hc z J hJ
  have e₃ := vgam z J hJ
  have e₄ := ha z J hJ
  rw [_root_.mul_assoc (GlobalTheory.UT.cst _ z _), mul_comm (rigV D _ z J).val, e₂, e₃] at e₁
  have e₅ : GlobalTheory.UT.cst (FractionRing V) z (l * coef s g' w mu * c₀) =
      GlobalTheory.UT.cst (FractionRing V) z (κ₀ * (algebraMap V (FractionRing V) r * algebraMap V (FractionRing V) a)) := by
    simp only [CoefBasic.cst_eq, map_mul] at e₁ e₄ ⊢
    rw [← e₄]
    linear_combination CoefBasic.cstH z l * e₁
  have e₆ := CoefBasic.cstH_inj z ((CoefBasic.cst_eq _ _).symm.trans (e₅.trans (CoefBasic.cst_eq _ _)))
  rw [map_mul]
  field_simp
  linear_combination e₆

end GlobalTheory.Poinc.IntTerm
