module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIsoRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.RingTheory.Localization.Integer
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemRegularTraitsGivenChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareApproxValuesAtPointOfElementsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefMapIntOfPos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionThetaValuesAbelianPartDefinedOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpTorsionDefOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomial, Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomialStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearForm, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotientsStatement, Development.AbelianVarietyTheory.Definitions.Divisors.IsMonomialTauOfTauIn, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoords, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoordsStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPartOfBasisOfInjective, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfCoeffNeZero, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConePullOfSurjective, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreField, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreFieldStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomial =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomial", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIsoRel\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpTorsionDefOver\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull\nimport Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.Coef

section Core

open GlobalTheory.UT GlobalTheory.UT.SymFrame ReciprocityTheory.ChartRestriction.G.DVR

variable {V₁ W₀ K : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] [Field K] [IsAlgClosed K] {D : DegPre V₁}
  {B₀ : Over (Sp W₀)} [GrpObj B₀] {f : W₀ →+* V₁} {q : Fin 8 → (D.P.A.left ⟶ B₀.left)} {ev : V₁ →+* K} {k₀ : Subfield K}
  {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (D.P.A.left ⟶ X₂)} {e : I → ℤ}
  {u : LB.Iso D.P.L (LB.LinComb L₂ π e)}

theorem step [IsLocalRing V₁] [IsNoetherianRing V₁] [IsIntegrallyClosed V₁] (H : Desc f q ev k₀ u) {N : ℕ} (hN : 1 ≤ N)
    (htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → RatP q k₀ x.left)
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (g : GtPtF D (FractionRing V₁)) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) (w : Frm D (FractionRing V₁) 1 g.b)
    (hw : w.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1) (χ : D.X)
    (hχ : RatP q k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c χ).left)
    (t₃ : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (h₃ : t₃.IsGen)
    (m₃ : ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀,
      ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ D.c χ).left)⁻¹ *
        val (Z := Sp K) t₃ (toUnit (Over.mk (spMap ev))).left z J).val = toStk z c) :
    ∃ R : V₁, (∀ z J, Good D.P.L z J → sval θ (cP D _ χ * g.b).left z J * (val (g.s χ) (𝟙 _) z J).val *
        (val w (𝟙 _) z J).val * (val t₃ (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val =
          cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) R)) ∧
      ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀, c ≠ 0 ∧ toStk z (ev R) = toStk z c *
        ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ (D.c χ * b)).left).val *
          sval (Z := Sp K) θ (toUnit (Over.mk (spMap ev)) ≫ (D.c χ * b)).left z J) := by
  obtain ⟨t₁, h₁⟩ := exists_gen_of_local D.P.L D.P.isLB
    ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε
  obtain ⟨t₂, h₂⟩ := exists_gen_of_local D.P.L D.P.isLB ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)
  obtain ⟨a₁, g₁, m₁⟩ := char_mem H hN htor g b hgb ho χ hχ t₁ h₁
  obtain ⟨a₂, g₂, m₂⟩ := frame_mem H hN htor g b hgb ho w hw t₂ h₂
  obtain ⟨G, hG, vG⟩ := (((grep_gen (Y := 𝟙_ (Over (Sp V₁))) t₁ h₁ (𝟙 _)).mul (grep_gen t₂ h₂ (𝟙 _))).mul
    (grep_gen t₃ h₃ (𝟙 _))).inv.out D.P.isLB (fun k => (D.c χ * b).left ≫ D.famφB 0 k) (DegPre.famε 1) (fun U _ h => by
      rw [prod_gt (Z := Sp K), prod_ln, prod_famφB_zero, Fintype.prod_unique, Category.id_comp, zpow_neg_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  obtain ⟨x, hx⟩ := GlobalTheory.TwistUnit.exists_ratio_local D.P.isLB (H1.SectionArithmetic.pullSec θ (D.c χ * b).left) G hG
  have key : ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
      sval θ (toUnit T ≫ (D.c χ * b)).left z J * (val t₁ (toUnit T).left z J * val t₂ (toUnit T).left z J *
        val t₃ (toUnit T).left z J).val = gs (toUnit T).left z ⊤ x := fun T z J hJ => by
    have e₁ := (H1.SectionArithmetic.sval_pullSec θ (D.c χ * b).left (toUnit T).left z hJ).symm.trans (hx _ (toUnit T).left z J hJ)
    have e₂ := vG T (toUnit T) z J hJ
    simp only [Category.comp_id] at e₂
    refine (congrArg (· * _) (e₁.trans (congrArg (fun t => _ * Units.val t) e₂))).trans ?_
    rw [_root_.mul_assoc]
    erw [Units.inv_mul, _root_.mul_one]
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom x * a₁ * a₂, fun z J hJ => ?_, fun z J J₂ hJ hJ₂ => ?_⟩
  · have e₁ := (key _ z J hJ).trans (gs_gen x z)
    have e₂ : cP D _ χ * g.b = toUnit (TF (R := V₁) (FractionRing V₁)) ≫ (D.c χ * b) := by
      rw [hgb, MonObj.comp_mul]; rfl
    rw [e₂, g₁ z J hJ, g₂ z J hJ]
    simp only [CoefBasic.cst_eq, map_mul, Units.val_mul] at e₁ ⊢
    rw [← e₁]
    ring
  · have e₁ := (key (Over.mk (spMap ev)) z J hJ).trans (gs_ev ev x z)
    obtain ⟨c₁, hc₁, n₁⟩ := m₁ z J J₂ hJ hJ₂
    obtain ⟨c₂, hc₂, n₂⟩ := m₂ z J J₂ hJ hJ₂
    obtain ⟨c₃, hc₃, n₃⟩ := m₃ z J J₂ hJ hJ₂
    have ne : ∀ {c : K} {s : (Sp K).presheaf.stalk z}, IsUnit s → s = toStk z c → c ≠ 0 := by
      rintro c s hs e rfl
      rw [e, map_zero] at hs
      exact not_isUnit_zero hs
    refine ⟨c₁ * c₂ * c₃, k₀.mul_mem (k₀.mul_mem hc₁ hc₂) hc₃, mul_ne_zero (mul_ne_zero
      (ne (((a₁.isUnit.map ev).map _).mul (Units.isUnit _)) n₁) (ne (((a₂.isUnit.map ev).map _).mul (Units.isUnit _)) n₂))
      (ne (Units.isUnit _) n₃), ?_⟩
    have alg : ∀ {S : Type} [CommRing S] (p c b o v₁ v₂ v₃ : Sˣ) (s a₁ a₂ : S),
        s * (v₁ * v₂ * v₃).val * a₁ * a₂ = a₁ * (p⁻¹ * c * b * o⁻¹ * v₁).val * (a₂ * (o * b⁻¹ * v₂).val) *
          (c⁻¹ * v₃).val * (p.val * s) := by
      intro S _ p c b o v₁ v₂ v₃ s a₁ a₂
      have : v₁ * v₂ * v₃ = (p⁻¹ * c * b * o⁻¹ * v₁) * (o * b⁻¹ * v₂) * (c⁻¹ * v₃) * p := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [this]
      generalize p⁻¹ * c * b * o⁻¹ * v₁ = A
      generalize o * b⁻¹ * v₂ = B
      generalize c⁻¹ * v₃ = C
      simp only [Units.val_mul]
      ring
    simp only [map_mul]
    rw [← n₁, ← n₂, ← n₃, ← e₁]
    exact alg _ _ _ _ _ _ _ _ _ _

theorem core [IsLocalRing V₁] (hV : IsCN V₁) (H : Desc f q ev k₀ u) {N : ℕ} (hN : 2 ≤ N) (hNK : (N : K) ≠ 0)
    (htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → RatP q k₀ x.left)
    {X C : Type} [AddCommGroup X] (eX : X ≃+ D.X) (T : X → C → V₁) (hT : IsThetaTerms D N eX T)
    (hc : ∀ mu, RatP q k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c (eX mu)).left) (y : X → FractionRing V₁) (hy : y 0 = 1)
    (hψ : ∀ mu, ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c (eX mu)).left) (fun _ => -1)), t.IsGen ∧
      (∀ (z : (TF (R := V₁) (FractionRing V₁)).left) J, Good D.P.L z J →
        (val (D.psi (eX mu)) (jFK (R := V₁) (FractionRing V₁)) z J).val =
          (val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val * cst (FractionRing V₁) z (y mu)) ∧
      ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀,
        ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ D.c (eX mu)).left)⁻¹ *
          val (Z := Sp K) t (toUnit (Over.mk (spMap ev))).left z J).val = toStk z c) (mu : X) (c : C) :
    ∃ R R₀ : V₁, algebraMap V₁ (FractionRing V₁) (T mu c * R₀) = algebraMap V₁ (FractionRing V₁) R * y mu ∧
      ev R₀ ≠ 0 ∧ ∃ r ∈ k₀, ev R = r * ev R₀ := by
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, c₀, h₆⟩ := hT
  obtain ⟨θ, hθ, hnz, hlam, -, -⟩ := ThetaOne.main hV D
  obtain ⟨lam, hlam, -⟩ := hlam (FractionRing V₁) th
  choose t ht gt mt using hψ
  choose R gR mR using fun mu c => step H (by omega) htor θ (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c) (eX mu) (hc mu) (t mu)
    (ht mu) (mt mu)
  obtain ⟨κ, hκ, hθκ⟩ := theta_mem H θ (hθ K ev)
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB z
  have gen : ∀ mu c, CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (T mu c)) *
      (rigV D (TF (R := V₁) (FractionRing V₁)).hom z J).val =
      cst (FractionRing V₁) z lam * (@id ((TF (R := V₁) (FractionRing V₁)).left.presheaf.stalk z)ˣ
        (val (D.psi 0) (jFK (R := V₁) (FractionRing V₁)) z J))⁻¹.val *
        CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (R mu c) * y mu) := fun mu c => by
    have e₁ := h₅ mu c z J hJ
    rw [pow_one, term_val D _ th θ lam hlam _ _ z J hJ, Units.val_mul] at e₁
    have e₂ : (@id ((TF (R := V₁) (FractionRing V₁)).left.presheaf.stalk z)ˣ
      (val (D.psi (eX mu)) (jFK (R := V₁) (FractionRing V₁)) z J)).val = _ := gt mu z J hJ
    rw [map_mul, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, e₁, e₂, ← gR mu c z J hJ]
    ring
  have rel : ∀ mu c, algebraMap V₁ (FractionRing V₁) (T mu c * R 0 c₀) =
      algebraMap V₁ (FractionRing V₁) (R mu c) * y mu := fun mu c => by
    have e₀ := gen 0 c₀
    rw [h₆, hy, map_one, map_one, _root_.one_mul, _root_.mul_one] at e₀
    have e₁ := gen mu c
    refine CoefBasic.cstH_inj z ((rigV D (TF (R := V₁) (FractionRing V₁)).hom z J).isUnit.mul_right_cancel ?_)
    rw [map_mul, map_mul]
    linear_combination CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (R 0 c₀)) * e₁ -
      CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (R mu c) * y mu) * e₀
  let zK : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  obtain ⟨JK, hJK⟩ := CoefBasic.exists_good' D.P.isLB zK
  obtain ⟨J₂, hJ₂⟩ := CoefBasic.exists_good' H.hL₂ zK
  have inK : ∀ mu c, ∃ r ∈ k₀, ev (R mu c) = κ * r := fun mu c => by
    obtain ⟨r, hr, -, e₁⟩ := mR mu c zK JK J₂ hJK hJ₂
    obtain ⟨r', hr', e₂⟩ := hθκ (toUnit _ ≫ (D.c (eX mu) * b c)) (by
      rw [MonObj.comp_mul]
      refine ratP_mul H.hP H.hk (hc mu) (htor _ ?_)
      rw [← MonObj.comp_pow, (Frames.torsion_of_nsmul (g c) (b c) (h₁ c) (h₂ c)).2, MonObj.comp_one]) zK JK J₂ hJK hJ₂
    rw [e₂, ← map_mul] at e₁
    exact ⟨r * r', k₀.mul_mem hr hr', ((toStk zK).injective e₁).trans (mul_left_comm _ _ _)⟩
  have ne : ev (R 0 c₀) ≠ 0 := fun h0 => by
    obtain ⟨p, hp, hne⟩ := exists_torsion_ne D ev θ (hnz K ev) N hN hNK
    obtain ⟨c₁, rfl⟩ := h₃ K (spMap ev) p hp
    obtain ⟨r, -, hr, e₁⟩ := mR 0 c₁ zK JK J₂ hJK hJ₂
    have e₂ := rel 0 c₁
    rw [hy, _root_.mul_one] at e₂
    rw [← IsFractionRing.injective V₁ (FractionRing V₁) e₂, map_mul, h0, mul_zero, map_zero, map_zero eX, _root_.GlobalTheory.IndivisibleSection.c_zero_eq_one,
      _root_.one_mul] at e₁
    have u₁ : IsUnit (toStk zK r) := (IsUnit.mk0 r hr).map _
    exact hne zK JK hJK ((Units.mul_right_eq_zero _).1 (u₁.mul_right_eq_zero.1 e₁.symm))
  obtain ⟨r, hr, e₁⟩ := inK mu c
  obtain ⟨r₀, hr₀, e₀⟩ := inK 0 c₀
  have h0 : r₀ ≠ 0 := by
    rintro rfl
    exact ne (e₀.trans (mul_zero _))
  refine ⟨R mu c, R 0 c₀, rel mu c, ne, r / r₀, k₀.div_mem hr hr₀, ?_⟩
  rw [e₁, e₀]
  field_simp

end Core

section Main

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_split {V₁ : Type} [CommRing V₁] [IsDomain V₁] {m N : ℕ} (s : Fin m ⊕ Fin N → V₁) (n : Fin m ⊕ Fin N → ℤ)
    (σ : Fin N → V₁ˣ) (hσ : ∀ k, (σ k : V₁) = s (.inr k)) (hn : ∀ k, 0 ≤ n (.inl k)) :
    ∏ i : Fin (m + N), algebraMap V₁ (FractionRing V₁) (s (finSumFinEquiv.symm i)) ^ n (finSumFinEquiv.symm i) =
      algebraMap V₁ (FractionRing V₁) ((∏ k, s (.inl k) ^ (n (.inl k)).toNat) * (∏ k, σ k ^ n (.inr k)).val) := by
  rw [Equiv.prod_comp finSumFinEquiv.symm (fun i => algebraMap V₁ (FractionRing V₁) (s i) ^ n i), Fintype.prod_sum_type,
    map_mul, map_prod, Units.coe_prod, map_prod]
  congr 1
  · exact Finset.prod_congr rfl fun k _ => by rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hn k)]
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hσ]
    exact ((congrArg Units.val (map_zpow (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom) (σ k) _)).trans
      (Units.val_zpow_eq_zpow_val _ _)).symm

theorem coef_monomial : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → (∀ k mu, 0 ≤ qW W (ε (.inl k)) mu) → TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => ε (.inl k)) mu) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), FromBase Q τ₀ ib → (∀ a, ev (ρ (ib a)) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) = r * ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
  intro g l hl _ W _
  refine ⟨1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hV hlu Q _ ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ τ₀ m N s ε hs hε hτ hmono W₀ _ ib hB hk mu c
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨pr, w, hpr, huniv, hw, hc, B₀, iG, iC, M₀, c₀, τ₁, β, β₂, w₀, -, hM₀, hβ, hsq, hw₀, hβc, hτ₁, -, hψ⟩ :=
    PsiMono.psi_val_of W Q ρ hρ D e hS τ₀ _ _ hτ ib hB
  obtain ⟨Ω, hΩ, vΩ⟩ := exists_omega W ρ Q D pr B₀ β₂ w hw M₀ hM₀ w₀ hw₀
  have hN : 2 ≤ (l ^ j) ^ 2 := hl.two_le.trans ((Nat.le_self_pow (by omega) l).trans (Nat.le_self_pow (by omega) _))
  have hNu : IsUnit (((l ^ j) ^ 2 : ℕ) : V₁) := by push_cast; exact (hlu.pow _).pow _
  have htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ ((l ^ j) ^ 2) = 1 →
      RatP (fun a => (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) k₀ x.left := fun x hx a =>
    sharp_torsion_defOver ρ ib Q D pr hpr huniv B₀ β hβ K ev k₀ hk₀ hk _ (by omega) hNu x hx a
  have h2 : spMap (ρ.comp ib) = spMap ρ ≫ spMap ib := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have H : Desc (ρ.comp ib) (fun a => (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) ev k₀ Ω :=
    ⟨hk₀, fun T g hg => exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ T.hom g (h2 ▸ hg), hk, hM₀, hΩ,
      piB_congr ρ Q D pr B₀ β₂ hsq, htor 1 (one_pow _)⟩
  obtain ⟨R, R₀, e₁, hne, r, hr, e₂⟩ := core hV H hN (by simpa using (hNu.map ev).ne_zero) htor e _ hT
    (fun mu a => sharp_c_defOver ρ ib Q D e pr hc B₀ β c₀ hβc K ev k₀ hk mu a)
    (fun mu => ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s (finSumFinEquiv.symm i))) ^ qW W (ε (finSumFinEquiv.symm i)) mu)
    (by simp [qW]) (fun mu => by
      obtain ⟨t, ht, vt⟩ := exists_psi_gen W ρ Q D pr B₀ β₂ hM₀ hsq Ω hΩ (spMap ρ ≫ spMap ib) (D.c (e mu))
        (fun a => c₀ (mu a)) (fun a => by
          have := congrArg (· ≫ β) (hc mu a)
          simp only [Category.assoc, Over.comp_left, hβc] at this ⊢
          exact this) (fun a b => τ₁ (mu a) (mu b)) (fun a b => hτ₁ _ _)
      refine ⟨t, ht, fun z J hJ => ?_, fun z J J₂ hJ hJ₂ => ?_⟩
      · obtain ⟨JQ, hJQ⟩ := CoefBasic.exists_good' Q.M.isLB z
        obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' hM₀ z
        obtain ⟨y, hy, ey⟩ := hψ mu z JQ J J₀ hJQ hJ hJ₀
        have j1 : jFK (R := V₁) (FractionRing V₁) = 𝟙 _ := Spec.map_id _
        have t1 : (toUnit (TF (R := V₁) (FractionRing V₁))).left = (toUnit (TK V₁)).left := by
          show jFK (R := V₁) (FractionRing V₁) ≫ jK V₁ = jK V₁
          rw [j1]; exact Category.id_comp _
        have et := vt (TK V₁) z J J₀ hJ hJ₀
        rw [vΩ _ _ z J JQ J₀ hJ hJQ hJ₀] at et
        have pe : ∀ a b, (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ sharpPair ρ Q D pr a b =
            (lift (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu b))).left := by
          have k : ∀ a, (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
              (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)).left := fun a => by
            show (jK V₁ ≫ (D.c (e mu)).left) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
              (PsiMono.fracPt ρ hρ ≫ jK V) ≫ (Q.c (mu a)).left
            rw [PsiMono.fracPt_comp]
            exact (Category.assoc _ _ _).trans ((congrArg (jK V₁ ≫ ·) (hc mu a)).trans (Category.assoc _ _ _).symm)
          intro a b
          have hP := isGrpPullback_pullback Q.B (spMap ρ)
          apply pullback.hom_ext
          · refine Eq.trans ?_ ((k a).trans (congrArg (fun m => m.left) (lift_fst
              (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu b)))).symm)
            exact (Category.assoc _ _ _).trans (congrArg (fun m => (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ m.left)
              (lift_fst (pushPt hP.1.w (pr a)) (pushPt hP.1.w (pr b))))
          · refine Eq.trans ?_ ((k b).trans (congrArg (fun m => m.left) (lift_snd
              (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu b)))).symm)
            exact (Category.assoc _ _ _).trans (congrArg (fun m => (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ m.left)
              (lift_snd (pushPt hP.1.w (pr a)) (pushPt hP.1.w (pr b))))
        have ge : (TK V₁).hom ≫ spMap ρ ≫ spMap ib = (PsiMono.fracPt ρ hρ ≫ jK V) ≫ spMap ib := by
          rw [PsiMono.fracPt_comp]; exact (Category.assoc _ _ _).symm
        simp only [pe, ge] at et
        simp only [mul_zpow, Finset.prod_mul_distrib] at ey
        rw [j1, t1, ← hy]
        refine (congrArg Units.val (ey.trans (congrArg (· * _) ((_root_.mul_assoc _ _ _).symm.trans et.symm)))).trans ?_
        exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) rfl (gs_unit _ _ ⊤ trivial _).symm)
      · have et := vt (Over.mk (spMap ev)) z J J₂ hJ hJ₂
        obtain ⟨x, hx, ex⟩ := prod_mem (k₀ := k₀) (z := z) Finset.univ (fun a => prod_mem Finset.univ fun b =>
          zpow_mem (val_spMap_mem k₀ (τ₁ (mu a) (mu b)) ((ev.comp ρ).comp ib) hk z hJ₂) (W a b))
        refine ⟨x, hx, Eq.trans (congrArg Units.val ?_) ex⟩
        rw [← spMap_three]
        exact inv_mul_eq_iff_eq_mul.2 et) mu c
  refine ⟨r, hr, ?_⟩
  have e₃ := prod_split (fun i => ρ (s i)) (fun i => qW W (ε i) mu) (fun k => ((hs k).map ρ).unit) (fun _ => rfl)
    (fun k => hε k mu)
  rw [e₃, ← map_mul] at e₁
  have e₄ := IsFractionRing.injective V₁ (FractionRing V₁) e₁
  have e₅ : ∏ k, ρ (s (.inl k)) ^ (qW W (ε (.inl k)) mu).toNat = mo mu := (hmono mu).symm
  rw [e₅] at e₄
  have e₆ : u mu c * R₀ = R * (∏ k, ((hs k).map ρ).unit ^ qW W (ε (.inr k)) mu).val :=
    mul_left_cancel₀ (hmo mu).1 (by linear_combination e₄)
  have e₇ : ev (∏ k, ((hs k).map ρ).unit ^ qW W (ε (.inr k)) mu).val =
      ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => (congrArg Units.val (map_zpow (Units.map ev.toMonoidHom) _ _)).trans
      (Units.val_zpow_eq_zpow_val _ _)
  have e₈ := congrArg ev e₆
  rw [map_mul, map_mul, e₇, e₂] at e₈
  exact mul_right_cancel₀ hne (by linear_combination e₈)

end Main

end GlobalTheory.Poinc.Sep.Coef
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomial =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomialStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomialStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomial\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eighthPower_thetaCoefficient_eq_const_mul_monomial : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → (∀ k mu, 0 ≤ qW W (ε (.inl k)) mu) → TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => ε (.inl k)) mu) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), FromBase Q τ₀ ib → (∀ a, ev (ρ (ib a)) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) = r * ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
  first | exact @GlobalTheory.Poinc.Sep.Coef.coef_monomial
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomialStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearForm =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearForm", "h": "module\n\npublic import Mathlib.LinearAlgebra.FreeModule.Basic\npublic import Mathlib.RingTheory.Finiteness.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Algebra.Category.Grp.Injective\npublic import Mathlib.RingTheory.Localization.Integer\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory

theorem exists_pos_mul_extend_int_linearForm (F : Type) [AddCommGroup F] [Module.Free ℤ F]
    [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ) :
    ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  classical
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property P.subtype
    P.injective_subtype ((Algebra.linearMap ℤ ℚ).comp f)
  let b := Module.Free.chooseBasis ℤ F
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => g (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose n hn using hint
  let lam : F →ₗ[ℤ] ℤ := b.constr ℤ n
  have key : (Algebra.linearMap ℤ ℚ).comp lam = d • g := by
    refine b.ext fun i => ?_
    simpa [lam] using hn i
  refine ⟨d * d, mul_self_pos.mpr hd0, d • lam, fun x => ?_⟩
  have h1 := LinearMap.congr_fun key x
  have h2 := LinearMap.congr_fun hg x
  simp at h1 h2
  rw [h2] at h1
  have h3 : lam x = d * f x := by exact_mod_cast h1
  simp [h3, mul_assoc]

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearForm =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotientsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotientsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotients\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_stalk_elements_approx_leadingTerm_quotients : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ (φ : InvFun ℤ) (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i → IsPolFan id g φ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ (ga : Fin m → LinearMap.BilinForm ℤ Q.X) (M : ℕ), 1 ≤ M → IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ ξ : Sp V ⟶ S, UnifOver F j ξ Q → ∀ (N₁ : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W N₁ (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), HasTraitsR X₁ z₁ Φ.pre → IsChartMember X₁ z₁ Φ Q (ξ ≫ π) t δ y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) → ∀ ga' : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga' k a b = ga (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ Elements Φ y φ d ga' ev₁ k₀ := by
  first | exact @GlobalTheory.CoverElements.exists_elements
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotientsStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Divisors.IsMonomialTauOfTauIn =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Divisors.IsMonomialTauOfTauIn", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Model

variable {V : Type} [CommRing V] [IsDomain V]

theorem isMonomialTau_of_tauIn {Q : Data V} {τ₀ : Gens Q} {N : ℕ} {s : Fin N → V}
    {ε : Fin N → LinearMap.BilinForm ℤ Q.X} (h : TauIn Q τ₀ s ε) : Q.IsMonomialTau s ε := by
  intro a b
  obtain ⟨hg, k, hk, hv⟩ := h a b
  exact ⟨k, hk, Exists.intro (τ₀ a b) ⟨hg, hv⟩⟩

end GlobalTheory.Poinc.Sep.Model
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Divisors.IsMonomialTauOfTauIn =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoords =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoords", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsMonomialTauOfTauIn\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem isMonomialTau_inl_of_tauIn : ∀ (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : GlobalTheory.Poinc.Sep.Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.Poinc.Sep.TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) := by
  intro V _ _ Q τ₀ m N s ε hs h a b
  obtain ⟨k, hk, hc⟩ := Model.isMonomialTau_of_tauIn h a b
  let alg : V →* FractionRing V := (algebraMap V (FractionRing V) : V →* FractionRing V)
  let w : Vˣ := ∏ j : Fin N, (hs j).unit ^ ε (.inr j) a b
  refine ⟨k * Units.map alg w⁻¹, ?_, GlobalTheory.PolDeg.Taut.tauCoord_mul_unit hc w⁻¹⟩
  have hprod : (k : FractionRing V) = (∏ i : Fin m, algebraMap V (FractionRing V) (s (.inl i)) ^ ε (.inl i) a b) *
      ∏ j : Fin N, algebraMap V (FractionRing V) (s (.inr j)) ^ ε (.inr j) a b := by
    rw [hk, ← Fintype.prod_sum_type (fun x => algebraMap V (FractionRing V) (s x) ^ ε x a b)]
    exact Fintype.prod_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)
  have hw : ((Units.map alg w : (FractionRing V)ˣ) : FractionRing V) =
      ∏ j : Fin N, algebraMap V (FractionRing V) (s (.inr j)) ^ ε (.inr j) a b := by
    simp [w, alg, Units.coe_prod]
  rw [Units.val_mul, map_inv, Units.val_inv_eq_inv_val, hw, hprod, mul_inv_cancel_right₀]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _
    ((IsFractionRing.injective V (FractionRing V)).ne_iff' (map_zero _) |>.2 (hs j).ne_zero)

end GlobalTheory.Poinc.Sep
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoords =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoordsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoordsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoords\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isMonomialTau_first_coords_of_unit_last_coords : ∀ (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : GlobalTheory.Poinc.Sep.Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.Poinc.Sep.TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) := by
  first | exact @GlobalTheory.Poinc.Sep.isMonomialTau_inl_of_tauIn
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoordsStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPartOfBasisOfInjective =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPartOfBasisOfInjective", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\n\n"}
section -- clump:auto
@[expose] public section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isPartOfBasis_of_injective {L L' : Type} [AddCommGroup L] [AddCommGroup L'] {m : ℕ} (f : L →ₗ[ℤ] L')
    (hf : Function.Injective f) {v : Fin m → L} (h : IsPartOfBasis fun i => f (v i)) : IsPartOfBasis v := by
  classical
  obtain ⟨ψ, hψ⟩ := h.exists_dual
  obtain ⟨n', b, -⟩ := h
  let π : L →ₗ[ℤ] (Fin m → ℤ) := LinearMap.pi fun i => ψ i ∘ₗ f
  let s : (Fin m → ℤ) →ₗ[ℤ] L := ∑ i, (LinearMap.proj i : (Fin m → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)
  have hs : ∀ c, s c = ∑ i, c i • v i := fun c => by simp [s, LinearMap.sum_apply]
  have hπ : ∀ c, π (s c) = c := fun c => by
    ext j

    simp [π, hs, map_sum, hψ]
  let K := LinearMap.ker π
  obtain ⟨n, bK'⟩ := Submodule.basisOfPid b (K.map f)
  let bK := bK'.map (Submodule.equivMapOfInjective f hf K).symm
  have hinj : Function.Injective (s.coprod K.subtype) := by
    refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨c, k⟩ h0
    have h1 : s c + (k : L) = 0 := by simpa using h0
    have h2 : π (k : L) = 0 := k.2
    have h3 : c = 0 := by simpa [h2, hπ] using congrArg π h1
    subst h3
    have h4 : (k : L) = 0 := by simpa using h1
    exact Prod.ext rfl (Subtype.ext h4)
  have hsurj : Function.Surjective (s.coprod K.subtype) := fun x =>
    ⟨(π x, ⟨x - s (π x), by simp [K, LinearMap.mem_ker, hπ]⟩), by simp⟩
  let E : ((Fin m → ℤ) × K) ≃ₗ[ℤ] L := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨n, ((Pi.basisFun ℤ (Fin m)).prod bK).map E, fun i => ?_⟩
  have h1 : E (Pi.single i 1, 0) = v i := by
    change (s.coprod K.subtype) (Pi.single i 1, 0) = v i
    simp [hs, Pi.single_apply]
  simpa using h1

theorem isCone_of_pull : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X X₁ : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X₁), Function.Surjective r → IsCone bar φ (fun i => pull r (γ i)) →
    IsCone bar φ γ := by
  intro O _ bar φ X X₁ _ _ _ _ _ _ r m γ hr h
  have hmem : ∀ i, γ i ∈ balForms bar X₁ := fun i => by
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      exact (h.mem i).1 y z
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      simpa only [pull_apply, map_smul] using (h.mem i).2 a y z
  have hinj : Function.Injective (pullBal bar r) := fun β β' e =>
    Subtype.ext (LinearMap.ext₂ fun a b => by
      obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      exact LinearMap.congr_fun₂ (congrArg Subtype.val e) a b)
  refine ⟨hmem, fun i y => ?_, isPartOfBasis_of_injective (pullBal bar r) hinj h.basis,
    (linearOn_pull_iff hr).1 h.linear, IsStrict.of_pull hr h.strict⟩
  obtain ⟨y, rfl⟩ := hr y
  exact h.nonneg i y

end GlobalTheory.PolFan
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPartOfBasisOfInjective =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfCoeffNeZero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfCoeffNeZero", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

namespace ConeMeet

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCone bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

theorem apply_sum_nsmul {L : Type} [AddCommGroup L] (F : L →ₗ[ℤ] ℤ) {p : ℕ} (n : Fin p → ℕ) (v : Fin p → L) :
    F (∑ j, n j • v j) = ∑ j, (n j : ℤ) * F (v j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_nsmul]

theorem ray {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    (hγ' : IsCone bar φ γ') {i : Fin m} {k : ℕ} {d : Fin m' → ℕ} (hk : 0 < k) (hkd : k • γ i = ∑ j, d j • γ' j)
    (hback : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • γ' j = ∑ l, e l • γ l) :
    ∃ j, γ i = γ' j := by
  classical
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf : ∀ a b, f a (g b) = if a = b then 1 else 0 := hf
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have H1 : k • g i = ∑ j, d j • g' j := Subtype.ext (by simpa [g, g', Submodule.coe_sum] using hkd)
  have H2 : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := hback j hj
    exact ⟨kj, e, hkj, Subtype.ext (by simpa [g, g', Submodule.coe_sum] using he)⟩

  have coord : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l ∧
      ∀ l, (kj : ℤ) * f l (g' j) = e l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := H2 j hj
    refine ⟨kj, e, hkj, he, fun l => ?_⟩
    have t := congrArg (f l) he
    rw [map_nsmul, apply_sum_nsmul] at t
    simpa [hf] using t
  have Z : ∀ l, l ≠ i → ∀ j, d j ≠ 0 → f l (g' j) = 0 := by
    intro l hl
    have s := congrArg (f l) H1
    rw [map_nsmul, apply_sum_nsmul, hf, if_neg hl, smul_zero] at s
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (d j : ℤ) * f l (g' j) := fun j _ => by
      by_cases hd : d j = 0
      · simp [hd]
      · obtain ⟨kj, e, hkj, -, he⟩ := coord j hd
        have : 0 ≤ (kj : ℤ) * f l (g' j) := (he l).symm ▸ Int.natCast_nonneg _
        exact mul_nonneg (Int.natCast_nonneg _) ((mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 this)
    intro j hd
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 s.symm j (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hd)
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : k • g i = 0 := by rw [H1]; simp [hc]
    have s := congrArg (f i) this
    rw [map_nsmul, hf, if_pos rfl, map_zero] at s
    simp at s
    omega
  obtain ⟨kj, e, hkj, he, hc⟩ := coord j hj
  have hel : ∀ l, l ≠ i → e l = 0 := fun l hl => by
    have := hc l
    rw [Z l hl j hj, mul_zero] at this
    exact_mod_cast this.symm
  have he' : kj • g' j = e i • g i := by
    rw [he, Finset.sum_eq_single i (fun l _ hl => by rw [hel l hl, zero_smul]) (by simp)]
  have t := congrArg (f' j) he'
  rw [map_nsmul, map_nsmul, hf', if_pos rfl] at t
  simp only [nsmul_eq_mul, mul_one] at t
  have hx := hc i
  have hx0 : 0 ≤ f i (g' j) := (mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 (hx ▸ Int.natCast_nonneg _)
  have hxy : f i (g' j) * f' j (g i) = 1 := by
    have : (kj : ℤ) * (f i (g' j) * f' j (g i)) = kj * 1 := by
      rw [← mul_assoc, hx, mul_one]; exact_mod_cast t.symm
    exact mul_left_cancel₀ (by exact_mod_cast hkj.ne') this
  have hx1 : f i (g' j) = 1 := Int.eq_one_of_mul_eq_one_right hx0 hxy
  have hei : e i = kj := by rw [hx1, mul_one] at hx; exact_mod_cast hx.symm
  rw [hei] at he'
  refine ⟨j, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ (congrArg Subtype.val he') a b
  simp [g, g'] at this
  rcases this with h | h
  · exact h.symm
  · omega

theorem mem_of_coeff_ne_zero {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X}
    (hγ : IsCone bar φ γ) (hγ' : IsCone bar φ γ') {c : Fin m → ℝ} {c' : Fin m' → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc' : ∀ j, 0 ≤ c' j) (hrel : ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j)) (i : Fin m) (hi : c i ≠ 0) :
    ∃ j, γ i = γ' j := by
  classical
  obtain ⟨k, d, hk, hkd⟩ := inCone hγ' hγ.mem hγ.nonneg hc hc' ((linearOn_iff φ γ).1 hγ.linear c hc) hrel i hi
  refine ray hγ hγ' hk hkd fun j hj => ?_
  refine inCone (a := fun j => (d j : ℝ)) (b := Pi.single i (k : ℝ)) hγ hγ'.mem hγ'.nonneg
    (fun j => Nat.cast_nonneg _) (fun l => by by_cases h : l = i <;> simp [h])
    ((linearOn_iff φ γ').1 hγ'.linear _ fun j => Nat.cast_nonneg _) ?_ j (by exact_mod_cast hj)
  refine LinearMap.ext₂ fun a b => ?_
  have := LinearMap.congr_fun₂ hkd a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, nsmul_eq_mul] at this ⊢
  simp only [Pi.single_apply, smul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul]
  exact_mod_cast this.symm

end ConeMeet


open ConeMeet in
theorem cone_meet : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m → ℝ) (c' : Fin m' → ℝ), IsCone bar φ γ → IsCone bar φ γ' → (∀ i, 0 ≤ c i) → (∀ j, 0 ≤ c' j) →
    ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j) → ∀ i, c i ≠ 0 → ∃ j, γ i = γ' j ∧ c i = c' j := by
  intro O _ bar φ X _ _ _ m m' γ γ' c c' hγ hγ' hc hc' hrel i hi
  classical
  obtain ⟨j, hj⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel i hi
  refine ⟨j, hj, ?_⟩
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have s := sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms bar X).subtype) Subtype.val_injective (f' j)
    (β := Sum.elim g g') (c := Sum.elim c (-c')) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Submodule.subtype_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib,
        g, g', hrel, add_neg_cancel])
  rw [Fintype.sum_sum_type] at s
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, hf', Int.cast_ite,
    Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at s
  have h1 : ∑ l, c l * (f' j (g l) : ℝ) = c i := by
    rw [Finset.sum_eq_single i]
    · have : g i = g' j := Subtype.ext hj
      rw [this, hf', if_pos rfl, Int.cast_one, mul_one]
    · intro l _ hl
      by_cases hcl : c l = 0
      · rw [hcl, zero_mul]
      · obtain ⟨p, hp⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel l hcl
        have : g l = g' p := Subtype.ext hp
        rw [this, hf', if_neg, Int.cast_zero, mul_zero]
        rintro rfl
        exact hl (hγ.injective (hp.trans hj.symm))
    · simp
  linarith

end GlobalTheory.PolFan
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfCoeffNeZero =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConePullOfSurjective =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConePullOfSurjective", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPartOfBasisOfInjective\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfCoeffNeZero\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem apply_eq_zero_of_diag {X : Type} [AddCommGroup X] {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hp : ∀ y, 0 ≤ β y y) {y : X} (hy : β y y = 0) (z : X) : β y z = 0 := by
  by_contra hb
  have hA := hp z
  have h := hp (z + (-(β z z + 1) * β y z) • y)
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hy, hs z y] at h
  have hb2 : 1 ≤ β y z * β y z := mul_self_pos.2 hb
  have h3 := mul_nonneg (by linarith : 0 ≤ β z z + 1) (sub_nonneg.2 hb2)
  nlinarith [h3]

theorem exists_pull_eq {O : Type} [CommRing O] {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hk : ∀ y, r y = 0 → ∀ z, β y z = 0) : ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = β := by
  have key1 : ∀ a a' b, r a = r a' → β a b = β a' b := fun a a' b h => by
    have := hk (a - a') (by rw [map_sub, h, sub_self]) b
    rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  have key : ∀ a a' b b', r a = r a' → r b = r b' → β a b = β a' b' := fun a a' b b' h h' => by
    rw [key1 a a' b h, hs a' b, key1 b b' a' h', hs]
  have hs' : ∀ a, r (Function.surjInv hr a) = a := Function.surjInv_eq hr
  refine ⟨LinearMap.mk₂ ℤ (fun a b => β (Function.surjInv hr a) (Function.surjInv hr b)) ?_ ?_ ?_ ?_,
    LinearMap.ext₂ fun a b => ?_⟩
  · intro a a' b
    rw [← LinearMap.add_apply, ← map_add (f := _)]
    exact key _ _ _ _ (by rw [map_add (f := _), hs', hs', hs']) rfl
  · intro n a b
    rw [← LinearMap.smul_apply, ← map_smul]
    exact key _ _ _ _ (by rw [map_zsmul r, hs', hs']) rfl
  · intro a b b'
    rw [← map_add (f := _)]
    exact key _ _ _ _ rfl (by rw [map_add (f := _), hs', hs', hs'])
  · intro n a b
    rw [← map_smul]
    exact key _ _ _ _ rfl (by rw [map_zsmul r, hs', hs'])
  · simpa using key _ _ _ _ (hs' (r a)) (hs' (r b))

theorem isCone_pull_of_surjective : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (φ : InvFun O) (X₁ : Type) [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₁), IsPolFanOn bar φ X → Function.Surjective r → IsCone bar φ γ → IsCone bar φ (fun i => pull r (γ i)) := by
  intro O _ _ _ _ bar X _ _ _ φ X₁ _ _ _ r m γ hF hr hγ
  classical
  have hx := GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X m (fun i => pull r (γ i)) (fun _ => 1) (fun i => pull_mem r (hγ.mem i))
    (fun i y => hγ.nonneg i _) (fun _ => zero_le_one)
  obtain ⟨m₂, σ, c, hσ, hc, hsum⟩ := hF.cover _ hx
  let J : Finset (Fin m₂) := Finset.univ.filter fun j => c j ≠ 0
  let t : Fin J.card ↪ Fin m₂ := (J.orderEmbOfFin rfl).toEmbedding
  have hpos : ∀ k, c (t k) ≠ 0 := fun k => (Finset.mem_filter.1 (J.orderEmbOfFin_mem rfl k)).2
  have hout : ∀ j, j ∉ Set.range t → c j = 0 := fun j hj => by
    by_contra h0
    refine hj ?_
    have : j ∈ Set.range (J.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩)
    exact this
  have hδ := hF.face _ _ σ t hσ
  have hsum' : ∑ i, (1 : ℝ) • toReal (pull r (γ i)) = ∑ k, c (t k) • toReal (σ (t k)) :=
    hsum.trans (Fintype.sum_of_injective t t.injective _ _ (fun j hj => by simp [hout j hj]) fun _ => rfl).symm
  have hvan : ∀ k y, r y = 0 → σ (t k) y y = 0 := fun k y hy => by
    have h1 := LinearMap.congr_fun₂ hsum' y y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, hy, map_zero, Int.cast_zero, smul_eq_mul, mul_zero, Finset.sum_const_zero] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hc (t k))
      (by exact_mod_cast hσ.nonneg (t k) y : (0 : ℝ) ≤ (σ (t k) y y : ℝ))).1 h1.symm k (Finset.mem_univ _)
    exact_mod_cast (mul_eq_zero.1 h2).resolve_left (hpos k)
  have hex : ∀ k, ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = σ (t k) := fun k =>
    exists_pull_eq hr (hσ.mem (t k)).1 fun y hy z =>
      apply_eq_zero_of_diag (hσ.mem (t k)).1 (hσ.nonneg (t k)) (hvan k y hy) z
  choose δ hδ' using hex
  have hδc : IsCone bar φ δ := GlobalTheory.PolFan.isCone_of_pull O bar φ X X₁ r _ δ hr (by simpa only [hδ'] using hδ)
  have hsum₁ : ∑ i, (1 : ℝ) • toReal (γ i) = ∑ k, c (t k) • toReal (δ k) := LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    have h1 := LinearMap.congr_fun₂ hsum' a b
    simp only [← hδ'] at h1
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply] using h1
  have hmeet := GlobalTheory.PolFan.cone_meet O bar φ X₁ m _ γ δ (fun _ => 1) (fun k => c (t k)) hγ hδc (fun _ => zero_le_one)
    (fun k => hc _) hsum₁
  choose j hj using fun i => hmeet i one_ne_zero
  have hinj : Function.Injective j := fun i i' h =>
    hγ.injective ((hj i).1.trans ((congrArg δ h).trans (hj i').1.symm))
  have hfin := hF.face _ _ _ ⟨j, hinj⟩ hδ
  have heq : (fun i => pull r (γ i)) = fun i => σ (t (j i)) := funext fun i => by rw [(hj i).1, hδ']
  rw [heq]
  exact hfin

end GlobalTheory.PolFan
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConePullOfSurjective =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreField =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreField", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomialStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModule\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemRegularTraitsGivenChartStatement\npublic import Mathlib.LinearAlgebra.FreeModule.Basic\npublic import Mathlib.RingTheory.Finiteness.Defs\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearForm\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotientsStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoordsStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareApproxValuesAtPointOfElementsStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefMapIntOfPos\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionThetaValuesAbelianPartDefinedOverStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConePullOfSurjective\nimport Mathlib.Algebra.Module.StablyFree.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.CoassocSimps\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.Poinc.Sep.Assembly

theorem monoTau_inl {V : Type} [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V)
    (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X) (hs : ∀ k, IsUnit (s (.inr k)))
    (h : TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k))) :
    Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) :=
  GlobalTheory.T.isMonomialTau_first_coords_of_unit_last_coords V Q τ₀ m N s ε hs h

theorem unifOver_comp {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S Z : Scheme.{0}} (j : F.X ⟶ S)
    (π : S ⟶ Z) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ S) (Q : Data V)
    (h : UnifOver F j ξ Q) : UnifOver F (j ≫ π) (ξ ≫ π) Q := by
  refine ⟨h.1, fun R' _ _ _ ρ hc hi hf D ε hR => ?_⟩
  obtain ⟨G', i1, i2, A, i3, y', α, α₂, h1, h2, h3, h4, h5⟩ := h.2 R' ρ hc hi hf D ε hR
  exact ⟨G', i1, i2, A, i3, y', α, α₂, h1, by rw [← Category.assoc, h2]; simp only [Category.assoc], h3, h4, h5⟩

theorem isUnit_natCast_of_cyc (n : ℕ) (hn : n ≠ 0) (V : Type) [CommRing V] (f : Sp V ⟶ Sp (cycAway n)) :
    IsUnit ((n : ℕ) : V) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simpa using (isUnit_natCast hn).map φ.hom

theorem exists_ext_functional (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F)
    (f : P →ₗ[ℤ] ℤ) : ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x :=
  _root_.GlobalTheory.exists_pos_mul_extend_int_linearForm F P f

theorem isCone_inst {φ : InvFun ℤ} {X : Type} [AddCommGroup X] (i1 i2 : Module ℤ X) [f1 : @Module.Finite ℤ X _ _ i1]
    [f2 : @Module.Finite ℤ X _ _ i2] {m : ℕ} (gm' : Fin m → @LinearMap.BilinForm ℤ _ X _ (AddCommGroup.toIntModule X))
    (h : @IsCone ℤ _ id φ X _ i1 f1 m gm') : @IsCone ℤ _ id φ X _ i2 f2 m gm' := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact h

theorem isCone_equiv {φ : InvFun ℤ} {X X₁ : Type} [AddCommGroup X] [Module.Finite ℤ X] [AddCommGroup X₁]
    [Module.Finite ℤ X₁] (hF : IsPolFanOn id φ X) {m m' : ℕ} (gm' : Fin m → LinearMap.BilinForm ℤ X₁)
    (hgm' : IsCone id φ gm') (e : X ≃ₗ[ℤ] X₁) (h : Fin m' ≃ Fin m) :
    IsCone id φ (fun k => LinearMap.BilinForm.congr e.symm (gm' (h k))) := by
  have h1 := isCone_pull_of_surjective ℤ id X φ X₁ e.toLinearMap m gm' hF e.surjective hgm'
  have h2 := hF.face m m' _ h.toEmbedding h1
  convert h2 using 2 with k
  ext a b
  simp [pull]

theorem prod_zpow_eq {K ιt : Type} [Field K] {x : K} (hx : x ≠ 0) (s : Finset ιt) (f : ιt → ℤ) :
    ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hx]

theorem mem_of_pow_mem {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) (x : K) (p : ℕ) (hp : 0 < p)
    (h : x ^ p ∈ k₀) : x ∈ k₀ := by
  haveI := hk
  have hint : IsIntegral k₀ x := by
    refine ⟨Polynomial.X ^ p - Polynomial.C ⟨x ^ p, h⟩, Polynomial.monic_X_pow_sub_C _ (by omega), ?_⟩
    simp [Polynomial.eval₂_sub]
    exact sub_eq_zero.2 rfl
  have h1 := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.1 (Polynomial.natDegree_eq_of_degree_eq_some h1)
  rw [← hc]
  exact c.2

theorem mem_of_ratio {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {X R C : Type} [AddCommGroup X]
    [CommRing R] (ev₁ : R →+* K) (u : (Fin 8 → X) → C → R) (W : Matrix (Fin 8) (Fin 8) ℤ) {N : ℕ} (x : Fin N → K)
    (hx : ∀ k, x k ≠ 0) (gm' : Fin N → LinearMap.BilinForm ℤ X)
    (hu : ∀ mu c, ∃ r ∈ k₀, ev₁ (u mu c) = r * ∏ k, x k ^ qW W (gm' k) mu) {l l' : ℕ} (a : Fin l × Fin 8 → X)
    (a' : Fin l' × Fin 8 → X) (c : Fin l → C) (c' : Fin l' → C) (ha : IsUnit (∏ i, u (fun v => a (i, v)) (c i)))
    (k : Fin N) (p : ℤ) (hp : 0 < p) (hlin : ∀ k', lin W a (gm' k') - lin W a' (gm' k') = if k' = k then p else 0)
    (hr : ∃ r ∈ k₀, ev₁ (∏ i, u (fun v => a (i, v)) (c i)) = r * ev₁ (∏ i, u (fun v => a' (i, v)) (c' i))) :
    x k ∈ k₀ := by
  have key : ∀ {l : ℕ} (a : Fin l × Fin 8 → X) (c : Fin l → C), ∃ Rr ∈ k₀,
      ev₁ (∏ i, u (fun v => a (i, v)) (c i)) = Rr * ∏ k, x k ^ lin W a (gm' k) := by
    intro l a c
    choose rr hrr heq using hu
    refine ⟨∏ i, rr (fun v => a (i, v)) (c i), prod_mem fun i _ => hrr _ _, ?_⟩
    rw [map_prod]
    simp_rw [heq]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [prod_zpow_eq (hx k)]
    rfl
  obtain ⟨Rr, hR, hReq⟩ := key a c
  obtain ⟨Rr', hR', hR'eq⟩ := key a' c'
  obtain ⟨r, hr, hrr⟩ := hr
  have hne : ev₁ (∏ i, u (fun v => a (i, v)) (c i)) ≠ 0 := (ha.map ev₁).ne_zero
  have hP : ∀ (b : Fin N → ℤ), ∏ k, x k ^ b k ≠ 0 := fun b =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  have hR0 : Rr ≠ 0 := by intro h0; rw [h0, zero_mul] at hReq; exact hne hReq
  have hxp : x k ^ p = r * Rr' / Rr := by
    have e1 : x k ^ p = ∏ k', x k' ^ (lin W a (gm' k') - lin W a' (gm' k')) := by
      simp_rw [hlin]
      rw [Finset.prod_eq_single k (fun b _ hb => by rw [if_neg hb, zpow_zero]) (by simp)]
      rw [if_pos rfl]
    have e2 : ∏ k', x k' ^ (lin W a (gm' k') - lin W a' (gm' k')) =
        (∏ k', x k' ^ lin W a (gm' k')) / ∏ k', x k' ^ lin W a' (gm' k') := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k' _ => zpow_sub₀ (hx k') _ _
    rw [e1, e2, eq_div_iff hR0, div_mul_eq_mul_div, div_eq_iff (hP _)]
    rw [hReq, hR'eq] at hrr
    linear_combination hrr
  have hmem : x k ^ p.toNat ∈ k₀ := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hp.le, hxp]
    exact div_mem (mul_mem hr hR') hR
  exact mem_of_pow_mem k₀ hk (x k) p.toNat (by omega) hmem

theorem exists_hasSupports_int (q : ℕ) (φ : InvFun ℤ) (hpol : IsPolFan id q φ) :
    ∃ d, 1 ≤ d ∧ HasSupports (id : ℤ → ℤ) q φ d := by
  refine exists_hasSupports ℤ id q φ hpol fun X _ iM _ _ hX r gm' hgm' => ?_
  obtain rfl : iM = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  have : Module.Free ℤ X := inferInstance
  exact exists_supports_int φ X (hpol X hX) r gm' hgm'

theorem mem_balForms_of_symm {X : Type} [AddCommGroup X] (i : Module ℤ X)
    (β : @LinearMap.BilinForm ℤ _ X _ (AddCommGroup.toIntModule X)) (hs : ∀ y z, β y z = β z y) :
    β ∈ @balForms ℤ _ id X _ i := by
  obtain rfl : i = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  refine ⟨hs, fun a y z => ?_⟩
  simp

end GlobalTheory.Poinc.Sep.Assembly


open GlobalTheory.Poinc.Sep.Assembly in
theorem GlobalTheory.Poinc.Sep.sepSt : SepSt := by
  intro g hg n hn hodd F Z z i hTC φ hpol hnsi d J S π j hd hJ hval hbl hji V _ _ _ Q ξ hU m N s ε τ₀ hrk hcone hdef
    hsl hsr hτ K _ _ ev k₀ hk₀ hcen hdefo
  obtain ⟨hproj, hnorm, hoi, hiz, hdense, W, hE8, hTI⟩ := hTC
  haveI := hoi
  let ga : Fin m → LinearMap.BilinForm ℤ Q.X := fun k => (ε (.inl k) : LinearMap.BilinForm ℤ Q.X)
  let t : Fin m → V := fun k => s (.inl k)
  let δ : Fin m → LinearMap.BilinForm ℤ Q.X := fun k => (n : ℤ) • ga k
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsymm : ∀ k a b, δ k a b = δ k b a := fun k a b => by
    simp only [δ, LinearMap.smul_apply, smul_eq_mul]; rw [(hcone.mem k).1 a b]
  have hpsd : ∀ k a, 0 ≤ δ k a a := fun k a => by
    simp only [δ, LinearMap.smul_apply, smul_eq_mul]; exact mul_nonneg hn0.le (hcone.nonneg k a)
  have hposd : ∀ a, a ≠ 0 → ∃ k, 0 < δ k a a := fun a ha => by
    obtain ⟨k, hk⟩ := hdef a ha
    exact ⟨k, by simp only [δ, LinearMap.smul_apply, smul_eq_mul]; exact mul_pos hn0 hk⟩
  have hmono : Q.IsMonomialTau t δ :=
    monoTau_inl Q τ₀ s (fun k => (n : ℤ) • (ε k : LinearMap.BilinForm ℤ Q.X)) hsr hτ
  have hUi : UnifOver F i (ξ ≫ π) Q := hji ▸ unifOver_comp F j π ξ Q hU
  set l := n.minFac with hl_def
  have hl : l.Prime := Nat.minFac_prime (by omega)
  have hldvd : l ∣ n := Nat.minFac_dvd n
  have hlodd : Odd l := Odd.of_dvd_nat hodd hldvd
  have hl3 : 3 ≤ l := by
    have := hl.two_le; obtain ⟨r, hr⟩ := hlodd; omega
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.torsion_theta_values_abelianPart_defined_over Q.g l hl hlodd W hE8
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.eighthPower_thetaCoefficient_eq_const_mul_monomial Q.g l hl hlodd W hE8
  obtain ⟨jj, X₁, z₁, Φ, y, ρ, e, h, hjj, hTr, hCM⟩ := GlobalTheory.T.exists_fourierTermSystem_regular_traits_given_chart g hg n hn hodd F Z z i hproj ((GlobalTheory.isNormalScheme_iff Z).1 hnorm) hiz hdense W hE8 hTI
    V Q m t δ hrk hsl hsymm hpsd hposd hmono (ξ ≫ π) hUi l hl hldvd (max (max j₁ j₂) 1)
  let e' : Φ.X y ≃ₗ[ℤ] Q.X := e.toIntLinearEquiv
  let ga' : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y) := fun k => (LinearMap.BilinForm.congr e'.symm) (ga (h k))
  obtain ⟨ev₁, hev₁, hEl⟩ := GlobalTheory.T.exists_stalk_elements_approx_leadingTerm_quotients g hg n hn hodd F Z z i hproj ((GlobalTheory.isNormalScheme_iff Z).1 hnorm) hiz hdense W hE8 φ d J S π j hJ hval hbl hji
    hpol V Q m t δ hrk hsl hsymm hpsd hposd hmono ga n (by omega) hcone (fun k => rfl) ξ hU ((l ^ jj) ^ 2) X₁ z₁ Φ y ρ e h
    hTr hCM K ev k₀ hk₀ hcen hdefo ga' (fun k a b => by simp [ga', e'])
  obtain ⟨d₀, hd₀, hsup⟩ := exists_hasSupports_int g φ hpol
  have hjj1 : 1 ≤ jj := le_trans (le_max_right _ _) hjj
  have hN₁ : 3 ≤ (l ^ jj) ^ 2 := by
    have h1 : l ≤ l ^ jj := Nat.le_self_pow (by omega) l
    have h2 : l ^ jj ≤ (l ^ jj) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hm : Φ.mod y = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  have hrkΦ : Module.finrank ℤ (Φ.X y) ≤ g := by
    convert Φ.rank_le y <;> first | rfl | exact hm.symm
  have hFΦ : IsPolFanOn id φ (Φ.X y) := hpol (Φ.X y) hrkΦ
  have hδ' : ∀ k, Φ.δ y k = (n : ℤ) • ga' k := fun k => by
    ext a b
    rw [(hCM.2.2.2.1 k).2 a b]
    simp [ga', e', δ, ga]
  have hV := GlobalTheory.T.poincareApprox_values_at_point_of_elements ℤ id g φ hpol hnsi d₀ d hd₀ hd hsup 7 W hE8.1 ((l ^ jj) ^ 2) hN₁ _ Φ y ga' n (by omega)
    (isCone_inst (AddCommGroup.toIntModule _) (Φ.mod y) ga' (isCone_equiv hFΦ ga hcone e' h)) hδ' K ev₁ k₀ hEl
  obtain ⟨hinj, -, -, htd, D, e₈, hSharp, hTheta⟩ := hCM
  have hA1 : ∀ i, ev (s (.inl i)) = 0 := fun i => by
    obtain ⟨k, rfl⟩ := h.surjective i
    have := hV.1 k
    rw [(htd k).1, ← RingHom.comp_apply, hev₁] at this
    exact this
  have hlu : IsUnit ((l : ℕ) : Φ.V y) := by
    have hnV : IsUnit ((n : ℕ) : V) := isUnit_natCast_of_cyc n (by omega) V (ξ ≫ π ≫ z)
    have hlV : IsUnit ((l : ℕ) : V) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hldvd) hnV
    simpa using hlV.map ρ
  have hmu : ∀ mu : Fin 8 → Q.X, mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)) ≠ 0 ∧
      ∃ c, IsUnit (Φ.u y (fun a => e.symm (mu a)) c) := fun mu =>
    ⟨Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (Φ.t_mem y k).2, Φ.u_unit y _⟩
  refine ⟨hA1, ?_, ?_⟩
  · intro o' _ ζ' g' n' F' lam β β₂ hn' hd' hgp hsq hlb a
    have := hj₁ jj (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hjj) V (Φ.V y) (Φ.cn y) hlu Q le_rfl ρ hinj D e₈
      hSharp Φ.Q (fun mu c => Φ.u y (fun a => e.symm (mu a)) c) (fun mu => mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)))
      hmu hTheta K ev₁ k₀ hk₀ (fun mu c c' hc' => hV.2.1 _ c c' hc') o' ζ' g' n' F' lam β β₂ hn' (by rwa [hev₁]) hgp hsq hlb a
    rwa [hev₁] at this
  · intro W₀ _ ιtb hFB hW₀ i
    rcases i with i | k
    · rw [hA1 i]; exact k₀.zero_mem
    · let u : (Fin 8 → Q.X) → Φ.Q → Φ.V y := fun mu c => Φ.u y (fun a => e.symm (mu a)) c
      let mo : (Fin 8 → Q.X) → Φ.V y := fun mu => mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a))
      let εn : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X := fun k => (n : ℤ) • (ε k : LinearMap.BilinForm ℤ Q.X)
      have hqnn : ∀ k mu, 0 ≤ qW W (εn (.inl k)) mu := fun k mu => qW_nonneg hE8.1 (hsymm k) (hpsd k) mu
      have hmo : ∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => εn (.inl k)) mu := fun mu => by
        simp only [mo, mono]
        refine Fintype.prod_equiv h _ _ fun k' => ?_
        rw [(htd k').1]
        congr 2
        simp only [qW]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [(htd k').2]
        simp [εn, δ, ga]
      have hsb := hj₂ jj (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hjj) V (Φ.V y) (Φ.cn y) hlu Q le_rfl ρ
        hinj D e₈ hSharp Φ.Q u mo hmu hTheta K ev₁ k₀ hk₀ τ₀ m N s εn hsr hqnn hτ hmo W₀ ιtb hFB
        (fun a => by rw [← RingHom.comp_apply, hev₁]; exact hW₀ a)
      obtain ⟨c0, hc0, lam, hlam⟩ := exists_ext_functional (LinearMap.BilinForm ℤ Q.X) (balForms (id : ℤ → ℤ) Q.X)
        (ε.coord (.inr k))
      let lamΦ : LinearMap.BilinForm ℤ (Φ.X y) →ₗ[ℤ] ℤ := lam ∘ₗ (LinearMap.BilinForm.congr e').toLinearMap
      have hback : ∀ β : LinearMap.BilinForm ℤ Q.X,
          LinearMap.BilinForm.congr e' (LinearMap.BilinForm.congr e'.symm β) = β := fun β => by
        ext a b; simp
      have hlamε : ∀ j', lamΦ (LinearMap.BilinForm.congr e'.symm (ε j')) = if j' = .inr k then c0 else 0 := fun j' => by
        simp only [lamΦ, LinearMap.comp_apply, LinearEquiv.coe_coe, hback]
        rw [hlam (ε j'), Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs <;> simp
      have hker : ∀ k', lamΦ (Φ.δ y k') = 0 := fun k' => by
        rw [hδ' k', map_zsmul, show ga' k' = LinearMap.BilinForm.congr e'.symm (ε (.inl (h k'))) from rfl, hlamε]
        simp
      obtain ⟨l1, l1', M, a, a', c, c', hM, hu, hu', hlin, r, hr, hev⟩ := hV.2.2 lamΦ hker
      have hlin' : ∀ k', lin W (fun p => e (a p)) (εn (.inr k')) - lin W (fun p => e (a' p)) (εn (.inr k')) =
          if k' = k then (M : ℤ) * (n * c0) else 0 := fun k' => by
        have hb := (ε (.inr k')).2
        have := hlin _ (mem_balForms_of_symm (Φ.mod y) (LinearMap.BilinForm.congr e'.symm (εn (.inr k'))) fun y z => by
          simp only [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_symm, εn, LinearMap.smul_apply]
          rw [hb.1])
        have htr : ∀ {l2 : ℕ} (b : Fin l2 × Fin 8 → Φ.X y),
            lin W (fun p => e (b p)) (εn (.inr k')) = lin W b (LinearMap.BilinForm.congr e'.symm (εn (.inr k'))) := by
          intro l2 b; simp [lin, qW, e']
        have hl2 : lamΦ (LinearMap.BilinForm.congr e'.symm (εn (.inr k'))) =
            (n : ℤ) * (if (Sum.inr k' : Fin m ⊕ Fin N) = .inr k then c0 else 0) := by
          rw [show εn (.inr k') = (n : ℤ) • (ε (.inr k') : LinearMap.BilinForm ℤ Q.X) from rfl, map_zsmul, map_zsmul,
            hlamε, smul_eq_mul]
        rw [htr, htr, this, hl2]
        rcases eq_or_ne k' k with rfl | hk
        · simp only [if_true]
        · simp only [hk, if_false, Sum.inr.injEq, mul_zero]
      have hxk := mem_of_ratio k₀ hk₀ ev₁ u W (fun k => ev (s (.inr k))) (fun k => ((hsr k).map ev).ne_zero)
        (fun k => εn (.inr k)) (fun mu c => by
          obtain ⟨r, hr, he⟩ := hsb mu c
          refine ⟨r, hr, ?_⟩
          rw [he]
          simp only [← RingHom.comp_apply, hev₁]) (fun p => e (a p)) (fun p => e (a' p)) c c'
        (by
          have hc : (∏ i, u (fun v => e (a (i, v))) (c i)) = Φ.coefT y a c := by simp [u, GlobalTheory.Poinc.VSys.coefT]
          rw [hc]; exact hu) k ((M : ℤ) * (n * c0)) (by positivity) hlin'
        ⟨r, hr, by
          have hc : ∀ {l2 : ℕ} (b : Fin l2 × Fin 8 → Φ.X y) (d : Fin l2 → Φ.Q),
              (∏ i, u (fun v => e (b (i, v))) (d i)) = Φ.coefT y b d := by
            intro l2 b d; simp [u, GlobalTheory.Poinc.VSys.coefT]
          rw [hc, hc]; exact hev⟩
      exact hxk
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreField =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreFieldStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreFieldStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreField\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.chartSeparation_data_defined_over_centre_field : GlobalTheory.Poinc.Sep.SepSt := by
  first | exact @GlobalTheory.Poinc.Sep.sepSt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreFieldStatement =====
