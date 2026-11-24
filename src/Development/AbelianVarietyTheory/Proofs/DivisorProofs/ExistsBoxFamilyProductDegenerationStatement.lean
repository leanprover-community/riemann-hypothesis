module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegeneration, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegenerationStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegeneration =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegeneration", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional\nimport Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem trF_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X → D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (mu : D.X) :
    (DegPre.trF D F mu).left ≫ (TF (R := R) F ◁ p).left =
      (TF (R := R) F ◁ p).left ≫ (DegPre.trF D₁ F (q mu)).left := by
  refine congrArg (fun m => m.left) (?_ : DegPre.trF D F mu ≫ (TF (R := R) F ◁ p) =
    (TF (R := R) F ◁ p) ≫ DegPre.trF D₁ F (q mu))
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerLeft_snd, DegPre.trF, DegPre.trF, lift_snd, lift_snd_assoc]
    have b : DegPre.prB D F ≫ p = (TF (R := R) F ◁ p) ≫ DegPre.prB D₁ F := (whiskerLeft_snd _ _).symm
    have e : (DegPre.prB D F * cP D _ mu) ≫ p = (TF (R := R) F ◁ p) ≫ (DegPre.prB D₁ F * cP D₁ _ (q mu)) := by
      rw [MonObj.mul_comp, MonObj.comp_mul, b, GlobalTheory.ProdUnif.cPoint_pr hc, comp_cP]
    exact e

theorem zF_pr {D D₁ : DegPre R} (p : D.P.A ⟶ D₁.P.A) [IsMonHom p] :
    (DegPre.zF D F).left ≫ (TF (R := R) F ◁ p).left = (DegPre.zF D₁ F).left := by
  refine congrArg (fun m => m.left) (?_ : DegPre.zF D F ≫ (TF (R := R) F ◁ p) = DegPre.zF D₁ F)
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem deltaφ_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X →+ D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (k : ℕ) (α mu : D.X) (a : Fin 4 ⊕ Fin 4) :
    DegPre.deltaφ D F k α mu a ≫ p.left = (TF (R := R) F ◁ p).left ≫ DegPre.deltaφ D₁ F k (q α) (q mu) a := by
  rcases a with a | a
  · refine (GlobalTheory.ProdUnif.famφ_pr hc F (α + k • mu) a).trans ?_
    rw [map_add (f := _), map_nsmul]; rfl
  · show ((DegPre.trF D F mu).left ≫ DegPre.famφ D F α a) ≫ _ =
      _ ≫ (DegPre.trF D₁ F (q mu)).left ≫ DegPre.famφ D₁ F (q α) a
    rw [Category.assoc, GlobalTheory.ProdUnif.famφ_pr hc, ← Category.assoc, trF_pr F hc, Category.assoc]

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

section Values

variable {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X)
  {w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)}

theorem famMult_box₂ (hrig : IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig)
    (hpsi : ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x)))
    (k : ℕ) (α mu : D.X) (y : (TF (R := R) F).left) {J₁ J₂ J}
    (hJ₁ : Good D₁.P.L y J₁) (hJ₂ : Good D₂.P.L y J₂) (hJ : Good D.P.L y J) :
    (∏ a, om w y J₁ J₂ J ((DegPre.zF D F).left ≫ DegPre.deltaφ D F k α mu a) ^ DegPre.deltaε k a) *
      val (Z := (TF (R := R) F).left) (DegPre.famMult D F k mu α) (𝟙 _) y J =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)) (𝟙 _) y J₁ *
        val (Z := (TF (R := R) F).left) (DegPre.famMult D₂ F k (q₂ mu) (q₂ α)) (𝟙 _) y J₂ := by
  have a₁ : ∀ χ, (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ =>
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have a₂ : (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left ≫ eSec D.P.A =
      (1 : TF (R := R) F ⟶ D.P.A).left :=
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have b₁ := fun χ => hpsi χ _ (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ J₂ J hJ₁ hJ₂ hJ
  have b₂ := hrig _ ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₁ J₂ J hJ₁ hJ₂ hJ
  simp only [Fintype.prod_unique, Category.comp_id] at b₁ b₂
  have r₀ : val D.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      val D.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J := val_pull hJ _ _ _
  have r₁ : val D₁.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ =
      val D₁.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₁ := val_pull hJ₁ _ _ _
  have r₂ : val D₂.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂ =
      val D₂.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₂ := val_pull hJ₂ _ _ _
  have c₁ : ∀ χ, val (D.psi χ) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      om w y J₁ J₂ J (cP D (TF (R := R) F) χ).left *
        (val (D₁.psi (q₁ χ)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ *
          val (D₂.psi (q₂ χ)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂) := fun χ => by
    have h := b₁ χ
    rw [zpow_neg_one, show (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ ptK (D.c χ) =
      (cP D (TF (R := R) F) χ).left from a₁ χ] at h
    exact inv_mul_eq_iff_eq_mul.1 h
  have c₂ : val D.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      (om w y J₁ J₂ J (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ *
        (val D₁.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ *
          val D₂.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂) := by
    rw [r₀, r₁, r₂]
    rw [zpow_one, Category.assoc, a₂] at b₂
    exact eq_inv_mul_of_mul_eq b₂
  have c₃ := c₁ (mu + α)
  rw [map_add (f := _), map_add (f := _)] at c₃
  rw [GlobalTheory.BoxFamily.prod_delta_zero F D k α mu (om w y J₁ J₂ J), GlobalTheory.BoxFamily.famMult_val F hJ,
    GlobalTheory.BoxFamily.famMult_val F hJ₁, GlobalTheory.BoxFamily.famMult_val F hJ₂, c₃, c₁ mu, c₁ α, c₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  module

end Values

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem fe_along {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X →+ D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) {k : ℕ} (E₁ : Fam D₁ F k) (mu α : D.X)
    (u₁ : LB.Gen (LB.LinComb D₁.P.L (DegPre.deltaφ D₁ F k (q α) (q mu)) (DegPre.deltaε k))) (hu₁ : u₁.IsGen)
    (hc₁ : LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ u₁ (DegPre.zF D₁ F).left)
      (DegPre.famMult D₁ F k (q mu) (q α)))
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J₁} (hJ₁ : Good D₁.P.L z J₁) :
    sval (E₁.s (q (α + k • mu))) (r ≫ (TF (R := R) F ◁ p).left) z J₁ =
      sval (E₁.s (q α)) ((r ≫ (DegPre.trF D F mu).left) ≫ (TF (R := R) F ◁ p).left) z J₁ *
        (val u₁ (r ≫ (TF (R := R) F ◁ p).left) z J₁).val := by
  have h := (secRel_iff D₁.P.isLB _ _ _ _ _ _ _ _ _ u₁).1 (E₁.fe _ _ u₁ hu₁ hc₁) _
    (r ≫ (TF (R := R) F ◁ p).left) z J₁ hJ₁
  rw [map_add (f := _), map_nsmul, h, Category.assoc, Category.assoc, trF_pr F hc]

variable {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} {q₁ : D.X →+ D₁.X} {q₂ : D.X →+ D₂.X}
  {w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)}

theorem gen_box₂ (hS : IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂) (hw : w.IsGen)
    (hrig : IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig)
    (hpsi : ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) (hG : GlobalFnsSt)
    (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α))
    (u₁ : LB.Gen (LB.LinComb D₁.P.L (DegPre.deltaφ D₁ F k (q₁ α) (q₁ mu)) (DegPre.deltaε k))) (hu₁ : u₁.IsGen)
    (hc₁ : LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ u₁ (DegPre.zF D₁ F).left)
      (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)))
    (u₂ : LB.Gen (LB.LinComb D₂.P.L (DegPre.deltaφ D₂ F k (q₂ α) (q₂ mu)) (DegPre.deltaε k))) (hu₂ : u₂.IsGen)
    (hc₂ : LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ u₂ (DegPre.zF D₂ F).left)
      (DegPre.famMult D₂ F k (q₂ mu) (q₂ α))) :
    IsBoxGen w (TF (R := R) F ◁ p₁).left (TF (R := R) F ◁ p₂).left u u₁ u₂ := by
  haveI := hS.hom₁
  haveI := hS.hom₂
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (deltaφ_pr F hS.c_pr₁ k α mu)
    (deltaφ_pr F hS.c_pr₂ k α mu) hu hu₁ hu₂ (fst (TF (R := R) F) D.P.A).left (DegPre.zF D F).left
    (congrArg (fun q => q.left) z₁) (surj_appTop D F hG) ?_
  intro y J₁ J₂ J hJ₁ hJ₂ hJ
  have e := famMult_box₂ F q₁ q₂ hrig hpsi k α mu y hJ₁ hJ₂ hJ
  have v : val u (DegPre.zF D F).left y J =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D F k mu α) (𝟙 _) y J := by
    have h := val_corr hJ hc (𝟙 _)
    rwa [val_pull hJ, Category.id_comp] at h
  have v₁ : val u₁ ((DegPre.zF D F).left ≫ (TF (R := R) F ◁ p₁).left) y J₁ =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)) (𝟙 _) y J₁ := by
    have h := val_corr hJ₁ hc₁ (𝟙 _)
    rw [val_pull hJ₁, Category.id_comp] at h
    rw [zF_pr]; exact h
  have v₂ : val u₂ ((DegPre.zF D F).left ≫ (TF (R := R) F ◁ p₂).left) y J₂ =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₂ F k (q₂ mu) (q₂ α)) (𝟙 _) y J₂ := by
    have h := val_corr hJ₂ hc₂ (𝟙 _)
    rw [val_pull hJ₂, Category.id_comp] at h
    rw [zF_pr]; exact h
  rw [v, v₁, v₂]
  exact e

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

theorem exists_isBoxFam₂ : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), w.IsGen → IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig → (∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (E₁ : Fam D₁ F k) (E₂ : Fam D₂ F k), ∃ E : Fam D F k, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k E E₁ E₂ := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w hw hrig hpsi F _ _ k E₁ E₂
  haveI := hS.hom₁
  haveI := hS.hom₂
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  choose s hs using fun α : D.X => exists_boxSec w hw D₁.P.isLB D₂.P.isLB D.P.isLB
    (GlobalTheory.ProdUnif.famφ_pr hS.c_pr₁ F α) (GlobalTheory.ProdUnif.famφ_pr hS.c_pr₂ F α) (E₁.s (q₁ α)) (E₂.s (q₂ α))
  refine ⟨⟨s, ?_⟩, hs⟩
  intro mu α u hu hc
  obtain ⟨u₁, hu₁, hc₁⟩ := (gen_fe (D := D₁) (F := F) hG k (q₁ mu) (q₁ α)).1
  obtain ⟨u₂, hu₂, hc₂⟩ := (gen_fe (D := D₂) (F := F) hG k (q₂ mu) (q₂ α)).1
  have hb := gen_box₂ F hS hw hrig hpsi hG k α mu u hu hc u₁ hu₁ hc₁ u₂ hu₂ hc₂
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.P.isLB y
  have e₁ := hs (α + k • mu) _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have e₂ := hs α _ (𝟙 _ ≫ (DegPre.trF D F mu).left) y J₁ J₂ J hJ₁ hJ₂ hJ
  have e₃ := hb _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have f₁ := fe_along F hS.c_pr₁ E₁ mu α u₁ hu₁ hc₁ (𝟙 _) y hJ₁
  have f₂ := fe_along F hS.c_pr₂ E₂ mu α u₂ hu₂ hc₂ (𝟙 _) y hJ₂
  have e₅ : (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.deltaφ D F k α mu a) ^ DegPre.deltaε k a) =
      (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.famφ D F (α + k • mu) a) ^ DegPre.famε k a) *
      (∏ a, om w y J₁ J₂ J ((𝟙 _ ≫ (DegPre.trF D F mu).left) ≫ DegPre.famφ D F α a) ^ DegPre.famε k a)⁻¹ := by
    simp only [Category.assoc]
    exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
  refine (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.famφ D F (α + k • mu) a) ^ DegPre.famε k a).mul_right_inj.1 ?_
  refine e₁.trans ?_
  rw [f₁, f₂]
  refine Eq.trans ?_ ((congrArg₂ (· * ·) e₂ (congrArg Units.val e₃)).symm.trans ?_)
  · rw [Units.val_mul]; ring
  · rw [e₅]; exact GlobalTheory.BoxFamily.unit_shuffle _ _ _ _

end GlobalTheory.BoxFamSum
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegeneration =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegenerationStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegenerationStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegeneration\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

theorem _root_.GlobalTheory.T.exists_boxFamily_productDegeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), w.IsGen → IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig → (∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (E₁ : Fam D₁ F k) (E₂ : Fam D₂ F k), ∃ E : Fam D F k, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k E E₁ E₂ := by
  first | exact @GlobalTheory.BoxFamSum.exists_isBoxFam₂
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegenerationStatement =====
