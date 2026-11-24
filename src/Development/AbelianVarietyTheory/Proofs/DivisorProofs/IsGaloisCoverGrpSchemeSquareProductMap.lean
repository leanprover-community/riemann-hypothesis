module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.ProdGalois
variable {S : Scheme.{0}}

theorem transl_lift_fst {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ fst A A = fst A A ≫ transl h₁ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_fst,
    ← Category.assoc, toUnit_unique (fst A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_snd {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ snd A A = snd A A ≫ transl h₂ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_snd,
    ← Category.assoc, toUnit_unique (snd A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_fst_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (fst A A).left = (fst A A).left ≫ (transl h₁).left := by
  rw [← Over.comp_left, transl_lift_fst, Over.comp_left]

theorem transl_lift_snd_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (snd A A).left = (snd A A).left ≫ (transl h₂).left := by
  rw [← Over.comp_left, transl_lift_snd, Over.comp_left]

theorem grpScheme_square_hom_ext_fst_snd {A : Over S} {X : Scheme.{0}} {a b : X ⟶ (G2 A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem grpSchemeSquareProductMap_comp_fst {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem grpSchemeSquareProductMap_eq_pullback_map {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ = pullback.map A.hom A.hom A'.hom A'.hom ψ.left ψ.left (𝟙 S) (by simp) (by simp) := by
  apply grpScheme_square_hom_ext_fst_snd
  · rw [grpSchemeSquareProductMap_comp_fst]; exact (pullback.lift_fst _ _ _).symm
  · rw [grpSchemeSquareProductMap_comp_snd]; exact (pullback.lift_snd _ _ _).symm

end GlobalTheory.UPel.HT.Hecke.ProdGalois


open GlobalTheory.UPel.HT.Hecke.ProdGalois in
theorem GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → GlobalTheory.ZM.IsGaloisCover (G × G) (fun h => (GlobalTheory.UPel.HT.Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left) (GlobalTheory.UPel.HT.Hecke.sq2 ψ) := by
  intro S A A' _ _ _ _ G ψ _ hψ
  have := hψ.finite
  have hfin := hψ.fin
  have het := hψ.etale
  have hon := hψ.onto
  refine
    { finite := inferInstance
      one := ?_
      mul := ?_
      inv := ?_
      fin := ?_
      etale := ?_
      onto := ?_
      fibre := ?_ }
  · apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).1 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
    · rw [transl_lift_snd_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).2 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
  · intro a c
    apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.assoc, transl_lift_fst_left, reassoc_of% transl_lift_fst_left]
      have e := hψ.mul a.1 c.1
      rw [show ((a * c).1 : 𝟙_ (Over S) ⟶ A) = ((a.1 * c.1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
    · rw [transl_lift_snd_left, Category.assoc, transl_lift_snd_left, reassoc_of% transl_lift_snd_left]
      have e := hψ.mul a.2 c.2
      rw [show ((a * c).2 : 𝟙_ (Over S) ⟶ A) = ((a.2 * c.2 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
  · intro a
    apply grpScheme_square_hom_ext_fst_snd
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_fst, reassoc_of% transl_lift_fst_left, hψ.inv a.1]
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_snd, reassoc_of% transl_lift_snd_left, hψ.inv a.2]
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    exact MorphismProperty.pullbackMap (P := @IsFinite) hfin hfin (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Etale.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullbackMap (P := @Etale) het het (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Surjective.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullbackMap (P := @Surjective) hon hon (Over.w ψ).symm (Over.w ψ).symm
  · intro K _ _ y y' e
    have e₁ : (y ≫ (fst A A).left) ≫ ψ.left = (y' ≫ (fst A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_fst, reassoc_of% e]
    have e₂ : (y ≫ (snd A A).left) ≫ ψ.left = (y' ≫ (snd A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_snd, reassoc_of% e]
    obtain ⟨a₁, ha₁, hu₁⟩ := hψ.fibre K _ _ e₁
    obtain ⟨a₂, ha₂, hu₂⟩ := hψ.fibre K _ _ e₂
    refine ⟨(a₁, a₂), ?_, ?_⟩
    · apply grpScheme_square_hom_ext_fst_snd
      · rw [Category.assoc, transl_lift_fst_left, ← Category.assoc]; exact ha₁
      · rw [Category.assoc, transl_lift_snd_left, ← Category.assoc]; exact ha₂
    · intro b hb
      refine Prod.ext (hu₁ b.1 ?_) (hu₂ b.2 ?_)
      · show (y ≫ (fst A A).left) ≫ (transl (b.1 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (fst A A).left
        rw [Category.assoc, ← transl_lift_fst_left _ (b.2 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (fst A A).left) hb
      · show (y ≫ (snd A A).left) ≫ (transl (b.2 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (snd A A).left
        rw [Category.assoc, ← transl_lift_snd_left (b.1 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (snd A A).left) hb
