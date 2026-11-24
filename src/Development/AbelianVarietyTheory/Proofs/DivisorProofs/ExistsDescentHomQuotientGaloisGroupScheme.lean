module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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

noncomputable section

namespace GlobalTheory.HomDescent

variable {S : Scheme.{0}}

theorem isPullback_whiskerLeft' (A : Over S) {Y Z : Over S} (q : Y ⟶ Z) :
    IsPullback (A ◁ q).left (snd A Y).left (snd A Z).left q.left := by
  have h1 : IsPullback (fst A Z).left (snd A Z).left A.hom Z.hom := IsPullback.of_hasPullback A.hom Z.hom
  have h2 : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback A.hom Y.hom
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerLeft_fst, Over.w q]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

theorem isPullback_whiskerRight' {A A' : Over S} (q : A ⟶ A') (Y : Over S) :
    IsPullback (q ▷ Y).left (fst A Y).left (fst A' Y).left q.left := by
  have h1 : IsPullback (snd A' Y).left (fst A' Y).left Y.hom A'.hom :=
    (IsPullback.of_hasPullback A'.hom Y.hom).flip
  have h2 : IsPullback (snd A Y).left (fst A Y).left Y.hom A.hom := (IsPullback.of_hasPullback A.hom Y.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w q]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem epi_of_isPullback {X Y P Q : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {u : P ⟶ Q} {v : P ⟶ X} {t : Q ⟶ Y} (hp : IsPullback u v t π) : Epi u := by
  have := GlobalTheory.GaloisCartDesc.epi_pullback_fst h t
  rw [← hp.isoPullback_hom_fst]
  infer_instance

theorem exists_desc : ∀ (S : Scheme.{0}) (A A' B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj B] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ B, IsMonHom f → (∀ h ∈ H, h ≫ f = 1) → ∃ f' : A' ⟶ B, IsMonHom f' ∧ ψ ≫ f' = f := by
  intro S A A' B _ _ _ _ _ H ψ hψ hG f hf hH
  have inv : ∀ a : H, (GlobalTheory.UPel.HT.Hecke.transl a.1).left ≫ f.left = f.left := by
    intro a
    rw [← Over.comp_left]
    congr 1
    rw [GlobalTheory.UPel.HT.Hecke.transl, mul_comp, Category.id_comp, Category.assoc, hH a.1 a.2, comp_one, _root_.mul_one]
  obtain ⟨g, hg, -⟩ := hG.existsUnique_desc f.left inv
  have eψ : Epi ψ.left := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hG
  have w : g ≫ B.hom = A'.hom := by
    rw [← cancel_epi ψ.left, reassoc_of% hg, Over.w, Over.w]
  let f' : A' ⟶ B := Over.homMk g w
  have hf' : ψ ≫ f' = f := Over.OverMorphism.ext hg
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · rw [← IsMonHom.one_hom ψ, Category.assoc, hf', IsMonHom.one_hom]
  · have e1 : Epi (ψ ▷ A).left := epi_of_isPullback hG (isPullback_whiskerRight' ψ A)
    have e2 : Epi (A' ◁ ψ).left := epi_of_isPullback hG (isPullback_whiskerLeft' A' ψ)
    have e : Epi (ψ ⊗ₘ ψ).left := by
      rw [MonoidalCategory.tensorHom_def, Over.comp_left]; infer_instance
    apply Over.OverMorphism.ext
    rw [← cancel_epi (ψ ⊗ₘ ψ).left, ← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [← Category.assoc, ← IsMonHom.mul_hom ψ, Category.assoc, hf', IsMonHom.mul_hom, ← hf',
      ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]

end GlobalTheory.HomDescent
