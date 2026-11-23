module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Comma.LocallySmall
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open GlobalTheory GlobalTheory.PointQuot

private theorem constObj_hom_ext {S : Scheme} {I : Type} {Z : Over S} (f₁ f₂ : constObj S I ⟶ Z)
    (h : ∀ c, PointQuot.constPt S c ≫ f₁ = PointQuot.constPt S c ≫ f₂) : f₁ = f₂ := by
  ext : 1
  apply Sigma.hom_ext
  intro c
  have := congrArg Over.Hom.left (h c)
  exact this

theorem UpperTheory.Gal.crystallineComparison.Mod.constSub_of : ConstSub := by
  intro K _ A _ hsep Γ hfin
  have hinj : Function.Injective (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) := Subtype.val_injective
  haveI hmono : Mono (constDesc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A))) := mono_constDesc _ hinj
  obtain ⟨hG, hmon⟩ := exists_grpObj_constObj (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) Γ
    Subtype.range_coe
  have hsplit : FinEt.IsSplitOfRank (constObj (Sp K) Γ).hom (Nat.card Γ) := by
    rw [FinEt.isSplitOfRank_iff_exists_iso]
    refine ⟨Sigma.reindex (Finite.equivFin Γ).symm (fun _ => Sp K), ?_⟩
    apply Sigma.hom_ext
    intro j
    have h := Sigma.ι_reindex_hom (Finite.equivFin Γ).symm (fun _ : Γ => Sp K) j
    simp only [constObj, Over.mk_hom]
    rw [← Category.assoc]
    erw [h]
    simp
  haveI := hsplit.isFinite
  haveI := hsplit.etale
  refine ⟨constObj (Sp K) Γ, hG, constDesc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)), hmon, hmono,
    hsplit.isFinite, hsplit.etale, ?_, ?_, ?_, ?_⟩
  · refine ⟨hsplit.isFinite, (inferInstance : Flat (constObj (Sp K) Γ).hom), ?_, hsplit.finrank_eq⟩
    let c0 : Γ := ⟨1, Γ.one_mem⟩
    have hw : (PointQuot.constPt (Sp K) c0).left ≫ (toUnit (constObj (Sp K) Γ)).left = 𝟙 _ := by
      rw [← Over.comp_left]
      simp
    refine ⟨fun y => ⟨(PointQuot.constPt (Sp K) c0).left y, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, hw]
    rfl
  · intro g
    constructor
    · rintro ⟨y, hy⟩
      let z : (𝟙_ (Over (Sp K))).left := (⊥ : PrimeSpectrum K)
      obtain ⟨V, hzV, c, hc⟩ := locally_const_desc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) y z
      haveI : Nonempty (openObj (𝟙_ (Over (Sp K))) V).left := ⟨⟨z, hzV⟩⟩
      haveI := epi_toUnit (openObj (𝟙_ (Over (Sp K))) V)
      have e : openι (𝟙_ (Over (Sp K))) V = toUnit _ := toUnit_unique _ _
      rw [hy, e] at hc
      have := (cancel_epi _).1 hc
      rw [this]
      exact c.2
    · intro hg
      exact ⟨PointQuot.constPt (Sp K) (⟨g, hg⟩ : Γ), constPt_desc _ _⟩
  · intro α hα
    apply constObj_hom_ext
    intro c
    rw [← Category.assoc, constPt_desc]
    exact (hα _ c.2).trans (comp_one _).symm
  · intro α hα
    refine ⟨constDesc (fun c : Γ => PointQuot.constPt (Sp K) (⟨c.1 ≫ α, hα _ c.2⟩ : Γ)), ?_⟩
    apply constObj_hom_ext
    intro c
    simp only [← Category.assoc, constPt_desc]
