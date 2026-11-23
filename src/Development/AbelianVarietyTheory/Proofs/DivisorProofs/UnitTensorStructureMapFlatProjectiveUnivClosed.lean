module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem topS_hom_ext {Rg : Type} [CommRing Rg] {Y : Over (Sp Rg)} (u v : Y ⟶ topS Rg) : u = v := by
  have hm : Mono (topS Rg).hom := by
    change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w u, Over.w v]

instance isIso_snd_left {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) :
    IsIso (snd (topS Rg) A).left := by
  have : IsIso (snd (topS Rg) A) := by
    refine ⟨⟨lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A), ?_, ?_⟩⟩
    · refine CartesianMonoidalCategory.hom_ext _ _ (topS_hom_ext _ _) ?_
      simp
    · simp
  exact (Over.forget _).map_isIso (snd (topS Rg) A)

theorem fA_flat_isProjBy_universallyClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  intro Rg _ A _ L hA hL hamp
  have hsq : IsPullback (snd (topS Rg) A).left (fA A) A.hom (𝟙 (Sp Rg)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w (snd (topS Rg) A)⟩
  obtain ⟨hproj, hsm, hpr, -⟩ :=
    GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp Rg) A L hA hL hamp Rg (𝟙 _) _ _ (fA A) hsq
  exact ⟨inferInstance, hproj, inferInstance⟩

end GlobalTheory.HomFixUniv
