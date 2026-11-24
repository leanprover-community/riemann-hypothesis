module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.SiegelDataPull

open GlobalTheory.SiegelPullComp

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : Geo.Tor.IsSquare ψ ψ₂) (h : Geo.Tor.IsSquare φ φ₂) : Geo.Tor.IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem siegData_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T T' : Scheme.{0}) (sT : T ⟶ Sp O) (f : T' ⟶ T) (t : SAB H T) (t' : SAB H T') (ν : SABMap t' t f) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (lev' : D.La → (𝟙_ (Over T') ⟶ t'.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), (∀ x, (lev' x).left ≫ ν.φ = f ≫ (lev x).left) → SiegData sT t lev Ag z bas w → SiegData (f ≫ sT) t' lev' Ag z bas (f ≫ w) := by
  intro E _ _ _ H D O _ T T' sT f t t' ν lev lev' g p N Ag z bas w hlev hw
  obtain ⟨o, φ, φ₂, hpb, hsq, hiso, hlv, hsnd, hSPB⟩ := hw
  obtain ⟨⟨o', ho'⟩, -⟩ := GlobalTheory.siegPre_pullback _ _ _ _ _ _ _ ((f ≫ sT) ≫ spMap z) f o
    (Category.assoc f sT (spMap z)).symm
  have hpbo := ho'
  obtain ⟨φ₁, φ₁₂, hpb₁, hsq₁, hiso₁, hlv₁⟩ := hpbo
  have hν : IsGrpPullback t'.G t.G f ν.φ := ν.cart
  have hc : IsGrpPullback o'.A t.G f (φ₁ ≫ φ) := (hpb₁.comp hpb).congr (Category.comp_id f) rfl
  obtain ⟨e, he, hel⟩ := grpPullback_iso hc hν
  haveI := he
  have hpb' : IsGrpPullback o'.A t'.G (𝟙 T') e.hom.left := isGrpPullback_of_iso e
  have hsq' := GlobalTheory.LamPull.exists_isSquare hpb'.1.w
  have hν₂ := GlobalTheory.LamPull.exists_isSquare hν.1.w
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.PP.isLB _ _
  have hΛ' : (abelian₂ t'.G t'.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t'.PP.isLB _ _
  have sA := isSquare_comp hsq₁ hsq
  have sB := isSquare_comp hsq' hν₂
  rw [hel] at sB
  have key := GlobalTheory.LamPull.isSquare_unique sA sB
  refine ⟨o', e.hom.left, _, hpb', hsq', ?_, ?_, ?_, ?_⟩
  · have h2 := GlobalTheory.SiegelPullComp.iso_pull φ₁₂ hiso
    have h3 := GlobalTheory.SiegelPullComp.iso_pull_pull hΛ φ₂ φ₁₂
    rw [key] at h3
    have h4 := (GlobalTheory.SiegelPullComp.iso_pull_pull hΛ (lift (pushPt hν.1.w (fst t'.G t'.G))
      (pushPt hν.1.w (snd t'.G t'.G))).left (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left).symm
    have h5 := GlobalTheory.SiegelPullComp.iso_pull (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left ((GlobalTheory.LamPull.lam_pull E H T T' t t' f).2 ν _ hν₂).symm
    have l0 := o'.isLB
    have l1 := pull_isLB o.isLB φ₁₂
    have l2 := pull_isLB (pull_isLB hΛ φ₂) φ₁₂
    refine LBIso.trans l0 l1 (pull_isLB hΛ' _) hiso₁ ?_
    refine LBIso.trans l1 l2 (pull_isLB hΛ' _) h2 ?_
    refine LBIso.trans l2 (pull_isLB hΛ _) (pull_isLB hΛ' _) h3 ?_
    refine LBIso.trans (pull_isLB hΛ _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ' _) h4 h5
  · intro u
    apply hν.1.hom_ext
    · rw [Category.assoc, hel, ← Category.assoc, hlv₁ u, Category.assoc, hlv u, hlev]
    · rw [Category.assoc, Over.w e.hom, Over.w (o'.lev u), Over.w (lev' (bas u))]
  · rw [Category.assoc, hsnd]
  · rw [Category.assoc f w (pullback.fst Ag.s (spMap z))]
    exact GlobalTheory.SiegelPullComp.pb_comp hSPB ho'

end GlobalTheory.SiegelDataPull

end
