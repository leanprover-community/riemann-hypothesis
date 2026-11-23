module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem lbIso_lam_pull_id_w0 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
    (t : SAB H S) :
    LBIso t.PP.L ((abelian₂ t.G t.PP.L).pull (Y := t.G.left) (lift (𝟙 t.G) (t.act.act H.w0)).left) := by
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  refine t.prim.trans t.PP.isLB (LB.isLB_linComb t.PP.isLB _ _) (LB.isLB_pull hΛ _) ?_
  refine LBIso.chartPull (A := abelian₂ t.G t.PP.L) (B := abelian₂ t.G t.PP.L) (h := (lift (𝟙 t.G) (t.act.act H.w0)).left)
    (chartPullSame t.PP.L _ _ _ _ fun I => ?_) (Geo.Tor.chartPullPull _ _ _ rfl) (Pdiv.PullbackComparison.gen_refl _ hΛ)
  have e : psum t.G ![𝟙 t.G, t.act.act H.w0] I.down =
      lift (𝟙 t.G) (t.act.act H.w0) ≫ psum t.G (x2 t.G) I.down := by
    refine Eq.trans (congrArg (fun z => psum t.G z I.down) (funext fun i => ?_))
      (psum_hom (preHom (lift (𝟙 t.G) (t.act.act H.w0))) (x2 t.G) I.down).symm
    fin_cases i
    · exact (lift_fst _ _).symm
    · exact (lift_snd _ _).symm
  exact congrArg (fun z => z.left) e

theorem exists_sabMap_of_isProper_of_lbIso_lam : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left) (φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → IsSquare φ φ₂ → LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hL E _ _ _ H S S' t t' f φ φ₂ hp gp sq hΛ hact
  refine exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S' t t' f φ hp gp ?_ hact
  have l : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  have l' : (abelian₂ t'.G t'.PP.L).IsLB := LB.isLB_linComb t'.PP.isLB _ _
  let δ : t.G.left ⟶ (G2 t.G).left := (lift (𝟙 t.G) (t.act.act H.w0)).left
  let δ' : t'.G.left ⟶ (G2 t'.G).left := (lift (𝟙 t'.G) (t'.act.act H.w0)).left
  have a₁ : δ ≫ (fst t.G t.G).left = 𝟙 _ := congrArg (fun z => z.left) (lift_fst (𝟙 t.G) (t.act.act H.w0))
  have a₂ : δ ≫ (snd t.G t.G).left = (t.act.act H.w0).left :=
    congrArg (fun z => z.left) (lift_snd (𝟙 t.G) (t.act.act H.w0))
  have b₁ : δ' ≫ (fst t'.G t'.G).left = 𝟙 _ := congrArg (fun z => z.left) (lift_fst (𝟙 t'.G) (t'.act.act H.w0))
  have b₂ : δ' ≫ (snd t'.G t'.G).left = (t'.act.act H.w0).left :=
    congrArg (fun z => z.left) (lift_snd (𝟙 t'.G) (t'.act.act H.w0))
  have e : δ' ≫ φ₂ = φ ≫ δ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst t.G t.G).left = (_ ≫ _) ≫ (fst t.G t.G).left
      rw [Category.assoc, sq.1, ← Category.assoc, b₁, Category.assoc, a₁, Category.id_comp, Category.comp_id]
    · show (_ ≫ _) ≫ (snd t.G t.G).left = (_ ≫ _) ≫ (snd t.G t.G).left
      rw [Category.assoc, sq.2, ← Category.assoc, b₂, Category.assoc, a₂, hact]
  have s₁ : LBIso t'.PP.L (((abelian₂ t.G t.PP.L).pull φ₂).pull δ') :=
    (lbIso_lam_pull_id_w0 t').trans t'.PP.isLB (LB.isLB_pull l' _) (LB.isLB_pull (LB.isLB_pull l _) _)
      (SiegelPullComp.iso_pull δ' hΛ)
  have s₂ : LBIso t'.PP.L ((abelian₂ t.G t.PP.L).pull (δ' ≫ φ₂)) :=
    s₁.trans t'.PP.isLB (LB.isLB_pull (LB.isLB_pull l _) _) (LB.isLB_pull l _) (SiegelPullComp.iso_pull_pull l φ₂ δ')
  rw [e] at s₂
  have s₃ : LBIso t'.PP.L (((abelian₂ t.G t.PP.L).pull δ).pull φ) :=
    s₂.trans t'.PP.isLB (LB.isLB_pull l _) (LB.isLB_pull (LB.isLB_pull l _) _) (SiegelPullComp.iso_pull_pull l δ φ).symm
  exact s₃.trans t'.PP.isLB (LB.isLB_pull (LB.isLB_pull l _) _) (LB.isLB_pull t.PP.isLB _)
    (SiegelPullComp.iso_pull φ (lbIso_lam_pull_id_w0 t)).symm

end GlobalTheory
