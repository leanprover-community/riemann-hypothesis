module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.LamPull

theorem exists_isSquare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) :
    IsSquare φ (lift (pushPt w (fst G' G')) (pushPt w (snd G' G'))).left :=
  ⟨congrArg (fun z => z.left) (lift_fst (pushPt w (fst G' G')) (pushPt w (snd G' G'))),
    congrArg (fun z => z.left) (lift_snd (pushPt w (fst G' G')) (pushPt w (snd G' G')))⟩

theorem isSquare_unique {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b := by
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

theorem lbIso_lam_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ))
    {φ₂ : (G2 G').left ⟶ (G2 G).left} (hφ : IsSquare φ φ₂) : LBIso (abelian₂ G' L') ((abelian₂ G L).pull φ₂) := by
  obtain rfl := isSquare_unique hφ (exists_isSquare h.1.w)
  have hΛ : (abelian₂ G L).IsLB := DVR.linComb_isLB L hL _ _
  have h₁ : LBIso (abelian₂ G' L') (abelian₂ G' (L.pull φ)) := by
    obtain ⟨w, hw⟩ := H
    exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩
  let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have h₂ : LBIso (abelian₂ G' (L.pull φ)) ((abelian₂ G L).pull U.left) := by
    refine LBIso.chartPull
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (Geo.Tor.chartPullPull (abelian₂ G L) _ U.left rfl) ⟨idIso _, idIso_isGen hΛ⟩
    fin_cases i <;> simp [U, x2]
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ (LB.isLB_pull hL φ) _ _) (LB.isLB_pull hΛ _) h₁ h₂

theorem lam_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S), (∀ φ : t'.G.left ⟶ t.G.left, φ ≫ t.G.hom = t'.G.hom ≫ f → ∃ φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left, IsSquare φ φ₂) ∧ ∀ (ν : SABMap t' t f) (φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left), IsSquare ν.φ φ₂ → LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) := by
  intro E _ _ _ H S S' t t' f
  refine ⟨fun φ w => ⟨_, exists_isSquare w⟩, fun ν φ₂ hφ => ?_⟩
  obtain ⟨w, hw, -⟩ := ν.lin
  exact lbIso_lam_pull ν.cart t.PP.isLB t'.PP.isLB ⟨w, hw⟩ hφ

end GlobalTheory.LamPull
