module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularCurve
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

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge

theorem topologicalKrullDim_le_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Sp k) (g : ℕ)
    (hf : SmoothOfRelativeDimension g f) : topologicalKrullDim X ≤ g := by
  rw [GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk]
  exact iSup_le fun x ↦ GroundTheory.Arith.SchemeCoh.ringKrullDim_stalk_le_of_smoothOfRelativeDimension g f x

theorem subsingleton_coh_abelian (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g n : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hn : g < n) :
    Subsingleton (GlobalTheory.coh (GlobalTheory.structureModule A.left) n) := by
  refine GlobalTheory.subsingleton_coh_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA) _ ?_
  refine lt_of_le_of_lt ((topologicalKrullDim_subspace_le _ _).trans
    (topologicalKrullDim_le_of_smooth A.hom g hg)) ?_
  exact_mod_cast hn

theorem exact_of_subsingleton_Hs {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (n : ℕ) (hdd : dn F (n + 1) ∘ₗ dn F n = 0) (h : Subsingleton (Hs F n)) :
    Function.Exact (dn F n) (dn F (n + 1)) := by
  intro x
  constructor
  · intro hx
    have hm : (⟨x, hx⟩ : LinearMap.ker (dn F (n + 1))) ∈
        (LinearMap.range (dn F n)).comap (LinearMap.ker (dn F (n + 1))).subtype :=
      (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
    exact hm
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hdd y

theorem vanSt (hCx : CxSt) (hCmp : CmpSt) : VanSt := by
  intro R _ A _ g hA hg hR P _ _ S n hn
  letI := hR.toField
  have hsep : IsSeparated A.hom := by
    have := hA.proper
    infer_instance
  obtain ⟨e⟩ := (hCmp R A.left A.hom hsep P S).2 n
  have hs : Subsingleton (GlobalTheory.coh (GlobalTheory.structureModule A.left) (n + 1)) :=
    subsingleton_coh_abelian R A g (n + 1) hA hg (Nat.lt_succ_of_le hn)
  exact exact_of_subsingleton_Hs _ n ((hCx R _ (OSys A.hom S)).1 n) e.toEquiv.subsingleton

end GlobalTheory.CompanionTheory.Hodge
