module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
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
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section
namespace GlobalTheory.GenPb

theorem genfib_grpPullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm ∧ ψ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ ξ₀ ∧ IsGrpPullback A'.A ρ.P.A (ξ₀ ≫ FinalForm.u₀) (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' ξ gm hgm ξ₀ hξ
  have := U'.gen_hom
  have : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
  have gpA : IsGrpPullback A'.A G' (jK R) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) :=
    ((isGrpPullback_of_iso U'.gen.symm).comp (isGrpPullback_pullback G' (jK R))).congr
      (Category.id_comp _) rfl
  have h2 : IsGrpPullback A'.A FinalForm.G (ξ₀ ≫ U₀.ι) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm) :=
    (gpA.comp hgm).congr hξ.symm rfl
  have hw : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) ≫ FinalForm.G.hom = (A'.A.hom ≫ ξ₀) ≫ U₀.ι := by
    have := h2.1.w
    simpa [Category.assoc] using this
  refine ⟨FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw,
    FinalForm.cart.1.lift_fst _ _ _, FinalForm.cart.1.lift_snd _ _ _, ?_⟩
  have h3 : IsGrpPullback A'.A ((Over.pullback FinalForm.u₀).obj ρ.P.A) ξ₀
      (FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw) :=
    IsGrpPullback.cancel FinalForm.cart (h2.congr rfl (by rw [FinalForm.cart.1.lift_fst, Category.assoc]))
      (FinalForm.cart.1.lift_snd _ _ _)
  exact h3.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)

end GlobalTheory.GenPb
