module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Tors

theorem ext_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (x x' : TFK (R := V) (FractionRing V) ⟶ A.A) (h h' h'' : (𝟙_ (Over (Sp V))) ⟶ G), IntTerm.Ext U.toUnifPre x h → IntTerm.Ext U.toUnifPre x' h' → IntTerm.Ext U.toUnifPre (x * x') h'' → h'' = h * h' := by
  intro V _ _ _ _ D A G _ _ _ U x x' h h' h'' hx hx' hx''
  have := U.gen_hom
  have := U.separated
  have hmon : IsMonHom U.gen.inv := inferInstance
  have hpb := isGrpPullback_pullback G (jK V)
  have e₁ := hpb.2 (TFK (R := V) (FractionRing V)) (x ≫ U.gen.inv) (x' ≫ U.gen.inv)
    (toUnit (TF (R := V) (FractionRing V)) ≫ h) (toUnit (TF (R := V) (FractionRing V)) ≫ h')
    (hx.symm.trans (Category.assoc _ _ _).symm) (hx'.symm.trans (Category.assoc _ _ _).symm)
  have e₂ : (x * x') ≫ U.gen.inv = (x ≫ U.gen.inv) * (x' ≫ U.gen.inv) := MonObj.mul_comp _ _ _
  have e₃ : toUnit (TF (R := V) (FractionRing V)) ≫ (h * h') =
      (toUnit (TF (R := V) (FractionRing V)) ≫ h) * (toUnit (TF (R := V) (FractionRing V)) ≫ h') :=
    MonObj.comp_mul _ _ _
  have e : (toUnit (TF (R := V) (FractionRing V)) ≫ h'').left =
      (toUnit (TF (R := V) (FractionRing V)) ≫ (h * h')).left := by
    rw [e₃]
    refine Eq.trans ?_ e₁.symm
    rw [← e₂]
    exact hx''.symm.trans (Category.assoc _ _ _).symm
  have hj : (toUnit (TF (R := V) (FractionRing V))).left = jK V := by
    have h₁ : jFK (R := V) (FractionRing V) = 𝟙 _ := Spec.map_id _
    have h₂ : (toUnit (TF (R := V) (FractionRing V))).left ≫ 𝟙 _ = jFK (R := V) (FractionRing V) ≫ jK V :=
      Over.w (toUnit (TF (R := V) (FractionRing V)))
    rw [Category.comp_id, h₁] at h₂
    exact h₂.trans (Category.id_comp _)
  have hd : IsDominant (jK V) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap V (FractionRing V))).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))]; exact bot_le)
  refine Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp V) G.hom ((Over.w h'').trans (Over.w (h * h')).symm) (jK V) ?_)
  rw [← hj]
  exact e

end GlobalTheory.Poinc.Tors
