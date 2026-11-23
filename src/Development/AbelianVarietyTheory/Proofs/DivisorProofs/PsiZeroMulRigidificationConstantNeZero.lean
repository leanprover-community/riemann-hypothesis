module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem psi_zero_rig_const : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), ∃ c₀ : FractionRing V, c₀ ≠ 0 ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = GlobalTheory.UT.cst (FractionRing V) z c₀ := by
  intro V _ _ D
  obtain ⟨z⟩ := GlobalTheory.UT.CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J', hJ'⟩ := GlobalTheory.UT.CoefBasic.exists_good' D.P.isLB z
  obtain ⟨c, hc⟩ := GlobalTheory.UT.CoefBasic.cstH_surj z
    ((@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J')).val * (rigV D (TF (R := V) (FractionRing V)).hom z J').val)
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    rw [← Units.val_mul] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := GlobalTheory.UT.CoefBasic.pt_eq z z'
    have a₁ := GlobalTheory.UT.CoefBasic.val_tr (D.psi_gen 0) (jFK (R := V) (FractionRing V)) hJ hJ'
    have a₂ : rigV D (TF (R := V) (FractionRing V)).hom z J =
        GlobalTheory.UT.CoefBasic.trU D.P.L z J J' ((TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A) *
        rigV D (TF (R := V) (FractionRing V)).hom z J' := by
      refine (GlobalTheory.UT.CoefBasic.val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
        (TF (R := V) (FractionRing V)).hom hJ hJ').trans ?_
      rw [Fintype.prod_unique, zpow_one]; rfl
    have e : jFK (R := V) (FractionRing V) ≫ ptK (D.c 0) = (TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A := by
      rw [GlobalTheory.Poinc.ThetaOne.c_zero]
      rfl
    simp only [e] at a₁
    rw [GlobalTheory.UT.CoefBasic.cst_eq, hc]
    show (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J).val * _ = _
    rw [a₁, a₂, ← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [Fintype.prod_unique, Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one, zpow_neg,
      zpow_one, id]
    rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.Poinc.IntTerm

end
