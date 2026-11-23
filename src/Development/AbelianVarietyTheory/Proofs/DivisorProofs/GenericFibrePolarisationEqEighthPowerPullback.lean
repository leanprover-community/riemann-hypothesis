module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
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

namespace GlobalTheory.Poinc.GenPull

theorem lbIso_gen_pull : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀), ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → LBIso A'.L (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' gm ψ hψ H
  have e0 : LBIso A'.L (A'.L.pull (𝟙 _)) := GlobalTheory.SiegelPullComp.iso_pull_id A'.isLB
  have hc : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have e1 : LBIso ((A'.L.pull U'.gen.hom.left).pull U'.gen.inv.left) (A'.L.pull (𝟙 _)) := by
    have := GlobalTheory.SiegelPullComp.iso_pull_pull A'.isLB U'.gen.hom.left U'.gen.inv.left
    rwa [hc] at this
  have e2 := GlobalTheory.SiegelPullComp.iso_pull U'.gen.inv.left U'.ext
  have e3 := GlobalTheory.SiegelPullComp.iso_pull_pull U'.LG.isLB (pullback.fst G'.hom (jK R)) U'.gen.inv.left
  have e4 := GlobalTheory.SiegelPullComp.iso_pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) H
  have e5 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB gm (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R))
  have hq : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm = ψ ≫ FinalForm.φ := by
    rw [Category.assoc, hψ]
  rw [hq] at e5
  have e6 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB FinalForm.φ ψ
  have e7 := GlobalTheory.SiegelPullComp.iso_pull ψ (⟨FinalForm.w, FinalForm.w_gen⟩ : LBIso _ _)
  have e8 := GlobalTheory.SiegelPullComp.iso_pull_pull ρ.P.isLB (pullback.fst ρ.P.A.hom FinalForm.u₀) ψ
  have hA := A'.isLB
  have hG := U'.LG.isLB
  have hZ := FinalForm.L.isLB
  have hP := ρ.P.isLB
  refine LBIso.trans hA (pull_isLB (pull_isLB hA _) _) (pull_isLB hP _) (LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _) e0 e1.symm) ?_
  refine LBIso.trans (pull_isLB (pull_isLB hA _) _) (pull_isLB (pull_isLB hG _) _) (pull_isLB hP _) e2 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hG _) _) (pull_isLB hG _) (pull_isLB hP _) e3 ?_
  refine LBIso.trans (pull_isLB hG _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e4 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) (pull_isLB hP _) e5 ?_
  refine LBIso.trans (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e6.symm ?_
  exact LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e7 e8

end GlobalTheory.Poinc.GenPull
