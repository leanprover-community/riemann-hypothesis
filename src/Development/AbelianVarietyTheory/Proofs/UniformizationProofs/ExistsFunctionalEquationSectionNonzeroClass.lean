module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombBijective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtPt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullSecSval
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSubSum
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistConvNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Imports
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralWitness
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProdExpOppositeTranslates
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfSvalWhiskerRightEqZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalSecScale
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.FESection

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB k hk hF1 hFk ⟨β₁, hβ₁⟩ ⟨β₀, hβ₀⟩ α
  have hG := hL.globalFns
  obtain ⟨σ, f, sf, hσ, hpf, hfef, -, hf0⟩ := IntWit.integral_witness V hV D A G U (Kbar V) k β₀ hFk hβ₀
  obtain ⟨ϑ, g, sg, hϑ, hpg, hfeg, ⟨j₁, hs1⟩, -⟩ := IntWit.integral_witness V hV D A G U (Kbar V) 1 β₁ hF1 hβ₁
  have hg0 : ∃ j, (g (α - β₀)).f j ≠ 0 := by
    by_contra hn
    push_neg at hn
    have h1 : ∀ j, (sg (α - β₀)).f j = 0 := fun j =>
      sec_ext_val (s' := DVR.SecOps.secZero) D.P.isLB (fun y J hJ => by
        rw [hpg _ y J hJ, DVR.UUA.sval_zero_of hn _ y J (hJ.mem _ _),
          DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]) j
    exact hs1 (FamFree.zero_of_eq_add_nsmul hG (⟨sg, hfeg⟩ : Fam D (Kbar V) 1)
      ⟨β₁ - (α - β₀), by rw [one_smul, add_sub_cancel]⟩ h1 j₁)
  obtain ⟨W, _, _, _, φ, a, hW, hφ, hnv⟩ := GlobalTheory.UU.exists_twist_conv_ne_zero V hV D k f g α β₀
    (GlobalTheory.NullExp.main V _ D A G U _ k σ f hσ) hf0 hg0
  obtain ⟨σ', f', hσ', hff, hpf'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) k σ f hσ
  obtain ⟨ϑ', g', hϑ', hgg, hpg'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) 1 ϑ g hϑ
  have hu : φ ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  obtain ⟨x, hx⟩ := TorPtEx.main V hV D A G U W hW a
  obtain ⟨σ'', hprod⟩ := GlobalTheory.UU.prodExp_opposite_translates hG V hV D A G U W hW a x hx k σ' ϑ' f' g' hσ' hϑ'
  obtain ⟨h, hh, hext⟩ := GlobalTheory.UU.ExpExt.main hL hL2 V hV D A G U W hW (k + 1) (by omega) σ''
  have hconv := GlobalTheory.ConvOfProd.main V _ D A G U _ k 1 _ _ h σ'' hprod hh
  obtain ⟨ht, hs⟩ := PullSec.pullEx V hV D A G U (Kbar V) (TA V W) φ (k + 1)
  obtain ⟨t, ht, -⟩ := ht σ''
  obtain ⟨s, hs, -⟩ := hs h
  refine ⟨t, s, hext _ φ t s ht hs, ?_, ?_⟩
  · refine GlobalTheory.ConvFE.conv_famFE hG V hV D hB W hW (Kbar V) φ hφ k 1 f' g' h sf sg s a (a ^ k)⁻¹ (fun mu => ?_)
      ((hpf' _ φ sf).2 (hu ▸ hpf)) ((hpg' _ φ sg).2 (hu ▸ hpg)) hs hfef hfeg hconv
    rw [one_smul, ofAdd_nsmul, map_pow, MonoidHom.inv_apply, MonoidHom.pow_apply, mul_inv_cancel]
  · obtain ⟨j, hj⟩ := hnv f' g' h hff hgg hconv
    by_contra hn
    push_neg at hn
    haveI := D.P.isAb.smooth
    haveI : Flat D.P.A.hom := inferInstance
    haveI : IsAffine (TA V W).left := inferInstanceAs (IsAffine (Spec _))
    haveI : IsAffine (TF (R := V) (Kbar V)).left := inferInstanceAs (IsAffine (Spec _))
    refine hj (sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A _ _ φ hφ _ D.P.L D.P.isLB _ _ _ (h α)
      (fun z J hJ => ?_) j)
    exact (hs α z J hJ).symm.trans (DVR.UUA.sval_zero_of hn _ z J (hJ.mem _ _))

end GlobalTheory.UU.FESection
