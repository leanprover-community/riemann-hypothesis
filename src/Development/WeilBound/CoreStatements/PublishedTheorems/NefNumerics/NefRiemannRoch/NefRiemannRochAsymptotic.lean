import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharH0H1BoundHigher
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistBoundOfShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMul
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegAllDims
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfRegularSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfTwoCuts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1GrowthNoSectionsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyGrowthTwist
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestFurther
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistPushforwardClosedImmersio

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRR

theorem hdim_twist_structureModule_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ _ hproj d L hL hkd hind i hi
  haveI : IsLocallyNoetherian X := by
    obtain ⟨N, f, hf, -⟩ := hproj
    haveI := hf
    exact LocallyOfFiniteType.isLocallyNoetherian (f ≫ PSpace.str k N)
  have hsupp : suppDim (GlobalTheory.structureModule X) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (suppDim_structureModule (X := X)).trans_le hkd
  by_cases hsec : ∃ p, 1 ≤ p ∧ HasNonzeroSec (lbPow L p)
  · obtain ⟨p, hp, s, hs⟩ := hsec
    have hmono : Mono (cutHom (GlobalTheory.structureModule X) (isLB_lbPow hL.isLB p) s) :=
      (mono_cutHom_structureModule_iff _ s).mpr ((sec_ne_zero_iff s).mp hs)
    exact T.higherCohomology_twist_bound_of_regular_section k X hproj d L hL.isLB hind (GlobalTheory.structureModule X) hsupp p hp s hmono i hi
  · push_neg at hsec
    have h0 : ∀ m, 1 ≤ m → hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 = 0 := by
      intro m hm
      by_contra hne
      exact hsec m hm (lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) (Nat.pos_of_ne_zero hne))
    have hint := T.nef_intersection_nonneg_all_dims k X hproj (d + 1) (GlobalTheory.structureModule X) hsupp (fun _ => L) (fun _ => hL)
    have hi2 := T.higherCohomology_twist_bound_of_two_cuts k X hproj d L hL.isLB hind (GlobalTheory.structureModule X) hsupp
    rcases Nat.lt_or_ge i 2 with h | h
    · obtain rfl : i = 1 := by omega
      exact T.h1_dim_bound_of_no_sections_nonneg_interNum k X hproj d L hL.isLB (GlobalTheory.structureModule X) hsupp h0 hint hi2
    · exact hi2 i h

end GlobalTheory.NefRR
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.higher_cohomology_growth_structure : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  atlas_forward_decl _root_.GlobalTheory.NefRR.hdim_twist_structureModule_le
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefBound

theorem le_natCast_of_lt_succ {a : WithBot ℕ∞} {d : ℕ} (h : a < ((d + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (d : WithBot ℕ∞) :=
  _root_.UpperTheory.Reformulated.B.Yhb2.main h

end GlobalTheory.NefBound

open GlobalTheory.VB in

theorem GlobalTheory.NefBound.hdim_twist_le_of_isIntegral : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (G : X.Modules) [IsFiniteQC G], ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist G (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ _ hp d L hL hd hE
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  suffices H : ∀ r : ℕ, ∀ (G : X.Modules) [IsFiniteQC G], genRank G = r → ∀ i, 0 < i →
      ∃ C : ℕ, ∀ m : ℕ, hdim k (twist G (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d) by
    intro G _
    exact H _ G rfl
  intro r
  induction r with
  | zero =>
    intro G _ h i hi
    have hs : suppDim G ≤ (d : WithBot ℕ∞) :=
      GlobalTheory.NefBound.le_natCast_of_lt_succ (suppDim_lt_of_genRank_eq_zero hd h)
    obtain ⟨C, hC⟩ := hE G hs i hi
    refine ⟨C, fun m => (hC m).trans (Nat.mul_le_mul_left _ ?_)⟩
    exact Nat.mul_le_mul (Nat.le_succ d) (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))
  | succ r ih =>
    intro G _ h i hi
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule X).genRank_eq, hr] at e₃
    let S := ShortComplex.mk (QCoh.sectionHom s) (cokernel.π _) (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    have hQ : IsFiniteQC S.X₃ := inferInstanceAs (IsFiniteQC (cokernel (QCoh.sectionHom s)))
    have h1 : IsFiniteQC S.X₁ := inferInstanceAs (IsFiniteQC (structureModule X))
    have hbd : ∀ i, 0 < i → ∃ C : ℕ, ∀ m : ℕ,
        hdim k (twist (twist G (lbPow A n)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d) :=
      fun i hi => GlobalTheory.T.sheafCohomologyDim_twist_bound_of_shortExact k X hp L hL.isLB S hS h1 hQ i _
        (GlobalTheory.T.higher_cohomology_growth_structure k X hp d L hL hd hE i hi) (ih (cokernel (QCoh.sectionHom s)) (by omega) i hi)
    obtain ⟨C, hC⟩ := GlobalTheory.T.higher_cohomology_growth_twist k X hp d L hL.isLB hE (twist G (lbPow A n))
      ((QCoh.suppDim_le _).trans hd) _ (isLB_lbZPow hM (-1)) hbd i hi
    refine ⟨C, fun m => ?_⟩
    exact (hdim_congr k i ((twistFunctor (lbPow L m)).mapIso (Twist.twistTwistZNegOneIso G hM))).symm.trans_le (hC m)
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.higher_cohomology_growth_coherent : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (G : X.Modules) [IsFiniteQC G], ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist G (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  atlas_forward_decl _root_.GlobalTheory.NefBound.hdim_twist_le_of_isIntegral
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RRPush

theorem hdim_pushforward_le : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → ∀ N : LB Y, IsNef k N → ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ L : LB X, IsNef k L → ∀ Z : Closeds X, IsIrreducible (Z : Set X) → topologicalKrullDim (Z : Set X) ≤ (d + 1 : ℕ) → ∀ (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [IsFiniteQC G], ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist ((Scheme.Modules.pushforward (redι Z)).obj G) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ d hY X _ hp L hL Z hZ hd G _ i hi
  haveI := isIntegral_red hZ
  letI := algebraΓAlong k (redι Z)
  have hk := appTop_algebraMap_along k (redι Z)
  have hp' : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    obtain ⟨n, e, he, hs⟩ := hp
    exact ⟨n, redι Z ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom hk]⟩
  have hLZ : IsNef k (L.pull (redι Z)) := hL.pull_of_isClosedImmersion (redι Z) hk
  have hdV : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (d + 1 : ℕ) :=
    (topologicalKrullDim_red Z).trans_le hd
  obtain ⟨C, hC⟩ := GlobalTheory.T.higher_cohomology_growth_coherent k _ hp' d (L.pull (redι Z)) hLZ hdV
    (fun E _ hE j hj => hY _ hp' _ hLZ E hE j hj) G i hi
  refine ⟨C, fun m => ?_⟩
  rw [GlobalTheory.T.sheafCohomologyDim_twist_pushforward_closedImmersion k X _ (redι Z) L hL.isLB G m i]
  exact hC m

end GlobalTheory.RRPush
end
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem nefTwist_hdim_bound_succ : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → ∀ N : LB Y, IsNef k N → ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → ∀ N : LB Y, IsNef k N → ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d + 1 : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * ((d + 1) * (m + 1) ^ d))) := by
  intro k _ _ d hd Y _ hY N hN E _ hsupp j hj
  haveI hnoeth : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hY
  obtain ⟨hprop, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hY
  haveI := hprop
  have hfin : ∀ (F : Y.Modules) [IsFiniteQC F] (m : ℕ), FiniteCoh k (twist F (lbPow N m)) :=
    fun F _ m => IsAmpleLB.finiteCohTwists (algebraMap_eq_strHom k Y) F hA _ (isLB_lbPow hN.isLB m)
  let P : Y.Modules → Prop := fun F => suppDim F ≤ ((d + 1 : ℕ) : WithBot ℕ∞) →
    ∀ j, 0 < j → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow N m)) j ≤ C * ((d + 1) * (m + 1) ^ d)
  have key : ∀ F : Y.Modules, IsFiniteQC F → P F := by
    refine QCoh.devissage Y P ?_ ?_ ?_
    · intro F hF _ j _
      refine ⟨0, fun m => ?_⟩
      have hz : IsZero (twist F (lbPow N m)) := (isZero_twist_iff (isLB_lbPow hN.isLB m)).2 hF
      haveI : Subsingleton (coh (twist F (lbPow N m)) j) := by
        have := cohOn.subsingleton_of_isZero hz ⊤ j
        exact this
      rw [hdim_eq_zero_of_subsingleton]
      exact Nat.zero_le _
    · intro S hS h1 h3 hP1 hP3 hs2 j hj
      haveI := h1
      haveI := h3
      haveI := hS.mono_f
      haveI := hS.epi_g
      obtain ⟨C1, hC1⟩ := hP1 ((suppDim_le_of_mono S.f).trans hs2) j hj
      obtain ⟨C3, hC3⟩ := hP3 ((suppDim_le_of_epi S.g).trans hs2) j hj
      refine ⟨C1 + C3, fun m => ?_⟩
      have hL := isLB_lbPow hN.isLB m
      haveI := Twist.preservesFiniteLimits_twistFunctor hL
      haveI := Twist.preservesColimits_twistFunctor hL
      have hS' := hS.map_of_exact (twistFunctor (lbPow N m))
      have h := hdim₂_le k hS' j ((hfin S.X₁ m).finite j) ((hfin S.X₃ m).finite j)
      have e1 := hC1 m
      have e3 := hC3 m
      simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃, twistFunctor_obj] at h
      calc hdim k (twist S.X₂ (lbPow N m)) j ≤ hdim k (twist S.X₁ (lbPow N m)) j + hdim k (twist S.X₃ (lbPow N m)) j := h
        _ ≤ C1 * ((d + 1) * (m + 1) ^ d) + C3 * ((d + 1) * (m + 1) ^ d) := Nat.add_le_add e1 e3
        _ = (C1 + C3) * ((d + 1) * (m + 1) ^ d) := by ring
    · intro Z hirr IH G hG hs j hj
      haveI := hG
      have hsub : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ (Z : Set Y) := by
        refine (support_pushforward_subset_image_of_isClosedImmersion _ G).trans ?_
        rintro _ ⟨x, -, rfl⟩
        rw [← range_redι Z]
        exact ⟨x, rfl⟩
      haveI : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
        ProperFinite.isFiniteQC_pushforward (redι Z) (IsAmpleLB.pull_of_isClosedImmersion hA (redι Z)) G
      by_cases hstrict : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊂ (Z : Set Y)
      · exact IH _ inferInstance hstrict hs j hj
      · have heq : support ((Scheme.Modules.pushforward (redι Z)).obj G) = (Z : Set Y) := by
          by_contra hne
          exact hstrict (HasSubset.Subset.ssubset_of_ne hsub hne)
        have hgen := hirr.isGenericPoint_genericPoint_closure
        rw [Z.isClosed.closure_eq] at hgen
        obtain ⟨w, hcl⟩ : ∃ w : Y, closure ({w} : Set Y) = (Z : Set Y) := ⟨_, hgen⟩
        have hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
          rw [heq, ← hcl]
          exact subset_closure (Set.mem_singleton _)
        have hdimZ : topologicalKrullDim (Z : Set Y) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
          have := SheafCycle.dim_closure_le_suppDim hw
          rw [hcl] at this
          exact this.trans hs
        exact RRPush.hdim_pushforward_le k d hd Y hY N hN Z hirr hdimZ G j hj
  exact key E inferInstance hsupp j hj

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRiemannRoch

theorem hdim_twist_nef_pow_le_of_pos (k : Type) [Field k] [Infinite k] (d : ℕ) :
    ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → ∀ N : LB Y, IsNef k N →
      ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j →
        ∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * (d * (m + 1) ^ (d - 1)) := by
  induction d with
  | zero =>
    intro Y _ hY N hN E _ hE j hj
    refine ⟨0, fun m => ?_⟩
    haveI := isNoetherian_of_isProjOver hY
    have hE0 : suppDim E ≤ 0 := by exact_mod_cast hE
    haveI := subsingleton_coh_of_suppDim_le_zero hE0 hj
    rw [hdim_twist_of_suppDim_le_zero k hE0 (isLB_lbPow hN.isLB m), hdim_eq_zero_of_subsingleton]
    exact Nat.zero_le _
  | succ d ih => exact nefTwist_hdim_bound_succ k d ih

theorem abs_factorial_mul_sections_sub_top_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ), topologicalKrullDim X ≤ (d : ℕ) → ∀ L : LB X, IsNef k L → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * (lbH0 k (lbPow L m) : ℤ) - topSelfIntersection k L d * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hX d hd L hL
  haveI := isNoetherian_of_isProjOver hX
  obtain ⟨_, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hX
  have hLB := hL.isLB
  have hO : suppDim (structureModule X) ≤ ((d : ℕ) : WithBot ℕ∞) := by
    rw [QCoh.suppDim_structureModule]
    exact hd
  obtain ⟨p, hpdeg, hpeval, hpcoeff⟩ := DiffVanish.exists_polynomial_chi (F := structureModule X)
    (A := lbPow L 0) (B := L) (diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) _ hX hO) ℚ
    (isLB_lbPow hLB 0) hLB
  have hb : ∀ n : ℕ, 0 < n → ∃ C : ℕ, ∀ m : ℕ,
      hdim k (twist (structureModule X) (lbPow L m)) n ≤ C * (d * (m + 1) ^ (d - 1)) :=
    fun n hn => hdim_twist_nef_pow_le_of_pos k d X hX L hL (structureModule X) hO n hn
  choose! Cf hCf using hb
  set D : ℕ := d.factorial with hD
  set K : ℕ := ⌈(D : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|⌉₊ with hK
  refine ⟨K + D * ∑ i ∈ Finset.range d, Cf (i + 1), fun m => ?_⟩
  have hLm := isLB_lbPow hLB m
  haveI : IsFiniteQC (twist (structureModule X) (lbPow L m)) := isFiniteQC_twist hLm
  have hvan : ∀ n : ℕ, d + 1 ≤ n → Subsingleton (coh (twist (structureModule X) (lbPow L m)) n) := by
    intro n hn
    refine IsAmpleLB.subsingleton_coh_of_suppDim_lt hA _ ?_
    rw [suppDim_twist hLm]
    refine lt_of_le_of_lt hO ?_
    exact_mod_cast (Nat.lt_of_succ_le hn)
  have hchi1 := chi_eq_sum_range k (d + 1) hvan
  have hchi2 : (chi k (twist (structureModule X) (lbPow L m)) : ℚ) = p.eval (m : ℚ) := by
    rw [← hpeval (m : ℤ) (lbPow L m) hLm]
    · push_cast
      rfl
    · rw [cls_lbPow hLB, cls_lbPow hLB]
      simp
  have hev := Polynomial.eval_eq_sum_range' (n := d + 1) (by omega) (m : ℚ) (p := p)
  have hcd : (D : ℚ) * p.coeff d = (topSelfIntersection k L d : ℚ) := by
    rw [hpcoeff, topSelf_def]
    have : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos d).ne'
    field_simp
  set h : ℕ → ℚ := fun n => (hdim k (twist (structureModule X) (lbPow L m)) n : ℚ) with hh
  have hB : ∀ i ∈ Finset.range d, ((m : ℚ) ^ i ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : (m : ℚ) ^ i ≤ ((m : ℚ) + 1) ^ i := pow_le_pow_left₀ (by positivity) (by linarith) i
    have h2 : ((m : ℚ) + 1) ^ i ≤ ((m : ℚ) + 1) ^ (d - 1) :=
      pow_le_pow_right₀ (by have : (0 : ℚ) ≤ m := by positivity
                            linarith) (by omega)
    have h3 : ((m : ℚ) + 1) ^ (d - 1) ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) := by
      have : (1 : ℚ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      have : (0 : ℚ) ≤ ((m : ℚ) + 1) ^ (d - 1) := by positivity
      nlinarith
    linarith
  have hH : ∀ i ∈ Finset.range d, h (i + 1) ≤ (Cf (i + 1) : ℚ) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    intro i _
    have := hCf (i + 1) (Nat.succ_pos i) m
    simp only [hh]
    exact_mod_cast this
  have hkey : ((D : ℚ) * h 0 - (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d) =
      (D : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i
        - (D : ℚ) * ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1) := by
    have e1 : (chi k (twist (structureModule X) (lbPow L m)) : ℚ) =
        h 0 + ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1) := by
      rw [hchi1]
      push_cast
      rw [Finset.sum_range_succ']
      simp [hh]
      ring
    rw [hchi2, hev, Finset.sum_range_succ] at e1
    linear_combination (-(D : ℚ)) * e1 + (m : ℚ) ^ d * hcd
  have hfin : |(D : ℚ) * h 0 - (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d| ≤
      ((K + D * ∑ i ∈ Finset.range d, Cf (i + 1) : ℕ) : ℚ) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    rw [hkey]
    set B : ℚ := (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) with hBdef
    have hD0 : (0 : ℚ) ≤ D := by positivity
    have s1 : |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i| ≤ (∑ i ∈ Finset.range d, |p.coeff i|) * B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (m : ℚ) ^ i)]
      exact mul_le_mul_of_nonneg_left (hB i hi) (abs_nonneg _)
    have s2 : |∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)| ≤ (∑ i ∈ Finset.range d, (Cf (i + 1) : ℚ)) * B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by simp only [hh]; positivity)]
      exact hH i hi
    have hK' : (D : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i| ≤ (K : ℚ) := Nat.le_ceil _
    have hB0 : 0 ≤ B := by positivity
    calc |(D : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i
          - (D : ℚ) * ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)|
        ≤ |(D : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i|
          + |(D : ℚ) * ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)| := abs_sub _ _
      _ = (D : ℚ) * |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i|
          + (D : ℚ) * |∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hD0]
      _ ≤ (D : ℚ) * ((∑ i ∈ Finset.range d, |p.coeff i|) * B)
          + (D : ℚ) * ((∑ i ∈ Finset.range d, (Cf (i + 1) : ℚ)) * B) := by
          gcongr
      _ ≤ (K : ℚ) * B + (D : ℚ) * ((∑ i ∈ Finset.range d, (Cf (i + 1) : ℚ)) * B) := by
          nlinarith
      _ = ((K + D * ∑ i ∈ Finset.range d, Cf (i + 1) : ℕ) : ℚ) * B := by
          push_cast
          ring
  have hfin' : ((|(d.factorial : ℤ) * (lbH0 k (lbPow L m) : ℤ) - topSelfIntersection k L d * (m : ℤ) ^ d| : ℤ) : ℚ) ≤
      (((K + D * ∑ i ∈ Finset.range d, Cf (i + 1) : ℕ) : ℤ) * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) : ℤ) := by
    push_cast
    simpa [hh, lbH0, hD] using hfin
  exact_mod_cast hfin'

end GlobalTheory.NefRiemannRoch
end
