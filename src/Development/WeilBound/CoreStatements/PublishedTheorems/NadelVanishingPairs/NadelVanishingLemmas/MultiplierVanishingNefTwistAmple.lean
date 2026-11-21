import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexDirectLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTwistNonzeroLocusMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleAddNefIsAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultipleBelowThreshold
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorOfForm
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCanonicalBundleBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEqStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreading
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsHaveSameZeroSchemeOfLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameDivisorTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBaseChangeSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProperModelFinitelyGeneratedSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeSncSameDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfRelSncDivisor
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartBaseChange
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerAffineChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFibreEquivPushoutFormallyEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOpenContainingFibreContainsNear
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeDivisorsSncBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefPullbackIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory

theorem isZero_cechH_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec)
    {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens),
    (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∀ n : ℕ,
    (∀ᶠ c : ℕ in atTop, IsZero (cechH ℤ (twistZ F L c) ⊤ U n)) → IsZero (cechH ℤ F (nonzeroLocus σ) U n) := by
  intro X F _ L hL σ ι _ _ U hU n h
  obtain ⟨μ, ρ, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.cech_twist_nonzero_locus_maps X F L hL σ U hU
  exact GlobalTheory.T.cech_complex_direct_limit (fun c => cechCube ℤ (twistZ F L c) ⊤ U) (cechCube ℤ F (nonzeroLocus σ) U) μ ρ h₁ h₂ h₃ h₄ n h

theorem subsingleton_cohOn_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) [CompactSpace X] [X.IsSeparated] (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) (i : ℕ), (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow L c)) i)) → Subsingleton (cohOn F (nonzeroLocus σ) i) := by
  intro X _ _ F _ L hL σ i h
  obtain ⟨κ, hκ, T, c, hT, -, hTc, hcov⟩ :=
    Twist.exists_finite_affine_chart_cover hL (W := ⊤) (isCompact_univ (X := X))
  letI : Fintype κ := Fintype.ofFinite κ
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  have hsep : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ a ∈ s, T a) :=
    (cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl inferInstance) κ T hT
  have hc : ⨆ a, T a = ⊤ := eq_top_iff.2 hcov
  have hV : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (cechOpen (nonzeroLocus σ) T s) := by
    rintro s ⟨a, ha⟩
    have hle : ⨅ b ∈ s, T b ≤ L.U (c a) := (biInf_le T ha).trans (hTc a)
    have e := Twist.basicOpen_resG_zfun (Twist.zofSec σ) (c a) hle
    rw [Twist.nonzeroLocus_zofSec hL] at e
    have e' : cechOpen (nonzeroLocus σ) T s = X.basicOpen (resG X hle (Twist.zfun (Twist.zofSec σ) (c a))) := by
      rw [e, cechOpen, inf_comm]
    rw [e']
    exact (hsep s ⟨a, ha⟩).basicOpen _
  have hVc : nonzeroLocus σ ≤ ⨆ a, T a := hc ▸ le_top
  have eV := cechHEquivCohOn ℤ hVc (cechAcyclicMod_of_isAffineOpen hV F) i
  have hZ : IsZero (cechH ℤ F (nonzeroLocus σ) T i) := by
    refine isZero_cechH_nonzeroLocus_of_eventually_twist X F L hL σ T hsep i (h.mono fun k hk => ?_)
    haveI hq : (twistZ F L k).IsQuasicoherent := Twist.isQuasicoherent_twist (Twist.isLB_lbZPow hL k)
    have e2 := cechHEquivCoh ℤ hc hsep (twistZ F L k) i
    haveI : Subsingleton (coh (twistZ F L k) i) := by rw [Twist.twistZ_natCast]; exact hk
    haveI : Subsingleton (cechH ℤ (twistZ F L k) ⊤ T i) := e2.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  haveI : Subsingleton (cechH ℤ F (nonzeroLocus σ) T i) := ModuleCat.subsingleton_of_isZero hZ
  exact eV.symm.injective.subsingleton

end GlobalTheory
end
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory

private theorem exists_sec_lbPow_add_nonzeroLocus_eq_inf {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {m n : ℕ} (s : (lbPow L m).Sec) (s' : (lbPow L n).Sec) :
    ∃ τ : (lbPow L (m + n)).Sec, nonzeroLocus τ = nonzeroLocus s ⊓ nonzeroLocus s' := by
  refine ⟨powSecMk (m + n) (fun i => powSecFn s i * powSecFn s' i) ?_, ?_⟩
  · intro i j
    rw [map_mul, map_mul, powSecFn_compat s i j, powSecFn_compat s' i j, pow_add]
    ring
  · rw [nonzeroLocus_powSecMk]
    simp_rw [Scheme.basicOpen_mul, ← nonzeroLocus_inf_powSecFn]
    apply le_antisymm
    · exact iSup_le fun i => le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    · intro x hx
      have hx' : x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx' ⊢
      obtain ⟨i, hi⟩ := hx'
      exact ⟨i, ⟨hx.1, hi⟩, ⟨hx.2, hi⟩⟩

theorem exists_sec_lbPow_nonzeroLocus_eq_iInf {X : Scheme.{0}} {H : LB X} (hH : H.IsLB)
    {r : ℕ} (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec) (he : ∀ a, 0 < e a)
    (t : Finset (Fin r)) (ht : t.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : (lbPow H N).Sec, nonzeroLocus τ = ⨅ a ∈ t, nonzeroLocus (σ a) := by
  induction t using Finset.cons_induction with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | cons a s ha ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨e a, he a, σ a, ?_⟩
      simp
    · obtain ⟨N, hN, τ, hτ⟩ := ih hs
      obtain ⟨τ', hτ'⟩ := exists_sec_lbPow_add_nonzeroLocus_eq_inf hH (σ a) τ
      refine ⟨e a + N, by omega, τ', ?_⟩
      rw [hτ', hτ, Finset.cons_eq_insert, Finset.iInf_insert]

theorem subsingleton_cohOn_preimage_iInf_nonzeroLocus : ∀ (X Y : Scheme.{0}) [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), H.IsLB → ∀ j : ℕ, (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → ∀ (r : ℕ) (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec), (∀ a, 0 < e a) → ∀ t : Finset (Fin r), t.Nonempty → Subsingleton (cohOn F (s ⁻¹ᵁ (⨅ a ∈ t, nonzeroLocus (σ a))) j) := by
  intro X Y _ _ s F _ H hH j hev r e σ he t ht
  obtain ⟨N, hN, τ, hτ⟩ := exists_sec_lbPow_nonzeroLocus_eq_iInf hH e σ he t ht
  rw [← hτ, ← nonzeroLocus_secPowPull τ s]
  have hM : (H.pull s).IsLB := LB.isLB_pull hH s
  have hL : (lbPow (H.pull s) N).IsLB := isLB_lbPow hM N
  apply subsingleton_cohOn_nonzeroLocus_of_eventually_twist Y F (lbPow (H.pull s) N) hL
  obtain ⟨c0, hc0⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨c0, fun c hc => ?_⟩
  have hcls : cls (lbPow (lbPow (H.pull s) N) c) (isLB_lbPow hL c)
      = cls (lbPow (H.pull s) (N * c)) (isLB_lbPow hM (N * c)) := by
    rw [CechPic.cls_lbPow hL, CechPic.cls_lbPow hM, CechPic.cls_lbPow hM, smul_smul, mul_comm]
  obtain ⟨iso⟩ := nonempty_twist_iso_of_cls_eq F (isLB_lbPow hL c) (isLB_lbPow hM (N * c)) hcls
  have hsub := hc0 (N * c) (le_trans hc (Nat.le_mul_of_pos_left c hN))
  exact (cohOn.mapIso (Γ(Y, ⊤)) ⊤ j iso).toEquiv.subsingleton

end GlobalTheory
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.PassageDown

theorem exists_cover_of_isCompact {X : Scheme.{0}} {H : LB X} (h : IsAmpleLB H) {V : X.Opens}
    (hV : IsCompact (V : Set X)) : ∃ (r : ℕ) (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec),
      (∀ a, 0 < e a) ∧ (∀ a, IsAffineOpen (nonzeroLocus (σ a))) ∧ ⨆ a, nonzeroLocus (σ a) = V := by
  classical
  have key : ∀ x : V, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : (lbPow H n).Sec, (x : X) ∈ nonzeroLocus s ∧
      nonzeroLocus s ≤ V ∧ IsAffineOpen (nonzeroLocus s) := fun x => h.exists_affine_le x.2
  choose n hn s hxs hsV hsA using key
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover (fun x : V => (nonzeroLocus (s x) : Set X))
    (fun x => (nonzeroLocus (s x)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxs _⟩)
  refine ⟨t.card, fun a => n (t.equivFin.symm a), fun a => s (t.equivFin.symm a),
    fun a => hn _, fun a => hsA _, ?_⟩
  apply le_antisymm
  · exact iSup_le fun a => hsV _
  · intro y hy
    have hy' := ht hy
    simp only [Set.mem_iUnion] at hy'
    obtain ⟨i, hi, hyi⟩ := hy'
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨j, hj⟩ : ∃ j, t.equivFin.symm j = ⟨i, hi⟩ := ⟨_, Equiv.symm_apply_apply _ _⟩
    refine ⟨j, ?_⟩
    show y ∈ nonzeroLocus (s ↑(t.equivFin.symm j))
    rw [hj]
    exact hyi

end GlobalTheory.PassageDown

private theorem passage_cohOn_lemma {X Y : Scheme.{0}} (s : Y ⟶ X) (F : Y.Modules) (V : X.Opens)
    {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hV : V ≤ ⨆ i, U i)
    (hP : CechAcyclicMod V U ((Scheme.Modules.pushforward s).obj F))
    (hF : CechAcyclicMod (s ⁻¹ᵁ V) (fun i => s ⁻¹ᵁ U i) F) (n : ℕ) :
    Nonempty (cohOn ((Scheme.Modules.pushforward s).obj F) V n ≃+ cohOn F (s ⁻¹ᵁ V) n) := by
  have hV' : s ⁻¹ᵁ V ≤ ⨆ i, s ⁻¹ᵁ U i := by
    intro y hy
    have hy' := hV hy
    rw [TopologicalSpace.Opens.mem_iSup] at hy' ⊢
    exact hy'
  let φ := cechCubePushforwardIso V U (R := ℤ) F (g := s) (fun r => by simp)
  haveI : IsIso (cechComplexMap φ.hom) :=
    isIso_cechComplexMap _ (fun t _ => ConcreteCategory.bijective_of_isIso (φ.hom.app t))
  let e1 := cechAbHEquivH' hV (cechAcyclicMod_iff.1 hP) n
  let e2 := cechAbHEquivH' hV' (cechAcyclicMod_iff.1 hF) n
  let e3 := cechAbHEquiv ℤ ((Scheme.Modules.pushforward s).obj F) V U n
  let e4 := cechAbHEquiv ℤ F (s ⁻¹ᵁ V) (fun i => s ⁻¹ᵁ U i) n
  let e5 := (HomologicalComplex.homologyMapIso (asIso (cechComplexMap φ.hom)) n).toLinearEquiv.toAddEquiv
  exact ⟨e1.symm.trans (e3.trans (e5.trans (e4.symm.trans e2)))⟩

theorem GlobalTheory.passage_down_of_twist_vanishing : ∀ (X Y : Scheme.{0}) [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), IsAmpleLB H → (∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → (∀ i, Nonempty (coh ((Scheme.Modules.pushforward s).obj F) i ≃+ coh F i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn F (s ⁻¹ᵁ U) j) := by
  intro X Y _ _ _ _ s F _ H hH hvan
  haveI : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pushforward s).obj F) :=
    GlobalTheory.QCoh.isQuasicoherent_pushforward s F
  have key : ∀ V : X.Opens, IsCompact (V : Set X) → ∀ n,
      Nonempty (cohOn ((Scheme.Modules.pushforward s).obj F) V n ≃+ cohOn F (s ⁻¹ᵁ V) n) := by
    intro V hV n
    obtain ⟨r, e, σ, he, hA, hcov⟩ := GlobalTheory.PassageDown.exists_cover_of_isCompact hH hV
    have hle : ∀ a, nonzeroLocus (σ a) ≤ V := fun a => hcov ▸ le_iSup (fun a => nonzeroLocus (σ a)) a
    have hint : ∀ t : Finset (Fin r), t.Nonempty → IsAffineOpen (⨅ a ∈ t, nonzeroLocus (σ a)) :=
      fun t ht => GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated (R := Γ(X, ⊤)) X.toSpecΓ hA t ht
    apply passage_cohOn_lemma s F V (fun a => nonzeroLocus (σ a)) hcov.ge
    · exact cechAcyclicMod_of_isAffineOpen (isAffineOpen_cechOpen_of_le hle hint) _
    · intro t ht q
      rw [← preimage_cechOpen, cechOpen_of_nonempty hle ht]
      exact subsingleton_cohOn_preimage_iInf_nonzeroLocus X Y s F H hH.isLB (q + 1)
        (hvan _ (Nat.succ_pos q)) r e σ he t ht
  refine ⟨fun i => ?_, fun U hU j hj => ?_⟩
  · obtain ⟨f⟩ := key ⊤ (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ) i
    exact ⟨f⟩
  · obtain ⟨f⟩ := key U hU.isCompact j
    haveI : Subsingleton (cohOn ((Scheme.Modules.pushforward s).obj F) U j) := by
      refine subsingleton_cohOn_of_cechAcyclic (ι := Unit) (U := fun _ => U)
        (le_iSup (fun _ : Unit => U) ()) ?_ (by rw [Fintype.card_unit]; exact hj)
      refine cechAcyclicMod_of_isAffineOpen (isAffineOpen_cechOpen_of_le (fun _ => le_rfl) ?_) _
      intro t ht
      obtain ⟨i, hi⟩ := ht
      rwa [show (⨅ _ ∈ t, U) = U from le_antisymm (biInf_le _ hi) (le_iInf₂ fun _ _ => le_rfl)]
    exact f.symm.toEquiv.subsingleton
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.pushforward_cohomology_affine : ∀ (X Y : Scheme.{0}) [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), IsAmpleLB H → (∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → (∀ i, Nonempty (coh ((Scheme.Modules.pushforward s).obj F) i ≃+ coh F i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn F (s ⁻¹ᵁ U) j) := by
  atlas_forward_decl _root_.GlobalTheory.passage_down_of_twist_vanishing
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.ample_add_nef_is_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (A N P : LB X) (hA : IsAmpleLB A) (hN : letI := algebraΓOfHom p; IsNef k N) (hP : P.IsLB), cls P hP = cls A hA.isLB + cls N (letI := algebraΓOfHom p; hN.isLB) → IsAmpleLB P := by
  first | exact @_root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | exact _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | (intros; apply _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem subring_subtype_flat {k : Type} [Field k] (R : Subring k) : R.subtype.Flat := by
  have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).2 R.subtype_injective
  let _ := FractionRing.liftAlgebra R k
  have := FractionRing.isScalarTower_liftAlgebra R k
  have h1 : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
  have h2 : Module.Flat R k := Module.Flat.trans R (FractionRing R) k
  exact (RingHom.flat_algebraMap_iff (R := R) (S := k)).2 h2

theorem resG_cstOn_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (c : R) : resG X h (cstOn p U c) = cstOn p V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫
    X.presheaf.map (homOfLE h).op).hom c = _
  erw [Scheme.Hom.appLE_map]
  rfl

theorem app_cstOn_const {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (j : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (h : V ≤ j ⁻¹ᵁ U) (c : R) :
    resG Y h ((j.app U).hom (cstOn p U c)) = cstOn (j ≫ p) V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫ j.appLE U V h).hom c = _
  exact congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom c)
    (Scheme.Hom.appLE_comp_appLE j p ⊤ U V le_top h)

theorem cstOn_comp_spMap_const {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}}
    (p : X ⟶ Sp R') (U : X.Opens) (c : R) : cstOn (p ≫ spMap φ) U c = cstOn p U (φ c) := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p ≫ spMap φ).appLE ⊤ U le_top =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p.appLE ⊤ U le_top := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    erw [Scheme.Hom.comp_appLE]
    rfl
  exact congrArg (fun g => g.hom c) e

def secComb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {n : ℕ}
    (c : Fin n → R) (τ : Fin n → L.Sec) : L.Sec where
  f i := ∑ a, cstOn p _ (c a) * (τ a).f i
  compat i j := by
    change resG X _ _ = _ * resG X _ _
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_mul, resG_cstOn_const, resG_cstOn_const, mul_left_comm]
    exact congrArg _ ((τ a).compat i j)

theorem resG_comb_pull {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X X₁ X₀ : Scheme.{0}}
    (f : X ⟶ Sp R') (f₁ : X₁ ⟶ Sp R) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁) (hf : j ≫ f₁ = f ≫ spMap φ)
    {n : ℕ} (c : Fin n → R) {U₀ : X₀.Opens} (t : Fin n → Γ(X₀, U₀)) {U₁ : X₁.Opens} {V V' W : X.Opens}
    (h₁ : U₁ ≤ π₁ ⁻¹ᵁ U₀) (hV : V ≤ j ⁻¹ᵁ U₁) (hV' : V' ≤ (j ≫ π₁) ⁻¹ᵁ U₀) (hW' : W ≤ V') (hW : W ≤ V) :
    resG X hW' (∑ a, cstOn f V' (φ (c a)) * resG X hV' (((j ≫ π₁).app U₀).hom (t a))) =
      resG X hW (resG X hV ((j.app U₁).hom
        (∑ a, cstOn f₁ U₁ (c a) * resG X₁ h₁ ((π₁.app U₀).hom (t a))))) := by
  rw [Cartier.resG_resG, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, map_mul, app_cstOn_const, resG_cstOn_const, hf, cstOn_comp_spMap_const,
    Cartier.app_resG, Cartier.resG_resG, Cartier.resG_resG]
  rfl

theorem exists_finset_sec_descends : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  classical
  intro k _ R₀ X X₀ f f₀ π _ L σ hπ hL
  obtain ⟨n, c, τ, hσ⟩ := GlobalTheory.T.flat_base_change_sections R₀ k R₀.subtype X₀ X f₀ f π L (subring_subtype_flat R₀) hπ hL σ
  refine ⟨Finset.univ.image c, fun R₁ hR hF X₁ f₁ π₁ j _ hj hf => ?_⟩
  subst hj
  let c₁ : Fin n → R₁ := fun a => ⟨c a, hF (by simp)⟩
  refine ⟨secComb f₁ c₁ fun a => Cartier.secPull (τ a) π₁, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ ((j ≫ π₁) x)))
  have h1 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ (L.pull (j ≫ π₁)).U fun _ => i := (Cartier.pull_U L _ fun _ => i).ge
  have h2 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ ((L.pull π₁).pull j).U fun _ _ => i :=
    (j.preimage_mono (Cartier.pull_U L π₁ fun _ => i).ge).trans
      (Cartier.pull_U (L.pull π₁) j fun _ _ => i).ge
  refine ⟨(j ≫ π₁) ⁻¹ᵁ L.U i, fun _ => i, fun _ _ => i, h1, h2, 1, hi, ?_⟩
  refine Eq.trans ?_ (one_mul _).symm
  refine (congrArg (resG X h1) (hσ fun _ => i)).trans ?_
  exact resG_comb_pull R₁.subtype f f₁ π₁ j hf c₁ (fun a => (τ a).f i)
    (Cartier.pull_U L π₁ fun _ => i).le (Cartier.pull_U (L.pull π₁) j fun _ _ => i).le
    (Cartier.pull_U L (j ≫ π₁) fun _ => i).le h1 h2

end GlobalTheory.LogPair
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_line_bundle : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  atlas_forward_decl _root_.GlobalTheory.LogPair.exists_finset_sec_descends
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SecDescent

theorem lbSec_descends_to_subring : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X) (hL : L.IsLB) (σ : L.Sec), IsPullback π f f₀ (spMap R₀.subtype) → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ (L₁ : LB X₁) (h₁ : L₁.IsLB) (σ₁ : L₁.Sec), cls L hL = CechPic.pull j (cls L₁ h₁) ∧ SameDiv σ (Cartier.secPull σ₁ j) := by
  intro k _ R₀ X X₀ f f₀ π _ L hL σ hp
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring k R₀ X X₀ f f₀ π L hp hL
  let R' : Subring k := R₀ ⊔ Subring.closure (S : Set k)
  have h' : R₀ ≤ R' := le_sup_left
  have hs' : (S : Set k) ⊆ R' := fun x hx => (le_sup_right : _ ≤ R') (Subring.subset_closure hx)
  let a : Sp R' ⟶ Sp R₀ := spMap (Subring.inclusion h')
  have e₁ : spMap R'.subtype ≫ a = spMap R₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have PX' := IsPullback.of_hasPullback f₀ a
  let j' : X ⟶ pullback f₀ a := PX'.lift π (f ≫ spMap R'.subtype) (by rw [Category.assoc, e₁, hp.w])
  have hj₁ : j' ≫ pullback.fst f₀ a = π := PX'.lift_fst _ _ _
  have hj₂ : j' ≫ pullback.snd f₀ a = f ≫ spMap R'.subtype := PX'.lift_snd _ _ _
  obtain ⟨L', hL', hI⟩ := hS R' h' hs' _ _ _ j' PX' hj₁ hj₂
  have hLj : (L'.pull j').IsLB := LB.isLB_pull hL' j'
  obtain ⟨τ, hστ⟩ := GlobalTheory.T.exists_sectionsHaveSameZeroScheme_of_lineBundleIso X L (L'.pull j') σ hL hLj hI
  have QX : IsPullback j' f (pullback.snd f₀ a) (spMap R'.subtype) :=
    IsPullback.of_right (by rw [hj₁, e₁]; exact hp) hj₂ PX'
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.spread_out_line_bundle k R' X (pullback f₀ a) f (pullback.snd f₀ a) j' L' τ QX hL'
  refine ⟨S ∪ F₂, fun R₁ hR hs X₁ f₁ π₁ j hp₁ hjπ hjf => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hs
  have hle : R' ≤ R₁ := sup_le hR (Subring.closure_le.2 hs.1)
  let b : Sp R₁ ⟶ Sp R' := spMap (Subring.inclusion hle)
  have e₂ : b ≫ a = spMap (Subring.inclusion hR) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have e₃ : spMap R₁.subtype ≫ b = spMap R'.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let q : X₁ ⟶ pullback f₀ a := PX'.lift π₁ (f₁ ≫ b) (by rw [Category.assoc, e₂, hp₁.w])
  have hq₁ : q ≫ pullback.fst f₀ a = π₁ := PX'.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd f₀ a = f₁ ≫ b := PX'.lift_snd _ _ _
  have QX₁ : IsPullback q f₁ (pullback.snd f₀ a) b :=
    IsPullback.of_right (by rw [hq₁, e₂]; exact hp₁) hq₂ PX'
  have hjq : j ≫ q = j' := by
    apply PX'.hom_ext
    · rw [Category.assoc, hq₁, hjπ, hj₁]
    · rw [Category.assoc, hq₂, reassoc_of% hjf, e₃, hj₂]
  obtain ⟨τ₁, hτ₁⟩ := hF₂ R₁ hle hs.2 X₁ f₁ q j QX₁ hjq hjf
  refine ⟨L'.pull q, LB.isLB_pull hL' q, τ₁, ?_, GlobalTheory.T.same_divisor_trans X L (L'.pull j') _ σ τ _ hLj hστ hτ₁⟩
  rw [(CechPic.cls_eq_iff hL hLj).2 hI, CechPic.cls_pull hL' j' hLj, CechPic.cls_pull hL' q, ← hjq,
    CechPic.pull_comp]

end GlobalTheory.SecDescent
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_line_bundle_section : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X) (hL : L.IsLB) (σ : L.Sec), IsPullback π f f₀ (spMap R₀.subtype) → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ (L₁ : LB X₁) (h₁ : L₁.IsLB) (σ₁ : L₁.Sec), cls L hL = CechPic.pull j (cls L₁ h₁) ∧ SameDiv σ (Cartier.secPull σ₁ j) := by
  atlas_forward_decl _root_.GlobalTheory.SecDescent.lbSec_descends_to_subring
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_finiteType_subring_ge_finset {k : Type} [CommRing k] (R₀ : Subring k)
    (h : Algebra.FiniteType ℤ R₀) (F : Finset k) :
    ∃ R : Subring k, R₀ ≤ R ∧ (F : Set k) ⊆ R ∧ Algebra.FiniteType ℤ R := by
  have h0 : (subalgebraOfSubring R₀).FG := (Subalgebra.fg_iff_finiteType _).2 h
  have h1 : (subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).FG :=
    h0.sup (Subalgebra.fg_adjoin_finset F)
  refine ⟨(subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).toSubring, ?_, ?_,
    (Subalgebra.fg_iff_finiteType _).1 h1⟩
  · intro x hx
    exact (le_sup_left : subalgebraOfSubring R₀ ≤ _) hx
  · intro x hx
    exact (le_sup_right : Algebra.adjoin ℤ (F : Set k) ≤ _) (Algebra.subset_adjoin hx)

theorem exists_model_with_sections : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  classical
  intro k _ X f hsm hpr s L σ h M hM
  obtain ⟨R₀, X₀, f₀, π₀, hft, hsm₀, hpr₀, hpb⟩ := GlobalTheory.T.exists_smooth_proper_model_finitelyGenerated_subring k X f hsm hpr
  choose F hF using fun i => GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ (L i) (h i) (σ i) hpb
  obtain ⟨G, hG⟩ := GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ M hM 0 hpb
  obtain ⟨R, hR, hFR, hRft⟩ :=
    exists_finiteType_subring_ge_finset R₀ hft (G ∪ Finset.univ.biUnion F)
  have hsp : spMap R.subtype ≫ spMap (Subring.inclusion hR) = spMap R₀.subtype := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have P := IsPullback.of_hasPullback f₀ (spMap (Subring.inclusion hR))
  let j : X ⟶ pullback f₀ (spMap (Subring.inclusion hR)) :=
    pullback.lift π₀ (f ≫ spMap R.subtype) (by rw [Category.assoc, hsp, hpb.w])
  have hj1 : j ≫ pullback.fst _ _ = π₀ := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd _ _ = f ≫ spMap R.subtype := pullback.lift_snd _ _ _
  have hGR : (G : Set k) ⊆ R := fun x hx => hFR (by
    simp only [Finset.coe_union, Set.mem_union]; exact Or.inl hx)
  have hFi : ∀ i, (F i : Set k) ⊆ R := fun i x hx => hFR (by
    rw [Finset.mem_coe, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
  choose L₁ h₁ σ₁ hc hd using fun i => hF i R hR (hFi i) _ _ _ j P hj1 hj2
  obtain ⟨M₁, hM₁, -, hMc, -⟩ := hG R hR hGR _ _ _ j P hj1 hj2
  refine ⟨R, _, pullback.snd f₀ (spMap (Subring.inclusion hR)), j, L₁, σ₁, h₁, M₁, hM₁, hRft,
    inferInstance, inferInstance, ?_, hc, hd, hMc⟩
  exact IsPullback.of_right (by rw [hj1, hsp]; exact hpb) hj2 P

end GlobalTheory.LogPair
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_smooth_proper : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  atlas_forward_decl _root_.GlobalTheory.LogPair.exists_model_with_sections
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.ChartDesc

theorem resG_etale (X : Scheme.{0}) (U W : X.Opens) (h : W ≤ U) (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : (resG X h).Etale := by
  have := HasRingHomProperty.appLE (P := @Etale) (𝟙 X) (inferInstanceAs (Etale (𝟙 X))) ⟨U, hU⟩
    ⟨W, hW⟩ (by simpa using h)
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] at this
  exact this

theorem chart_desc : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π)) (y : X'), IsPullback π f' f (spMap φ) → y ∈ C'.U → ∃ C : SncChart f d L σ, π y ∈ C.U := by
  intro R R' _ _ φ X X' f f' π _ d s L σ C' y H hy
  let c : ∀ i, (L i).ι := fun i => C'.c i ⟨⟩
  have hyc : ∀ i, π y ∈ (L i).U (c i) := fun i => by
    exact (Cartier.pull_U (L i) π (C'.c i)).le (C'.le i hy)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_iInter.2 hyc) (isOpen_iInter_of_finite fun i => ((L i).U (c i)).isOpen)
  have hc : ∀ i, (U : X.Opens) ≤ (L i).U (c i) := fun i _ hz => Set.mem_iInter.1 (hUle hz) i
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((C'.U ⊓ π ⁻¹ᵁ U : X'.Opens) : Set X') from ⟨hy, hxU⟩) (C'.U ⊓ π ⁻¹ᵁ U).isOpen
  have hWC : (W : X'.Opens) ≤ C'.U := fun _ hz => (hWle hz).1
  have hWU : (W : X'.Opens) ≤ π ⁻¹ᵁ U := fun _ hz => (hWle hz).2

  have hA : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (Qcqs.baseRingHom f U) (CommRingCat.ofHom φ) (π.app U)
      (Qcqs.baseRingHom f' (π ⁻¹ᵁ U)) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Qcqs.baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [Qcqs.baseRingHom]
  let K := X'.residueField y
  letI : Algebra R R' := φ.toAlgebra
  letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra
  letI : Algebra R' Γ(X', π ⁻¹ᵁ U) := (cstOn f' (π ⁻¹ᵁ U)).toAlgebra
  letI : Algebra Γ(X, U) Γ(X', π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  letI : Algebra R Γ(X', π ⁻¹ᵁ U) := ((cstOn f' (π ⁻¹ᵁ U)).comp φ).toAlgebra
  letI : Algebra Γ(X', π ⁻¹ᵁ U) Γ(X', W) := (resG X' hWU).toAlgebra
  letI : Algebra R' Γ(X', W) := (cstOn f' W).toAlgebra
  letI : Algebra Γ(X', W) K := (X'.evaluation W y hyW).hom.toAlgebra
  letI : Algebra Γ(X, U) K :=
    ((X'.evaluation W y hyW).hom.comp ((resG X' hWU).comp (π.app U).hom)).toAlgebra
  haveI : IsScalarTower R R' Γ(X', π ⁻¹ᵁ U) := .of_algebraMap_eq fun r ↦ rfl
  have e2 : ∀ r : R, (π.app U).hom (cstOn f U r) = cstOn f' (π ⁻¹ᵁ U) (φ r) := fun r => by
    have h1 := Qcqs.app_baseRingHom π f U r
    have h2 : Qcqs.baseRingHom (π ≫ f) (π ⁻¹ᵁ U) r = Qcqs.baseRingHom f' (π ⁻¹ᵁ U) (φ r) := by
      rw [H.w, Qcqs.baseRingHom_comp_SpecMap]; rfl
    exact h1.trans h2
  haveI : IsScalarTower R Γ(X, U) Γ(X', π ⁻¹ᵁ U) := .of_algebraMap_eq fun r ↦ (e2 r).symm
  haveI : Algebra.IsPushout R R' Γ(X, U) Γ(X', π ⁻¹ᵁ U) := by
    have po'' : IsPushout (CommRingCat.ofHom (algebraMap R Γ(X, U))) (CommRingCat.ofHom (algebraMap R R'))
        (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U)))
        (CommRingCat.ofHom (algebraMap R' Γ(X', π ⁻¹ᵁ U))) := po'
    exact (CommRingCat.isPushout_iff_isPushout.mp po'').symm
  haveI : IsScalarTower R' Γ(X', π ⁻¹ᵁ U) Γ(X', W) := .of_algebraMap_eq fun r ↦
    (Qcqs.baseRingHom_res f' hWU r).symm
  haveI : Algebra.FormallyEtale Γ(X', π ⁻¹ᵁ U) Γ(X', W) := by
    haveI : Algebra.Etale Γ(X', π ⁻¹ᵁ U) Γ(X', W) := resG_etale X' _ _ hWU hU' hW
    infer_instance

  let t : Fin d → Γ(X', W) := fun a => resG X' hWC (C'.t a)
  have ht : IsEtCoord f' W t := GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen R' X' f' C'.U W hWC d C'.t C'.affine hW C'.etale
  have hbasis := GlobalTheory.T.etale_coordinates_differentials R' Γ(X', W) K d t ht
  obtain ⟨ebc, hebc⟩ := GlobalTheory.T.exists_kaehler_fibre_equiv_D_compat R R' Γ(X, U) Γ(X', π ⁻¹ᵁ U) Γ(X', W) K (fun _ => rfl)
  have key : ∀ i, algebraMap Γ(X', π ⁻¹ᵁ U) Γ(X', W)
      (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U) (resG X (hc i) ((σ i).f (c i)))) =
      ((Units.map (resG X' hWC).toMonoidHom (C'.u i) : Γ(X', W)ˣ) : Γ(X', W)) *
        resG X' hWC ((C'.e i).elim 1 C'.t) := by
    intro i
    have e := congrArg (resG X' hWC) (C'.eq i)
    rw [map_mul] at e
    refine Eq.trans ?_ e
    show resG X' hWU ((π.app U).hom (resG X (hc i) ((σ i).f (c i)))) =
      resG X' hWC (resG X' (C'.le i) (resG X' _ ((π.app _).hom ((σ i).f (C'.c i ⟨⟩)))))
    rw [Cartier.app_resG, Cartier.resG_resG, Cartier.resG_resG, Cartier.resG_resG]
  have hunit : ∀ v : Γ(X', W)ˣ, algebraMap Γ(X', W) K v ≠ 0 := fun v =>
    (v.isUnit.map (algebraMap Γ(X', W) K)).ne_zero
  have hres : ∀ a : Γ(X, U), algebraMap Γ(X, U) K a ≠ 0 ↔ π y ∈ X.basicOpen a := by
    intro a
    change (X'.evaluation W y hyW).hom (resG X' hWU ((π.app U).hom a)) ≠ 0 ↔ _
    rw [Ne, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]
    change y ∈ X'.basicOpen ((X'.presheaf.map (homOfLE hWU).op).hom _) ↔ _
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact ⟨fun h => h.2, fun h => ⟨hyW, h⟩⟩
  have hrank : Module.finrank K (K ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d :=
    ebc.finrank_eq.trans hbasis.1
  have hvan : ∀ i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0},
      ∃ a, C'.e i.1 = some a ∧ algebraMap Γ(X', W) K (t a) = 0 := by
    rintro ⟨i, hi⟩
    have h0 : algebraMap Γ(X', W) K (algebraMap Γ(X', π ⁻¹ᵁ U) Γ(X', W)
        (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U) (resG X (hc i) ((σ i).f (c i))))) = 0 := hi
    rw [key i, map_mul] at h0
    rcases hE : C'.e i with _ | a
    · rw [hE] at h0
      simp only [Option.elim, map_one, mul_one] at h0
      exact absurd h0 (hunit _)
    · refine ⟨a, rfl, ?_⟩
      rw [hE] at h0
      exact (mul_eq_zero.1 h0).resolve_left (hunit _)
  choose g hg hg0 using hvan
  let emb : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} ↪ Fin d :=
    ⟨g, fun i j hij => Subtype.ext (C'.inj i.1 j.1 (g i) (hg i) (by rw [hij]; exact hg j))⟩
  let u : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} → Γ(X', W)ˣ :=
    fun i => Units.map (resG X' hWC).toMonoidHom (C'.u i.1)
  have hli := hbasis.2 _ emb u hg0
  have hfam : ∀ i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0},
      ebc ((1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i.1) ((σ i.1).f (c i.1)))) =
      (1 : K) ⊗ₜ[Γ(X', W)] KaehlerDifferential.D R' Γ(X', W) ((u i : Γ(X', W)) * t (emb i)) := by
    intro i
    rw [hebc, key i.1, hg i]
    rfl
  have hlin : LinearIndependent K (fun i : {i : Fin s // algebraMap Γ(X, U) K
      (resG X (hc i) ((σ i).f (c i))) = 0} =>
      (1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i.1) ((σ i.1).f (c i.1)))) := by
    refine LinearIndependent.of_comp ebc.toLinearMap ?_
    convert hli using 1
    funext i
    exact hfam i
  exact GlobalTheory.T.finrank_kaehler_affine_chart R X f d s L σ U c hc (π y) K hU hxU hres ⟨hrank, hlin⟩

end GlobalTheory.ChartDesc
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.snc_chart_descends : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π)) (y : X'), IsPullback π f' f (spMap φ) → y ∈ C'.U → ∃ C : SncChart f d L σ, π y ∈ C.U := by
  atlas_forward_decl _root_.GlobalTheory.ChartDesc.chart_desc
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.LogPair.relSnc_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  intro R k _ _ φ X X' f f' π _ _ d s L σ hpb hL hrel
  let W : X.Opens := ⨆ C : SncChart f d L σ, C.U
  have hW : π ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun y _ => ?_
    obtain ⟨C', hC'⟩ := hrel.chart y
    obtain ⟨C, hC⟩ := GlobalTheory.T.snc_chart_descends R k φ X X' f f' π d s L σ C' y hpb hC'
    show π y ∈ W
    exact (Opens.mem_iSup).2 ⟨C, hC⟩
  obtain ⟨a, ha, h⟩ := GlobalTheory.T.universallyClosed_open_containing_fibre_contains_nearby R k φ X X' f f' π W hpb hW
  refine ⟨a, ha, fun T _ χ hχ Z g ρ hρ => ?_⟩
  have hZ := h T χ hχ Z g ρ hρ
  refine ⟨fun i => LB.isLB_pull (hL i) ρ, fun z => ?_⟩
  have hz : ρ z ∈ W := by
    have : z ∈ ρ ⁻¹ᵁ W := by rw [hZ]; trivial
    exact this
  obtain ⟨C, hC⟩ := (Opens.mem_iSup).1 hz
  obtain ⟨C', hC'⟩ := GlobalTheory.T.snc_chart_base_change R T χ X Z f g ρ d s L σ C hρ
  refine ⟨C', ?_⟩
  rw [hC']
  exact hC
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_generic_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  atlas_forward_decl _root_.GlobalTheory.LogPair.relSnc_spread
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ModelSnc

def adjInv {k : Type} [Field k] (R : Subring k) (a : k) : Subring k :=
  (Polynomial.eval₂RingHom R.subtype a⁻¹).range

def toAdjInv {k : Type} [Field k] (R : Subring k) (a : k) : R →+* adjInv R a :=
  (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict.comp Polynomial.C

theorem subtype_comp_toAdjInv {k : Type} [Field k] (R : Subring k) (a : k) :
    (adjInv R a).subtype.comp (toAdjInv R a) = R.subtype := by
  ext r
  change Polynomial.eval₂ R.subtype a⁻¹ (Polynomial.C r) = (r : k)
  simp

theorem isUnit_toAdjInv {k : Type} [Field k] (R : Subring k) (a : R) (ha : (a : k) ≠ 0) :
    IsUnit (toAdjInv R (a : k) a) := by
  refine IsUnit.of_mul_eq_one ((Polynomial.eval₂RingHom R.subtype (a : k)⁻¹).rangeRestrict Polynomial.X) ?_
  apply Subtype.ext
  change Polynomial.eval₂ R.subtype (a : k)⁻¹ (Polynomial.C a) * Polynomial.eval₂ R.subtype (a : k)⁻¹ Polynomial.X = 1
  simp [ha]

theorem finiteType_adjInv {k : Type} [Field k] (R : Subring k) (hR : Algebra.FiniteType ℤ R) (a : k) :
    Algebra.FiniteType ℤ (adjInv R a) := by
  haveI := hR
  have hP : Algebra.FiniteType ℤ (Polynomial R) := inferInstance
  exact @Algebra.FiniteType.of_surjective _ _ _ _ _ _ _ _ hP
    (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict.toIntAlgHom
    (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict_surjective

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.ModelSnc

end

namespace GlobalTheory.ModelSnc

theorem exists_model_relSnc : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ), IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : RelSnc f₁ d L₁ σ₁) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h.isLB i) = CechPic.pull π (cls (L₁ i) (h₁.isLB i))) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  intro k _ X f d hf s L σ h M hM
  haveI : SmoothOfRelativeDimension d f := GlobalTheory.T.smoothOfRelativeDimension_of_relSncDivisor k X f d s L σ h
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth d f
  obtain ⟨R, X₁, f₁, π, L₁, σ₁, h₁, M₁, hM₁, hR, hsm₁, hpr₁, hpb, hcl, hsame, hclM⟩ :=
    GlobalTheory.T.spread_out_smooth_proper k X f hsm hf s L σ h.isLB M hM
  have hX : RelSnc f d (fun i => (L₁ i).pull π) (fun i => Cartier.secPull (σ₁ i) π) :=
    GlobalTheory.T.relative_snc_same_divisor k X f d s L σ _ _ h (fun i => pull_isLB (h₁ i) π) hsame
  haveI := hsm₁
  haveI := hpr₁
  obtain ⟨a, ha, hsp⟩ := GlobalTheory.T.relative_snc_generic_spread R k R.subtype X₁ X f₁ f π d s L₁ σ₁ hpb h₁ hX
  set R' := adjInv R (a : k)
  set χ := toAdjInv R (a : k)
  have hχ : IsUnit (χ a) := isUnit_toAdjInv R a ha
  let g : pullback f₁ (spMap χ) ⟶ Sp R' := pullback.snd f₁ (spMap χ)
  let ρ : pullback f₁ (spMap χ) ⟶ X₁ := pullback.fst f₁ (spMap χ)
  have hρ : IsPullback ρ g f₁ (spMap χ) := IsPullback.of_hasPullback f₁ (spMap χ)
  have hZ := hsp R' χ hχ _ g ρ hρ
  have hcomp : spMap R.subtype = spMap R'.subtype ≫ spMap χ := by
    rw [← spMap_comp, subtype_comp_toAdjInv]
  have hw : π ≫ f₁ = (f ≫ spMap R'.subtype) ≫ spMap χ := by
    rw [Category.assoc, ← hcomp]; exact hpb.w
  let π' : X ⟶ pullback f₁ (spMap χ) := pullback.lift π (f ≫ spMap R'.subtype) hw
  have hπ' : π' ≫ ρ = π := pullback.lift_fst _ _ _
  have hg' : π' ≫ g = f ≫ spMap R'.subtype := pullback.lift_snd _ _ _
  have hpb' : IsPullback π' f g (spMap R'.subtype) := by
    refine IsPullback.of_right ?_ hg' hρ
    rw [hπ', ← hcomp]; exact hpb
  haveI : IsProper g := inferInstance
  refine ⟨R', pullback f₁ (spMap χ), g, π', fun i => (L₁ i).pull ρ, fun i => Cartier.secPull (σ₁ i) ρ, hZ,
    M₁.pull ρ, pull_isLB hM₁ ρ, finiteType_adjInv R hR _, inferInstance, hpb', fun i => ?_, ?_⟩
  · rw [hcl i, ← hπ', pull_comp]; rfl
  · rw [hclM, ← hπ', pull_comp]; rfl

end GlobalTheory.ModelSnc
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_relative_snc : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ), IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : RelSnc f₁ d L₁ σ₁) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h.isLB i) = CechPic.pull π (cls (L₁ i) (h₁.isLB i))) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  atlas_forward_decl _root_.GlobalTheory.ModelSnc.exists_model_relSnc
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair

namespace GlobalTheory.Div

theorem vanishing_ample_snc_charZero : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f], IsProjOver f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro k _ _ X f d _ hproj s L σ h K M A hM hA r b hr hb hcls q hq
  have hprop : IsProper f := GlobalTheory.SchemeWords.isProper_of_isProjOver hproj
  obtain ⟨R, X₁, f₁, π, L₁, σ₁, h₁, M₁, hM₁, hft, hprop₁, hpb, hL, hMc⟩ :=
    GlobalTheory.T.spread_out_relative_snc k X f d hprop s L σ h M hM
  haveI : SmoothOfRelativeDimension d f₁ := GlobalTheory.T.smoothOfRelativeDimension_of_relSncDivisor R X₁ f₁ d s L₁ σ₁ h₁
  haveI : IsProper f₁ := hprop₁
  obtain ⟨K₁⟩ := (CanonLB.nonempty : Nonempty (CanonLB f₁ d))
  obtain ⟨A₁, hA₁, hA₁c⟩ := cls_surj (r • cls M₁ hM₁ - r • cls K₁.bundle K₁.isLB -
    ∑ i, b i • cls (L₁ i) (h₁.isLB i))
  have hK : cls K.bundle K.isLB = CechPic.pull π (cls K₁.bundle K₁.isLB) :=
    GlobalTheory.T.cechPicardClass_canonicalBundle_baseChange R k R.subtype X₁ X f₁ f π d K₁ K hpb
  have hApull : cls (A₁.pull π) (pull_isLB hA₁ π) = cls A hA.isLB := by
    have e : cls A hA.isLB = r • cls M hM - r • cls K.bundle K.isLB - ∑ i, b i • cls (L i) (h.isLB i) := by
      rw [hcls]; abel
    rw [e, cls_pull hA₁, hA₁c, map_sub, map_sub, map_nsmul, map_nsmul, map_sum, ← hMc, ← hK]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, ← hL i]
  have hAamp : IsAmpleLB (A₁.pull π) :=
    IsAmpleLB.of_lbIso hA (pull_isLB hA₁ π) ((cls_eq_iff _ _).1 hApull)
  have hcls₁ : r • cls M₁ hM₁ = r • cls K₁.bundle K₁.isLB + ∑ i, b i • cls (L₁ i) (h₁.isLB i) +
      cls A₁ hA₁ := by
    rw [hA₁c]; abel
  have hv := GlobalTheory.T.kawamata_viehweg_spreading R k R.subtype X₁ X f₁ f π d hft Subtype.coe_injective hpb s L₁ σ₁ h₁ K₁
    M₁ A₁ hM₁ hA₁ r b hAamp hr hb hcls₁ q hq
  have hMM : cls (M₁.pull π) (pull_isLB hM₁ π) = cls M hM := by rw [cls_pull hM₁, hMc]
  exact GlobalTheory.T.cohomology_subsingleton_of_cechPicardClass_eq X (M₁.pull π) M _ hM hMM q hv

end GlobalTheory.Div
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.kawamata_viehweg_vanishing : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f], IsProjOver f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  atlas_forward_decl _root_.GlobalTheory.Div.vanishing_ample_snc_charZero
end

section
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Div.SncBoundary

noncomputable def multHom {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (z : X) :
    CartierDiv X →+ ℤ :=
  AddMonoidHom.mk' (fun D => D.mult z) fun D E => CartierDiv.mult_add D E z

private theorem regAt_of_ord_eq_zero_of_normal {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    {z : X} (hz : Order.coheight z = 1) {f : X.functionField} (hf : f ≠ 0)
    (h0 : Scheme.ord f z = 0) : RegAt z f := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  obtain ⟨hD, hI⟩ := hN z
  have hnf : ¬ IsField (X.presheaf.stalk z) := by
    intro hF
    have h1 := ringKrullDim_stalk_eq_coheight z
    rw [ringKrullDim_eq_zero_of_isField hF, hz] at h1
    norm_num at h1
  haveI : Ring.DimensionLEOne (X.presheaf.stalk z) :=
    ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  have hDD : IsDedekindDomain (X.presheaf.stalk z) :=
    (isDedekindDomain_iff _ X.functionField).mpr
      ⟨hD, inferInstance, inferInstance, fun hx => (isIntegrallyClosed_iff X.functionField).mp hI hx⟩
  have hTF := IsDiscreteValuationRing.TFAE (X.presheaf.stalk z) hnf
  have hV : ValuationRing (X.presheaf.stalk z) := (hTF.out 2 1).mp hDD
  have hord : Ring.ordFrac (X.presheaf.stalk z) f = 1 := by
    have := (Scheme.ord_eq_iff hz hf).1 h0
    simpa [Scheme.ordHom] using this
  rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk z) f with ⟨a, ha⟩ | ⟨r, hr⟩
  · exact ⟨a, ha⟩
  · have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [map_zero] at hr
      exact hf (inv_eq_zero.mp hr.symm)
    have h2 : Ring.ordMonoidWithZeroHom (X.presheaf.stalk z) r = 1 := by
      rw [← Ring.ordFrac_eq_ord (K := X.functionField) _ hr0, hr, map_inv₀, hord, inv_one]
    have hmem : r ∈ nonZeroDivisors (X.presheaf.stalk z) := mem_nonZeroDivisors_of_ne_zero hr0
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hmem)
    rw [Ring.ordMonoidWithZeroHom_eq_coe _ hmem hn.symm] at h2
    have hn1 : Multiplicative.ofAdd (n : ℤ) = 1 := by exact_mod_cast h2
    have hn0 : n = 0 := by
      have : (n : ℤ) = 0 := by simpa using hn1
      exact_mod_cast this
    have h3 : Ring.ord (X.presheaf.stalk z) r = 0 := by rw [← hn, hn0]; rfl
    have hsub : Subsingleton (X.presheaf.stalk z ⧸ Ideal.span {r}) :=
      Module.length_eq_zero_iff.mp h3
    have hu : IsUnit r :=
      Ideal.span_singleton_eq_top.mp (Ideal.Quotient.subsingleton_iff.mp hsub)
    refine ⟨↑hu.unit⁻¹, ?_⟩
    have hm : algebraMap (X.presheaf.stalk z) X.functionField (↑hu.unit⁻¹ : X.presheaf.stalk z) *
        algebraMap (X.presheaf.stalk z) X.functionField r = 1 := by
      rw [← map_mul]
      simp
    rw [hr] at hm
    exact (mul_inv_eq_one₀ hf).1 hm

private theorem cartierDiv_eff_of_mult_eq_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (E : CartierDiv X)
    (h : ∀ z, E.mult z = 0) : E.Eff := by
  haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => (hN x).1, fun x => (hN x).2⟩
  rw [CartierDiv.eff_iff]
  intro x g hg
  apply GlobalTheory.Discrepancy.regAt_of_forall_coheight_eq_one
  intro z hzx hz
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  have hgz : E.IsEqn z g := hU z (hzx.mem_open U.isOpen hxU)
  refine regAt_of_ord_eq_zero_of_normal hN hz g.ne_zero ?_
  rw [← hgz.mult_eq]
  exact h z

private theorem cartierDiv_eq_zero_of_mult_eq_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (E : CartierDiv X)
    (h : ∀ z, E.mult z = 0) : E = 0 := by
  refine CartierDiv.Eff.eq_zero (cartierDiv_eff_of_mult_eq_zero hN E h) (cartierDiv_eff_of_mult_eq_zero hN (-E) fun z => ?_)
  show multHom z (-E) = 0
  rw [map_neg]
  exact neg_eq_zero.mpr (h z)

private theorem cartierDiv_mult_nonneg_of_eff {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {D : CartierDiv X} (hD : D.Eff) (z : X) : 0 ≤ D.mult z := by
  obtain ⟨g, hg⟩ := D.exists_isEqn z
  rw [hg.mult_eq]
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, ha⟩ := CartierDiv.eff_iff.mp hD z g hg
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp only [map_zero] at ha
      exact g.ne_zero ha.symm
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    rw [Scheme.le_ord_iff hz g.ne_zero, ← ha]
    have := Ring.ordFrac_ge_one_of_ne_zero (R := X.presheaf.stalk z) (K := X.functionField) ha0
    simpa [Scheme.ordHom] using this
  · simp [Scheme.ord_eq_zero_of_coheight_neq_one hz]

theorem vanishing_ample_snc_cartier : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Kc : CanonLB q n) (Q A : LB Y) (hQ : Q.IsLB) (hA : IsAmpleLB A) (B : Closeds Y) (Γ : CartierDiv Y) (e : ℕ), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → Γ.Eff → Γ.supp ≤ B → (∀ z, Γ.mult z < e) → e • cls Q hQ = e • cls Kc.bundle Kc.isLB + toPic Γ + cls A hA.isLB → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  intro k _ _ Y _ _ q n _ hp Kc Q A hQ hA B Γ e hB hΓ hsupp hmult heq i hi
  have hsm : Smooth q := SmoothOfRelativeDimension.smooth (n := n) (f := q)
  obtain ⟨-, hN, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y q hsm
  obtain ⟨r, w, D, σ, hw, hD, hBw, hrel⟩ := SncComp.relSnc_components k Y q n hp B hB
  have hnn : ∀ z, 0 ≤ Γ.mult z := cartierDiv_mult_nonneg_of_eff hΓ
  let b : Fin r → ℕ := fun j => (Γ.mult (w j)).toNat
  have hdec : Γ = ∑ j, b j • D j := by
    refine sub_eq_zero.mp (cartierDiv_eq_zero_of_mult_eq_zero hN _ fun z => ?_)
    show multHom z (Γ - ∑ j, b j • D j) = 0
    rw [map_sub, map_sum]
    simp only [map_nsmul]
    show Γ.mult z - ∑ j, b j • (D j).mult z = 0
    by_cases hz : ∃ j, z = w j
    · obtain ⟨j, rfl⟩ := hz
      rw [Finset.sum_eq_single j]
      · rw [(hD j).1]
        simp only [b, nsmul_eq_mul, mul_one]
        have := hnn (w j)
        omega
      · intro l _ hl
        rw [(hD l).2 (w j) (fun h => hl (hw h.symm)), smul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    · push_neg at hz
      rw [Finset.sum_eq_zero fun j _ => by rw [(hD j).2 z (hz j), smul_zero], sub_zero]
      by_contra hne
      obtain ⟨j, hj⟩ := hBw z (CartierDiv.coheight_eq_one_of_mult_ne_zero hne)
        (hsupp (CartierDiv.mem_supp_of_mult_ne_zero hne))
      exact hz j hj
  have he : 0 < e := by
    have h1 := hmult (genericPoint Y)
    have h2 := hnn (genericPoint Y)
    omega
  have hb : ∀ j, b j < e := by
    intro j
    have h1 := hmult (w j)
    have h2 := hnn (w j)
    simp only [b]
    omega
  rw [hdec, map_sum] at heq
  simp only [map_nsmul, toPic_apply] at heq
  exact GlobalTheory.Div.vanishing_ample_snc_charZero k Y q n hp r (fun j => toLB (D j)) σ hrel Kc Q A hQ hA
    e b he hb heq i hi

end GlobalTheory.Div.SncBoundary
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.snc_boundary_ample_decomposition : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Kc : CanonLB q n) (Q A : LB Y) (hQ : Q.IsLB) (hA : IsAmpleLB A) (B : Closeds Y) (Γ : CartierDiv Y) (e : ℕ), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → Γ.Eff → Γ.supp ≤ B → (∀ z, Γ.mult z < e) → e • cls Q hQ = e • cls Kc.bundle Kc.isLB + toPic Γ + cls A hA.isLB → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  atlas_forward_decl _root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogResVanish

open GlobalTheory.Cartier.CartierDiv in
private theorem mult_zero₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    (0 : CartierDiv Y).mult z = 0 := by
  have h := CartierDiv.mult_add (0 : CartierDiv Y) 0 z
  rw [add_zero] at h
  linarith

private theorem mult_nsmul₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (D : CartierDiv Y) (n : ℕ) (z : Y) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero₀]; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

private theorem mult_sub₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (D E : CartierDiv Y) (z : Y) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  linarith

private theorem eff_nsmul {Y : Scheme.{0}} [IsIntegral Y] {D : CartierDiv Y} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

private theorem supp_nsmul_le {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) (n : ℕ) :
    (n • D).supp ≤ D.supp := by
  induction n with
  | zero => rw [zero_nsmul, (CartierDiv.supp_eq_bot_iff).2 rfl]; exact bot_le
  | succ n ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

private theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

end GlobalTheory.LogResVanish

open GlobalTheory.LogResVanish in

theorem GlobalTheory.Discrepancy.vanishing_logRes_floor : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ (Q : LB Y) (hQ : Q.IsLB), cls Q hQ = CechPic.pull s (cls N hN) - toPic F → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm h hF N M T hN hM r hT hr hTc hMn a Fd A hA hAF Q hQ hQc i hi
  obtain ⟨ha, hFd, hFdB, hAc⟩ := hAF
  have hTlb : T.IsLB := by letI := algebraΓOfHom p; exact hT.isLB
  haveI := h.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.isNormalScheme_of_smooth (s ≫ p)
  haveI : CompactSpace Y := compactSpace_of_projOver h.proj
  haveI : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'

  set Γ := pullCart s G - m • K with hΓ
  set R := Γ - m • F with hR
  have hRm : ∀ z, R.mult z = Γ.mult z % (m : ℤ) := fun z => by
    rw [hR, mult_sub₀, mult_nsmul₀, hF z, Int.emod_def]
  have hR0 : ∀ z, 0 ≤ R.mult z := fun z => (hRm z).symm ▸ Int.emod_nonneg _ hm0
  have hRlt : ∀ z, R.mult z < m := fun z =>
    (hRm z).symm ▸ Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  have hReff : R.Eff := ((GlobalTheory.T.cartier_divisor_mult_characterize Y R).1).2 hR0
  have hRB : R.supp ≤ B := fun x hx => by
    obtain ⟨z, hzx, hz⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y R).2.1 x).1 hx
    refine h.supp (((GlobalTheory.T.cartier_divisor_mult_characterize Y Γ).2.1 x).2 ⟨z, hzx, fun e => hz ?_⟩)
    rw [hRm, e, Int.zero_emod]

  obtain ⟨b, hab, hb⟩ := GlobalTheory.T.exists_multiple_below_threshold Y R Fd m r a hr hRlt
  set Γ' := (r * b) • R + m • Fd with hΓ'
  have hΓ'eff : Γ'.Eff := (eff_nsmul hReff _).add (eff_nsmul hFd _)
  have hΓ'B : Γ'.supp ≤ B := (CartierDiv.supp_add_le _ _).trans
    (sup_le ((supp_nsmul_le _ _).trans hRB) ((supp_nsmul_le _ _).trans hFdB))

  have hAm : IsAmpleLB (lbPow A m) := (isAmpleLB_pow_iff hA.isLB hm).2 hA
  letI := algebraΓOfHom (s ≫ p)
  have hTp : IsNef k (T.pull s) := GlobalTheory.T.nef_pullback_is_nef k X Y p s hp T hT
  have hMp : IsNef k (M.pull s) := GlobalTheory.T.nef_pullback_is_nef k X Y p s hp M hMn
  obtain ⟨P, hP, hPc⟩ := cls_surj (b • cls (T.pull s) hTp.isLB + (m * (b - a)) • cls (M.pull s) hMp.isLB)
  have hPn : IsNef k P := (hTp.pow hA b).of_cls_eq_add (hMp.pow hA (m * (b - a))) hA hP
    (by rw [hPc, cls_lbPow hTp.isLB, cls_lbPow hMp.isLB])
  obtain ⟨A', hA'lb, hA'c⟩ := cls_surj (cls (lbPow A m) hAm.isLB + cls P hPn.isLB)
  have hA' : IsAmpleLB A' := GlobalTheory.T.ample_add_nef_is_ample k Y (s ≫ p) h.proj (lbPow A m) P A' hAm hPn hA'lb hA'c

  let Kc := CanonLB.all (s ≫ p) n
  have hne : EtaleKlt.ratPull p s n η ≠ 0 := fun e =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s h.bir n).1 (e.trans (map_zero _).symm))
  have hK : toPic K = cls Kc.bundle Kc.isLB := (GlobalTheory.T.canonical_divisor_of_form k Y (s ≫ p) n _ hne).2 K h.div Kc
  refine GlobalTheory.T.snc_boundary_ample_decomposition k Y (s ≫ p) n h.proj Kc Q A' hQ hA' B Γ' (m * r * b) h.snc hΓ'eff hΓ'B hb ?_ i hi

  rw [hA'c, cls_lbPow hA.isLB, hPc, cls_pull hTlb, cls_pull hM, hTc, ← hK, hQc]
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  have e1 : toPic Γ' = (r * (a + c)) • (toPic (pullCart s G) - m • toPic K - m • toPic F) +
      m • toPic Fd := by
    rw [hΓ', hR, hΓ]; simp only [map_add, map_nsmul, map_sub]
  have e2 : m • toPic Fd = m • (a • CechPic.pull s (cls M hM) - cls A hA.isLB) := by
    rw [hAc, add_sub_cancel_left]
  rw [e1, add_assoc, e2, toPic_pullCart]
  simp only [map_sub, map_nsmul, Nat.add_sub_cancel_left]
  module
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_vanishing_nef_twist : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ (Q : LB Y) (hQ : Q.IsLB), cls Q hQ = CechPic.pull s (cls N hN) - toPic F → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  atlas_forward_decl _root_.GlobalTheory.Discrepancy.vanishing_logRes_floor
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.LogResVanish

theorem isSeparated_of_isProjOver {k : Type} [Field k] {Z : Scheme.{0}} {f : Z ⟶ Sp k}
    (h : IsProjOver f) : Z.IsSeparated := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str k N) := by unfold PSpace.str; infer_instance
  exact ⟨by rw [← terminal.comp_from (i ≫ PSpace.str k N)]; infer_instance⟩

end GlobalTheory.LogResVanish

open GlobalTheory.LogResVanish in

theorem GlobalTheory.vanishing_logRes_pushforward_and_local : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → (∀ i, 0 < i → Subsingleton (coh (twist ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB (-F)))) N) i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn (twist (twist (GlobalTheory.structureModule Y) (toLB (-F))) (N.pull s)) (s ⁻¹ᵁ U) j) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm hres hF N M T hN hM r hT hr hcl hMnef a Fd A hA hAF
  letI := algebraΓOfHom p
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  have hHl : H.IsLB := hH.isLB
  have : CompactSpace X := hH.compactSpace
  have : CompactSpace Y := hA.compactSpace
  have : X.IsSeparated := isSeparated_of_isProjOver hp
  have : Y.IsSeparated := isSeparated_of_isProjOver hres.proj
  have hA0 : (toLB (-F)).IsLB := isLB_toLB _

  have key : ∀ (N' T' : LB X) (hN' : N'.IsLB) (hT' : IsNef k T'),
      cls T' hT'.isLB = (m * r) • cls N' hN' - r • toPic G - m • cls M hM →
      ∀ i, 0 < i → Subsingleton (coh (twist (twist (GlobalTheory.structureModule Y) (toLB (-F))) (N'.pull s)) i) := by
    intro N' T' hN' hT' e i hi
    obtain ⟨Q, hQ, eQ⟩ := cls_surj (CechPic.pull s (cls N' hN') - toPic F)
    have h := GlobalTheory.T.multiplier_vanishing_nef_twist k X p n hp η m G Y s K B F hη hm hres hF N' M T' hN' hM r hT' hr e hMnef
      a Fd A hA hAF Q hQ eQ i hi
    obtain ⟨iso⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule Y) hA0 (pull_isLB hN' s) hQ
      (by rw [eQ, cls_pull hN' s, ← toPic_apply, map_neg]; abel)
    exact (cohOn.mapIso Γ(Y, ⊤) ⊤ i iso).toEquiv.subsingleton_congr.2 h
  have hev : ∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist (twist (twist
      (GlobalTheory.structureModule Y) (toLB (-F))) (N.pull s)) (lbPow (H.pull s) c)) j) := by
    intro j hj
    refine Eventually.of_forall fun c => ?_
    have hNc : (tens N (lbPow H c)).IsLB := isLB_tens hN (isLB_lbPow hHl c)
    have hTc : IsNef k (tens T (lbPow H (m * r * c))) :=
      hT.tens ((IsAmpleLB.isNef (k := k) hH).pow hH _) hH
    have ec : cls _ hTc.isLB = (m * r) • cls _ hNc - r • toPic G - m • cls M hM := by
      rw [cls_tens hT.isLB (isLB_lbPow hHl _), cls_tens hN (isLB_lbPow hHl c), cls_lbPow hHl,
        cls_lbPow hHl, hcl, smul_add, smul_smul]
      abel
    obtain ⟨iso⟩ := nonempty_twist_twist_iso_of_cls_eq
      (twist (GlobalTheory.structureModule Y) (toLB (-F))) (pull_isLB hN s)
      (isLB_lbPow (pull_isLB hHl s) c) (pull_isLB hNc s)
      (by rw [cls_pull hNc s, cls_tens hN (isLB_lbPow hHl c), cls_lbPow hHl, cls_pull hN s,
        cls_lbPow (pull_isLB hHl s), cls_pull hHl s, map_add, map_nsmul])
    exact (cohOn.mapIso Γ(Y, ⊤) ⊤ j iso).toEquiv.subsingleton_congr.2 (key _ _ hNc hTc ec j hj)
  have : (GlobalTheory.structureModule Y).IsQuasicoherent := inferInstance
  have := Twist.isQuasicoherent_twist (F := GlobalTheory.structureModule Y) hA0
  have := Twist.isQuasicoherent_twist (F := twist (GlobalTheory.structureModule Y) (toLB (-F))) (pull_isLB hN s)
  have hdown := GlobalTheory.T.pushforward_cohomology_affine X Y s _ H hH hev
  refine ⟨fun i hi => ?_, hdown.2⟩
  obtain ⟨e⟩ := hdown.1 i
  have h0 := key N T hN hT hcl i hi
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ i (Twist.projIso N s _).symm).toEquiv.subsingleton_congr.2
    (e.toEquiv.subsingleton_congr.2 h0)
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_vanishing_nef_twist_ample : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → (∀ i, 0 < i → Subsingleton (coh (twist ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB (-F)))) N) i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn (twist (twist (GlobalTheory.structureModule Y) (toLB (-F))) (N.pull s)) (s ⁻¹ᵁ U) j) := by
  atlas_forward_decl _root_.GlobalTheory.vanishing_logRes_pushforward_and_local
end
