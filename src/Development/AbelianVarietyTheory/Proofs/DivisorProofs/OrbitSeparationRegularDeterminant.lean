import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KeepsCuspOfIsUnifAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OneMemSecAndSecInfEqBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismUnipotentFixesComplexPointEqOne
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChange
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExistsIffTopExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentLinearisedLineBundleFiniteGroupQuot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescendsHodgeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerDivisorToroidalComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleHodgeClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericGroupDet

theorem det_delta_ne_zero (S : Type) [Group S] [Fintype S] [DecidableEq S] (f : S → ℂ)
    (hf : ∀ h, f h = if h = 1 then 1 else 0) :
    (Matrix.of fun h g : S => f (h * g)).det ≠ 0 := by
  have : (Matrix.of fun h g : S => f (h * g)) = (Equiv.inv S).permMatrix ℂ := by
    ext h g
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hf, mul_eq_one_iff_inv_eq]
  rw [this, Matrix.det_permutation]
  simp

theorem exists_combination_delta (F V S J : Type) [Field F] [Algebra F ℂ] [AddCommGroup V] [Module F V]
    [Group S] [Fintype S] [DecidableEq S] [Fintype J]
    (ev : V →ₗ[F] (S → ℂ)) (r : J → S) (W : Submodule F V) (h1 : ∃ j, r j = 1)
    (h2 : ∀ v ∈ W, ∀ h, h ∉ Set.range r → ev v h = 0)
    (h3 : ∀ a : J → ℂ, (∀ v ∈ W, ∑ j, a j * ev v (r j) = 0) → a = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → V), (∀ k, w k ∈ W) ∧
      ∀ h, ∑ k, c k * ev (w k) h = if h = 1 then 1 else 0 := by
  classical
  set s : Set (J → ℂ) := (fun v => fun j => ev v (r j)) '' (W : Set V) with hs
  have htop : Submodule.span ℂ s = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφ : ∀ x : J → ℂ, φ x = ∑ j, x j * φ (fun j' => if j = j' then 1 else 0) := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp [smul_eq_mul]
    have ha := h3 (fun j => φ (fun j' => if j = j' then 1 else 0)) fun v hv => by
      have := hle (Submodule.subset_span ⟨v, hv, rfl⟩)
      rw [LinearMap.mem_ker, hφ] at this
      simpa [mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [hφ x, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [congrFun ha j]; simp
  let b : J → ℂ := fun j => if r j = 1 then 1 else 0
  have hb : b ∈ Submodule.span ℂ s := htop ▸ Submodule.mem_top
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hb
  choose w hw hwg using fun k => (g k).2
  refine ⟨n, c, w, hw, fun h => ?_⟩
  by_cases hr : h ∈ Set.range r
  · obtain ⟨j, rfl⟩ := hr
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hwg k]
  · have h1' : h ≠ 1 := by
      rintro rfl
      obtain ⟨j, hj⟩ := h1
      exact hr ⟨j, hj⟩
    rw [if_neg h1']
    exact Finset.sum_eq_zero fun k _ => by rw [h2 _ (hw k) h hr, mul_zero]

theorem exists_vec_det_ne_zero (F : Type) [Field F] [CharZero F] [Algebra F ℂ] (V : Type) [AddCommGroup V] [Module F V]
    (S : Type) [Group S] [Fintype S] [DecidableEq S] (ι : Type) [Finite ι] (ev : ι → V →ₗ[F] (S → ℂ))
    (J : ι → Type) [∀ i, Fintype (J i)] (r : ∀ i, J i → S) (W : ι → Submodule F V)
    (h1 : ∀ i, ∃ j, r i j = 1) (h2 : ∀ i, ∀ v ∈ W i, ∀ h, h ∉ Set.range (r i) → ev i v h = 0)
    (h3 : ∀ i (a : J i → ℂ), (∀ v ∈ W i, ∑ j, a j * ev i v (r i j) = 0) → a = 0) :
    ∃ v : V, ∀ i, (Matrix.of fun h g : S => ev i v (h * g)).det ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose n c w hw hcw using fun i => exists_combination_delta F V S (J i) (ev i) (r i) (W i) (h1 i) (h2 i) (h3 i)
  let vec : (Σ i, Fin (n i)) → V := fun p => w p.1 p.2
  let P : ι → MvPolynomial (Σ i, Fin (n i)) ℂ := fun i =>
    Matrix.det (Matrix.of fun h g : S => ∑ p, MvPolynomial.X p * MvPolynomial.C (ev i (vec p) (h * g)))
  have hP : ∀ i (x : (Σ i, Fin (n i)) → ℂ), MvPolynomial.eval x (P i) =
      (Matrix.of fun h g : S => ∑ p, x p * ev i (vec p) (h * g)).det := by
    intro i x
    rw [RingHom.map_det]
    congr 1
    ext h g
    simp [RingHom.mapMatrix_apply]
  have hPi : ∀ i, P i ≠ 0 := by
    intro i hz
    let x : (Σ i, Fin (n i)) → ℂ := fun p => if p.1 = i then c p.1 p.2 else 0
    have hx : ∀ h, ∑ p, x p * ev i (vec p) h = if h = 1 then 1 else 0 := by
      intro h
      rw [← hcw i h, Fintype.sum_sigma, Finset.sum_eq_single i]
      · simp [x, vec]
      · intro b _ hb
        exact Finset.sum_eq_zero fun k _ => by simp [x, hb]
      · simp
    have := det_delta_ne_zero S _ hx
    rw [← hP, hz, map_zero] at this
    exact this rfl
  have hQ : (∏ i, P i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hPi i
  obtain ⟨x, hx, hQx⟩ : ∃ x ∈ Set.pi Set.univ (fun _ : (Σ i, Fin (n i)) => Set.range (algebraMap F ℂ)),
      MvPolynomial.eval x (∏ i, P i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ (MvPolynomial.funext_set (fun _ => Set.range (algebraMap F ℂ))
      (fun _ => Set.infinite_range_of_injective (algebraMap F ℂ).injective)
      fun x hx => by rw [hcon x hx, map_zero])
  choose t ht using fun p => hx p (Set.mem_univ p)
  refine ⟨∑ p, t p • vec p, fun i => ?_⟩
  have hne : MvPolynomial.eval x (P i) ≠ 0 := by
    rw [map_prod] at hQx
    exact Finset.prod_ne_zero_iff.1 hQx i (Finset.mem_univ _)
  rw [hP] at hne
  convert hne using 2
  ext h g
  simp [map_sum, Finset.sum_apply, Algebra.smul_def, ht]

end GlobalTheory.GenericGroupDet
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_groupDeterminants_ne_zero : ∀ (F : Type) [Field F] [CharZero F] [Algebra F ℂ] (V : Type) [AddCommGroup V] [Module F V] (S : Type) [Group S] [Fintype S] [DecidableEq S] (ι : Type) [Finite ι] (ev : ι → V →ₗ[F] (S → ℂ)) (J : ι → Type) [∀ i, Fintype (J i)] (r : ∀ i, J i → S) (W : ι → Submodule F V), (∀ i, ∃ j, r i j = 1) → (∀ i, ∀ v ∈ W i, ∀ h, h ∉ Set.range (r i) → ev i v h = 0) → (∀ i (a : J i → ℂ), (∀ v ∈ W i, ∑ j, a j * ev i v (r i j) = 0) → a = 0) → ∃ v : V, ∀ i, (Matrix.of fun h g : S => ev i v (h * g)).det ≠ 0 := by
  atlas_forward_decl GlobalTheory.GenericGroupDet.exists_vec_det_ne_zero
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SecRingNonZeroDiv

open GlobalTheory.CompHt GlobalTheory.FlagTan

theorem eq_zero_of_mul_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ) (F : Rul Xo c), F ∈ secZ Xo c e → (∀ Z : Comp Xo c, ∃ y : FrPt Xo c ℂ, LiesOn Z y ∧ evR Xo c F y ≠ 0) → ∀ f ∈ secRing Xo c, F * f = 0 → f = 0 := by
  intro E _ _ _ H Dw l Xo c e F hF hZ f hf hFf
  classical
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have hFZ : ∀ Z : Comp Xo c, genVal Z F ≠ 0 := by
    intro Z h0
    obtain ⟨y, hy, hne⟩ := hZ Z
    exact hne ((genVal_eq_zero_iff E H Dw l Xo c Z e F hF).1 h0 ℂ y hy)
  have hf' : f ∈ ⨆ e, secZ Xo c e := by rw [← GlobalTheory.LevDesc.toSubmodule_secRing]; exact hf
  obtain ⟨a, ha, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hf'
  have key : ∀ Z : Comp Xo c, ∀ d ∈ a.support, genVal Z (a d) = 0 := by
    intro Z
    haveI : CharZero (Om Z) := charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
    let χ : (Ix Dw → ℤ) → ((Ix Dw → (Om Z)ˣ) →* Om Z) := fun d =>
      { toFun := fun t => ((∏ i, t i ^ d i : (Om Z)ˣ) : Om Z)
        map_one' := by simp
        map_mul' := fun t s => by simp [mul_zpow, Finset.prod_mul_distrib] }
    have hχ : Function.Injective χ := by
      intro d d' hdd
      funext i
      let u : (Om Z)ˣ := Units.mk0 2 two_ne_zero
      have hp : ∀ d : Ix Dw → ℤ, χ d (Pi.mulSingle i u) = (2 : Om Z) ^ d i := by
        intro d
        show ((∏ j, (Pi.mulSingle i u : Ix Dw → (Om Z)ˣ) j ^ d j : (Om Z)ˣ) : Om Z) = _
        rw [Finset.prod_eq_single i]
        · simp [u, Units.val_zpow_eq_zpow_val]
        · intro j _ hj
          simp [Pi.mulSingle_eq_of_ne hj]
        · simp
      have h1 : (2 : Om Z) ^ d i = (2 : Om Z) ^ d' i := by
        rw [← hp, ← hp, hdd]
      have h2 : (((2 : ℚ) ^ d i : ℚ) : Om Z) = (((2 : ℚ) ^ d' i : ℚ) : Om Z) := by
        rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]; exact h1
      exact zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) (Rat.cast_injective h2)
    have hli : LinearIndependent (Om Z) (fun d => (χ d : (Ix Dw → (Om Z)ˣ) → Om Z)) :=
      (linearIndependent_monoidHom _ (Om Z)).comp χ hχ
    have hsum : ∑ d ∈ a.support, genVal Z (a d) • (χ d : (Ix Dw → (Om Z)ˣ) → Om Z) = 0 := by
      funext t
      obtain ⟨y', hy'⟩ := SecSeparation.exists_frBor (genFr hG Z) t
      have h1 : evR Xo c (F * a.sum fun _ x => x) y' = 0 := by rw [hFf]; exact evalAt_zero _ _ y'
      have h2 : evR Xo c (F * a.sum fun _ x => x) y' = evR Xo c F y' * evR Xo c (a.sum fun _ x => x) y' :=
        evalAt_mul _ _ _ _ y'
      have h3 : evR Xo c F y' ≠ 0 := by
        rw [evR_frBor hF hy']
        exact mul_ne_zero (Units.ne_zero _) (hFZ Z)
      have h4 : evR Xo c (a.sum fun _ x => x) y' = 0 := (mul_eq_zero.1 (h2.symm.trans h1)).resolve_left h3
      have h5 : evR Xo c (a.sum fun _ x => x) y' = ∑ d ∈ a.support, evR Xo c (a d) y' :=
        map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y') _ _
      rw [h5] at h4
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h4]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [evR_frBor (ha d) hy', mul_comm]
      rfl
    intro d hd
    exact linearIndependent_iff'.1 hli a.support (fun d => genVal Z (a d)) hsum d hd
  refine Finset.sum_eq_zero fun d hd => ?_
  exact secZ_eq_zero_of_genVal (ha d) fun Z => key Z d hd

end GlobalTheory.SecRingNonZeroDiv
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integerExponentSection_mul_eq_zero_imp_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ) (F : Rul Xo c), F ∈ secZ Xo c e → (∀ Z : Comp Xo c, ∃ y : FrPt Xo c ℂ, LiesOn Z y ∧ evR Xo c F y ≠ 0) → ∀ f ∈ secRing Xo c, F * f = 0 → f = 0 := by
  atlas_forward_decl GlobalTheory.SecRingNonZeroDiv.eq_zero_of_mul_eq_zero
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep.UnipPrime

open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters Formalism.L2.Pj

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem exists_plOver (j : Fin 2) : Nonempty (PlOver D.host j) := by
  have hne : Ideal.span {((D.host.g j : ℕ) : 𝓞 D.host.F)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at h1
    have : ((D.host.g j : ℕ) : 𝓞 D.host.F) = algebraMap ℤ (𝓞 D.host.F) (D.host.g j : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank] at h1
    have hd : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
    have hg := (D.host.g_prime j).two_le
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
    have : 2 ^ Module.finrank ℚ D.host.F ≤ D.host.g j ^ Module.finrank ℚ D.host.F := Nat.pow_le_pow_left hg _
    have : 2 ≤ 2 ^ Module.finrank ℚ D.host.F := Nat.le_self_pow hd.ne' 2
    omega
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hg : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∈ P := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨⟨P, hP.isPrime, fun e => ?_⟩, hg⟩⟩
  rw [e, Ideal.mem_bot] at hg
  exact (D.host.g_prime j).ne_zero (by exact_mod_cast hg)

theorem isNilpotent_sub_one_of_unitri {r : ℕ} {k : Type} [Field k] {u : GL (Fin r) k} (hu : u ∈ unitri r k) :
    IsNilpotent ((u : Matrix (Fin r) (Fin r) k) - 1) := by
  have ht : ((u : Matrix (Fin r) (Fin r) k) - 1).BlockTriangular id := hu.1.sub Matrix.blockTriangular_one
  have hc : ((u : Matrix (Fin r) (Fin r) k) - 1).charpoly = Polynomial.X ^ r := by
    rw [Matrix.charpoly_of_upperTriangular _ ht]
    simp [hu.2]
  refine ⟨r, ?_⟩
  have := Matrix.aeval_self_charpoly ((u : Matrix (Fin r) (Fin r) k) - 1)
  rwa [hc, map_pow, Polynomial.aeval_X] at this

theorem neat_typePrime (hM : D.host.g 0 * D.host.g 1 ∣ l.M) (hg : ∀ k, Dw.p + Dw.q + 1 < D.host.g k)
    (v : Sq D.host) : NeatPrime (typePrime l v) (D.host.g v.1) (Dw.p + Dw.q) ∧ (typePrime l v).IsPrime := by
  have hP : (typePrime l v).IsPrime := by
    refine halfPrime_isPrime l v.2.1.isMaximal ?_
    obtain ⟨k, hk⟩ := (g_dvd (D := D) v.1).trans hM
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ v.2.2
  refine ⟨⟨D.host.g_prime v.1, absNorm_eq_of_split (D.host.g_prime _) (D.nd.g_split _) hP (g_mem_typePrime v),
    fun hmem => ?_, hg v.1⟩, hP⟩
  have h0 : Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime v.1).ne_zero
  have hsq : Squarefree (Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)}) :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D v.1).2
  have hd : typePrime l v * typePrime l v ∣ Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← sq]
    exact hmem
  exact hP.ne_top (Ideal.isUnit_iff.1 (hsq _ hd))

theorem unipAt_of_unitri (fr : TypeFrame Dw l) (γ : LevelAut Dw l) (v : Sq D.host)
    (hγ : typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1))) : UnipAt (typePrime l v) γ := by
  obtain ⟨n, hn⟩ := isNilpotent_sub_one_of_unitri hγ
  set Nm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)) :=
    ((typeRed fr γ v : GL (Fin D.R.r) (ZMod (D.host.g v.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) - 1
    with hNm
  let π : Dw.La →ₗ[𝓞 D.host.E] QMod Dw.La (typePrime l v) := Submodule.mkQ _
  have key : ∀ (m : ℕ) (x : Dw.La), fr v (π (((liftLa γ - 1) ^ m) x)) = (Nm ^ m).mulVec (fr v (π x)) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', ← Matrix.mulVec_mulVec, ← ih]
      generalize ((liftLa γ - 1) ^ m) x = y
      have h1 : π (liftLa γ y) = qProj (J := typePrime l v) le_sup_left
          (γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y)) := by
        rw [← liftLa_spec]; rfl
      have h2 : π y = qProj (J := typePrime l v) le_sup_left ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y) := rfl
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub, h1, h2, hNm, Matrix.sub_mulVec,
        Matrix.one_mulVec, typeRed_mulVec]
  refine ⟨n, fun x => ?_⟩
  have h := key n x
  rw [hn, Matrix.zero_mulVec, AddEquivClass.map_eq_zero_iff] at h
  exact (Submodule.Quotient.mk_eq_zero _).1 h

theorem exists_index (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)) (hS : S = grpHR fr ∨ ∃ k, S = grpGHR fr k) :
    ∃ j : Fin 2, ∀ γ ∈ S, ∀ v : Sq D.host, v.1 = j → typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1)) := by
  rcases hS with rfl | ⟨k, rfl⟩
  · exact ⟨0, fun γ hγ v _ => hγ v trivial⟩
  · refine ⟨k + 1, fun γ hγ v hv => hγ v ?_⟩
    show v.1 ≠ k
    rw [hv]; fin_cases k <;> decide

end GlobalTheory.OrbitSep.UnipPrime

open GlobalTheory.OrbitSep.UnipPrime GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters in

theorem GlobalTheory.OrbitSep.exists_neatPrime_unipAt : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H), D.host.g 0 * D.host.g 1 ∣ l.M → (∀ k, Dw.p + Dw.q + 1 < D.host.g k) → ∀ (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ (I : Ideal (𝓞 D.host.E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) ∧ l.Mb ≤ I ∧ ∀ γ ∈ S, UnipAt I γ := by
  intro D H Dw l hM hg fr S hS
  obtain ⟨j, hj⟩ := exists_index fr S hS
  obtain ⟨w⟩ := exists_plOver (D := D) j
  let v : Sq D.host := ⟨j, w⟩
  obtain ⟨hN, -⟩ := neat_typePrime (Dw := Dw) hM hg v
  exact ⟨typePrime l v, D.host.g v.1, hN, le_sup_left, fun γ hγ => unipAt_of_unitri fr γ v (hj γ hγ v rfl)⟩
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_neatPrime_levelAutSubgroup_unipotent : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H), D.host.g 0 * D.host.g 1 ∣ l.M → (∀ k, Dw.p + Dw.q + 1 < D.host.g k) → ∀ (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ (I : Ideal (𝓞 D.host.E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) ∧ l.Mb ≤ I ∧ ∀ γ ∈ S, UnipAt I γ := by
  atlas_forward_decl GlobalTheory.OrbitSep.exists_neatPrime_unipAt
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.AllWt (ptF)

namespace GlobalTheory.GenCxPt

open Cardinal

theorem mk_le_aleph0 (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] : #K ≤ ℵ₀ := by
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  have h := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
  rw [Cardinal.mkRat, max_self] at h
  exact h

theorem transcendental_complex (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    Algebra.Transcendental K ℂ := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  have h := Algebra.IsAlgebraic.cardinalMk_le_max K ℂ
  rw [Cardinal.mk_complex, max_eq_right (mk_le_aleph0 K)] at h
  exact absurd h (not_le.2 Cardinal.aleph0_lt_continuum)

theorem infinite_of_isTranscendenceBasis (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {κ : Type}
    {w : κ → ℂ} (hw : IsTranscendenceBasis K w) : Infinite κ := by
  haveI : Nonempty κ := hw.nonempty_iff_transcendental.2 (transcendental_complex K)
  have h := hw.lift_cardinalMk_eq_max_lift
  simp only [Cardinal.lift_id, Cardinal.mk_complex] at h
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have h1 : #κ ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite κ).le
  have h2 : #K ⊔ #κ ⊔ ℵ₀ ≤ ℵ₀ := sup_le (sup_le (mk_le_aleph0 K) h1) le_rfl
  rw [← h] at h2
  exact absurd h2 (not_le.2 Cardinal.aleph0_lt_continuum)

theorem nonempty_algHom_complex (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (L : Type) [Field L]
    [Algebra K L] (n : ℕ) (hn : Algebra.trdeg K L = n) : Nonempty (L →ₐ[K] ℂ) := by
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' K L
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' K ℂ
  haveI := infinite_of_isTranscendenceBasis K hw
  have hι : #ι < ℵ₀ := by rw [hv.cardinalMk_eq_trdeg, hn]; exact Cardinal.natCast_lt_aleph0
  haveI : Finite ι := Cardinal.lt_aleph0_iff_finite.1 hι
  have hle : #ι ≤ #κ := hι.le.trans (Cardinal.infinite_iff.1 inferInstance)
  obtain ⟨f⟩ := hle
  obtain ⟨j, -⟩ := GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis hv (hw.1.comp f f.injective)
  exact ⟨j⟩

end GlobalTheory.GenCxPt

namespace GlobalTheory.GenCxPt

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (f : B →+* C) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) :=
  (Spec.map_preimage _).symm

end GlobalTheory.GenCxPt

open GlobalTheory.GenCxPt in

theorem GlobalTheory.GenCxPt.exists_frPt_ptF_eq_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : Comp Xo c),
    ∃ y : FrPt Xo c ℂ, ∀ s, ptF y s = genPt Z := by
  intro E _ _ _ H Dw l Xo c Z
  haveI := c.fin
  obtain ⟨e⟩ := nonempty_algHom_complex c.F (kap Z) Dw.dim ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).2 Z)
  have hsnd : spMap (e : kap Z →+* ℂ) ≫ genSp Z ≫ strK = spMap (algebraMap c.F ℂ) := by
    rw [genSp_strK, spMap_comp_spMap, AlgHom.comp_algebraMap]
  have hx : (spMap (e : kap Z →+* ℂ) ≫ xGen Z) ≫ Xo.s = sOf c ℂ := by
    rw [xGen, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (genSp Z),
      ← Category.assoc, hsnd, sOf, spMap_comp_spMap]
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt _ hx
  refine ⟨y, fun s => ?_⟩
  have hpt : ptF y = spMap (e : kap Z →+* ℂ) ≫ genSp Z := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, hy, xGen, Category.assoc]
    · rw [ptF, pullback.lift_snd, Category.assoc, ← hsnd]
  rw [hpt]
  have : (spMap (e : kap Z →+* ℂ) ≫ genSp Z) s ∈ Set.range (genSp Z) :=
    ⟨spMap (e : kap Z →+* ℂ) s, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [genSp, Scheme.range_fromSpecResidueField] at this
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexFramedPoint_over_componentGenericPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : Comp Xo c), ∃ y : FrPt Xo c ℂ, ∀ s, ptF y s = genPt Z := by
  atlas_forward_decl GlobalTheory.GenCxPt.exists_frPt_ptF_eq_genPt
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactificationComponent_integral_smooth_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ _ : IsIntegral (X₀ TF.Y Z), SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z) ∧ IsProjOver (s₀ TF.Y Z) ∧ GeometricallyConnected (s₀ TF.Y Z) ∧ Surjective (π₀ TF.X Z) ∧ GlobalTheory.IsNormalScheme (V₀ TF.Y Z) ∧ ∀ v : V₀ TF.Y Z, i₀ TF.Y Z v = genPt Z → j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  first | exact @GlobalTheory.BaseVar.isVariety_barComp | exact GlobalTheory.BaseVar.isVariety_barComp | (intros; apply GlobalTheory.BaseVar.isVariety_barComp <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentStabilizer_acts_by_levelChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ S : Subgroup (LevelAut Dw l), ∃ (Γ : Subgroup (LevelAut Dw l)) (ρ : Γ →* Aut (V₀ Y Z)), Γ ≤ S ∧ ActsBy Γ.subtype ρ ∧ ∀ h ∈ S, ∀ y : FrPt Xo c ℂ, LiesOn Z y → LiesOn Z (move Xo c h⁻¹ y) → h ∈ Γ := by
  first | exact @GlobalTheory.CompLevelStab.stab_acts | exact GlobalTheory.CompLevelStab.stab_acts | (intros; apply GlobalTheory.CompLevelStab.stab_acts <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.NormalizationOpenImmersion

theorem isOpenImmersion_toNormalization {V P X : Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [inst : QuasiCompact c] [inst_1 : QuasiSeparated c]
    (h : c ≫ p = j) : IsOpenImmersion c.toNormalization := by
  have : IsImmersion (c ≫ p) := h ▸ inferInstance
  have : IsImmersion c := IsImmersion.of_comp c p
  infer_instance

theorem main : ∀ {V P X : AlgebraicGeometry.Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [inst : QuasiCompact c] [inst_1 : QuasiSeparated c]
    (h : c ≫ p = j), IsOpenImmersion c.toNormalization :=
  fun c p _ j _ _ _ h => isOpenImmersion_toNormalization c p j h

end GlobalTheory.NormalizationOpenImmersion
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section
namespace GlobalTheory.EqModel

theorem isProjOver_pi_const {R : Type} [CommRing R] (κ : Type) [Finite κ] (A : Over (Sp R))
    (h : IsProjOver A.hom) : IsProjOver (∏ᶜ fun _ : κ => A).hom := by
  let n := Nat.card κ
  let e : κ ≃ Fin n := Finite.equivFin κ
  let I₁ : (∏ᶜ fun _ : κ => A) ≅ ∏ᶜ fun _ : Fin n => A := (Pi.reindex e.symm (fun _ : κ => A)).symm
  let I₂ : (∏ᶜ fun _ : Fin n => A) ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A n :=
    (limit.isLimit _).conePointUniqueUpToIso (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A n)
  have : IsIso (I₁ ≪≫ I₂).hom.left := ((Over.forget _).mapIso (I₁ ≪≫ I₂)).isIso_hom
  have hp := Models.FamInh.isProjOver_powObj A h n
  have e' := ProjSpace.isProjOver_comp_of_isClosedImmersion (I₁ ≪≫ I₂).hom.left hp
  rwa [Over.w] at e'

theorem isOpenImmersion_toNormalization {V P X : Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact c] [QuasiSeparated c] (h : c ≫ p = j) :
    IsOpenImmersion c.toNormalization := by
  first
  | (rename_i h_5 h_7 h_8 h_9; revert V P X c p h_5 j h_7 h_8 h_9 h; exact @_root_.GlobalTheory.NormalizationOpenImmersion.main)
  | exact @_root_.GlobalTheory.NormalizationOpenImmersion.main
  | exact _root_.GlobalTheory.NormalizationOpenImmersion.main
  | (apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormalizationOpenImmersion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormalizationOpenImmersion.main ..)

theorem isQProjOver_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsQProjOver f := by
  obtain ⟨N, i, _, e⟩ := h
  exact ⟨N, i, inferInstance, inferInstance, e⟩

theorem exists_projective_quotient {F : Type} [Field F] {X : Scheme.{0}} (s : X ⟶ Sp F) {Γ : Type}
    [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (hs : IsProjOver s) (hρ : ∀ g, (ρ g).hom ≫ s = s) :
    ∃ (W : Scheme.{0}) (q : X ⟶ W) (sW : W ⟶ Sp F), IsAffineQuotient ρ q ∧ q ≫ sW = s ∧
      IsProjOver sW ∧ IsFinite q ∧ Surjective q := by
  have := OrbitsInAffineOpens.of_isQProjOver (isQProjOver_of_isProjOver' hs) ρ
  obtain ⟨W, q, hq⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hqs := hq.comp_desc s hρ
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs).1
  have : IsProper (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : LocallyOfFiniteType (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : IsProper (hq.desc s hρ) := hq.isProper _
  obtain ⟨L, hL⟩ := GaloisQuotient.exists_isAmpleLB_of_isAffineQuotient hq
    (isQProjOver_of_isProjOver' hs)
  exact ⟨W, q, hq.desc s hρ, hq, hqs, hL.isProjOver _, hq.isFinite (hq.desc s hρ), hq.surjective⟩

theorem exists_equivariant_model : ∀ (F : Type) [Field F] [NumberField F] (X V : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (j : V ⟶ X) [IsOpenImmersion j] (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut V), IsProjOver sX → Nonempty V → GlobalTheory.IsNormalScheme V → (∀ γ, (ρ γ).hom ≫ j ≫ sX = j ≫ sX) → ∃ (X' W : Scheme.{0}) (φ : X' ⟶ X) (ℓ : V ⟶ X') (ρ' : Γ →* Aut X') (q : X' ⟶ W) (sW : W ⟶ Sp F) (_ : IsIntegral X'), GlobalTheory.IsNormalScheme X' ∧ IsProjOver (φ ≫ sX) ∧ IsOpenImmersion ℓ ∧ ℓ ≫ φ = j ∧ (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) ∧ IsAffineQuotient ρ' q ∧ q ≫ sW = φ ≫ sX ∧ IsProjOver sW ∧ IsIntegral W ∧ IsFinite q ∧ Surjective q := by
  intro F _ _ X V _ sX j _ Γ _ _ ρ hX hne hN hρ
  classical
  let A : Over (Sp F) := Over.mk sX
  let P : Over (Sp F) := ∏ᶜ fun _ : Γ => A
  let B : Over (Sp F) := Over.mk (j ≫ sX)
  let c : B ⟶ P := Pi.lift fun γ => Over.homMk ((ρ γ).hom ≫ j) (by simpa [A, B] using hρ γ)
  have hcπ (γ : Γ) : c.left ≫ (Pi.π (fun _ : Γ => A) γ).left = (ρ γ).hom ≫ j := by
    rw [← Over.comp_left, Pi.lift_π]; rfl

  let σ₀ (g : Γ) : P ⟶ P := Pi.lift fun γ => Pi.π (fun _ : Γ => A) (γ * g)
  have hσπ (g γ : Γ) : σ₀ g ≫ Pi.π (fun _ : Γ => A) γ = Pi.π (fun _ : Γ => A) (γ * g) :=
    Pi.lift_π _ _
  have hσ (g h : Γ) : σ₀ g ≫ σ₀ h = σ₀ (h * g) :=
    Pi.hom_ext _ _ fun γ => by rw [Category.assoc, hσπ, hσπ, hσπ, mul_assoc]
  have hσ1 : σ₀ 1 = 𝟙 P := Pi.hom_ext _ _ fun γ => by rw [hσπ, mul_one, Category.id_comp]
  let σI (g : Γ) : P.left ≅ P.left :=
    { hom := (σ₀ g).left, inv := (σ₀ g⁻¹).left,
      hom_inv_id := by rw [← Over.comp_left, hσ, inv_mul_cancel, hσ1]; rfl,
      inv_hom_id := by rw [← Over.comp_left, hσ, mul_inv_cancel, hσ1]; rfl }
  let σ : Γ →* Aut P.left := MonoidHom.mk' σI fun g h => Iso.ext (by
    change (σ₀ (g * h)).left = (σ₀ h).left ≫ (σ₀ g).left
    rw [← Over.comp_left, hσ])
  have hσP (g : Γ) : (σ g).hom ≫ P.hom = P.hom := Over.w (σ₀ g)
  have hρmul (g γ : Γ) : (ρ (γ * g)).hom = (ρ g).hom ≫ (ρ γ).hom := by rw [map_mul]; rfl
  have H (g : Γ) : (ρ g).hom ≫ c.left = c.left ≫ (σ g).hom := by
    have e : (Over.homMk (ρ g).hom (by simpa [B] using hρ g) : B ⟶ B) ≫ c = c ≫ σ₀ g :=
      Pi.hom_ext _ _ fun γ => by
        rw [Category.assoc, Category.assoc, hσπ]
        ext1
        simp only [Over.comp_left, hcπ, Over.homMk_left, hρmul, Category.assoc]
    exact congrArg CommaMorphism.left e

  have : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX).1
  have hP : IsProjOver P.hom := isProjOver_pi_const Γ A hX
  have : IsProper P.hom := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hP).1
  have hcP : c.left ≫ P.hom = j ≫ sX := Over.w c
  have hc1 : c.left ≫ (Pi.π (fun _ : Γ => A) 1).left = j := by rw [hcπ, map_one]; rfl
  have : IsSeparated (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : QuasiSeparated c.left := .of_comp c.left P.hom
  have : IsSeparated (Pi.π (fun _ : Γ => A) 1).left := by
    have : IsSeparated ((Pi.π (fun _ : Γ => A) 1).left ≫ sX) := Over.w (Pi.π (fun _ : Γ => A) 1) ▸ inferInstance
    exact .of_comp _ sX
  have : IsIntegral V := isIntegral_of_isOpenImmersion j
  have : IsIntegral B.left := ‹IsIntegral V›
  have : GlobalTheory.IsNormalScheme B.left := hN
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sX)
  have : CompactSpace V := ⟨by
    rw [j.isOpenEmbedding.isInducing.isCompact_iff, Set.image_univ]
    exact NoetherianSpace.isCompact _⟩
  have : IsNoetherian V := {}
  have : QuasiCompact (c.left ≫ (Pi.π (fun _ : Γ => A) 1).left) := by
    rw [hc1]
    exact quasiCompact_of_noetherianSpace_source j
  have : QuasiCompact c.left := .of_comp c.left (Pi.π (fun _ : Γ => A) 1).left
  have : LocallyOfFiniteType (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : LocallyOfFiniteType c.left := locallyOfFiniteType_of_comp c.left P.hom

  have hfin : IsFinite c.left.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType c.left P.hom fun x _ =>
      charZero_of_injective_ringHom
        ((Scheme.ΓSpecIso (.of F)).inv ≫ (j ≫ sX).appTop ≫ V.Γevaluation x).hom.injective
  let φ : c.left.normalization ⟶ X := c.left.fromNormalization ≫ (Pi.π (fun _ : Γ => A) 1).left
  have hφ : φ ≫ sX = c.left.fromNormalization ≫ P.hom := by
    simp only [φ, Category.assoc]
    congr 1
    exact Over.w (Pi.π (fun _ : Γ => A) 1)
  have hproj : IsProjOver (φ ≫ sX) := hφ ▸ isProjOver_comp_of_isFinite _ hP
  have hnorm : GlobalTheory.IsNormalScheme c.left.normalization :=
    IsNormalScheme.normalization_of_isIntegral c.left
  let ρ' := normalizationAction c.left ρ σ H
  have hρ' (g : Γ) : (ρ' g).hom ≫ φ ≫ sX = φ ≫ sX := by
    rw [hφ, normalizationAction_fromNormalization_assoc, hσP]
  obtain ⟨W, q, sW, hq, hqs, hW, hqf, hqs'⟩ := exists_projective_quotient (φ ≫ sX) ρ' hproj hρ'
  refine ⟨c.left.normalization, W, φ, c.left.toNormalization, ρ', q, sW, inferInstance, hnorm, hproj,
    isOpenImmersion_toNormalization c.left (Pi.π (fun _ : Γ => A) 1).left j hc1, ?_,
    fun g => (toNormalization_normalizationAction c.left ρ σ H g).symm, hq, hqs, hW, hq.isIntegral,
    hqf, hqs'⟩
  simp only [φ, Scheme.Hom.toNormalization_fromNormalization_assoc, hc1]

end GlobalTheory.EqModel
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_normal_projective_compactification : ∀ (F : Type) [Field F] [NumberField F] (X V : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (j : V ⟶ X) [IsOpenImmersion j] (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut V), IsProjOver sX → Nonempty V → GlobalTheory.IsNormalScheme V → (∀ γ, (ρ γ).hom ≫ j ≫ sX = j ≫ sX) → ∃ (X' W : Scheme.{0}) (φ : X' ⟶ X) (ℓ : V ⟶ X') (ρ' : Γ →* Aut X') (q : X' ⟶ W) (sW : W ⟶ Sp F) (_ : IsIntegral X'), GlobalTheory.IsNormalScheme X' ∧ IsProjOver (φ ≫ sX) ∧ IsOpenImmersion ℓ ∧ ℓ ≫ φ = j ∧ (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) ∧ IsAffineQuotient ρ' q ∧ q ≫ sW = φ ≫ sX ∧ IsProjOver sW ∧ IsIntegral W ∧ IsFinite q ∧ Surjective q := by
  atlas_forward_decl GlobalTheory.EqModel.exists_equivariant_model
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.Cartier.RatSecDiv

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_mul_unit_iff {x : X} {a u : X.functionField} (hu : UnitAt x u) :
    UnitAt x (a * u) ↔ UnitAt x a := by
  refine ⟨fun h => ?_, fun h => h.mul hu⟩
  have e : a = a * u * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one]
  rw [e]; exact h.mul hu.inv

theorem local_of {D D' : CartierDiv X} {V : X.Opens} {h : X.functionField}
    (H : ∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V))
    {x : X} {gi rk : X.functionFieldˣ} (hi : D.IsEqn x gi) (hk : D'.IsEqn x rk) :
    RegAt x (h * (gi : X.functionField) / (rk : X.functionField)) ∧
      (UnitAt x (h * (gi : X.functionField) / (rk : X.functionField)) ↔ x ∈ V) := by
  obtain ⟨g, g', hg, hg', hr, hu⟩ := H x
  have u : UnitAt x (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) :=
    (hg.iff_unitAt.1 hi).mul (hk.iff_unitAt.1 hg')
  have e : h * (gi : X.functionField) / (rk : X.functionField) =
      h * (g : X.functionField) / (g' : X.functionField) *
        (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) := by
    have := g.ne_zero; have := g'.ne_zero; have := rk.ne_zero
    field_simp
  rw [e, unitAt_mul_unit_iff u]
  exact ⟨hr.mul u.regAt, hu⟩

end GlobalTheory.Cartier.RatSecDiv

open GlobalTheory.Cartier.RatSecDiv in

theorem GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq :
    ∀ {X : Scheme.{0}} [IsIntegral X] (D D' : CartierDiv X) (L : LB X) (r : L.ι → X.functionFieldˣ),
    Presents D' L r → ∀ (V : X.Opens) (h : X.functionField),
    (∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V)) →
    ∃ θ : (LB.div (toLB D) L).Sec, nonzeroLocus θ = V := by
  intro X _ D D' L r hP V h H
  have key (p : (LB.div (toLB D) L).ι) : ∃ a : Γ(X, (LB.div (toLB D) L).U p), ∀ hp,
      fnOf _ hp a = h * (p.1.1.2 : X.functionField) / (r p.2 : X.functionField) := by
    by_cases hp : genericPoint X ∈ (LB.div (toLB D) L).U p
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hp fun x hx =>
        (local_of H (p.1.2.2 x hx.1) (hP.isEqn p.2 x hx.2)).1
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (hp h').elim⟩
  choose a ha using key
  refine ⟨⟨a, fun p q => fn_ext fun hpq => ?_⟩, ?_⟩
  · have hp : genericPoint X ∈ (LB.div (toLB D) L).U p := hpq.1
    have hq : genericPoint X ∈ (LB.div (toLB D) L).U q := hpq.2
    refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg _ (fnOf_resG _ hpq _))).symm)
    rw [ha p hp, ha q hq]
    have eL := hP.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2)
    have e1 : fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val =
        (p.1.1.2 : X.functionField) / (q.1.1.2 : X.functionField) := fnOf_toLB_g _ _ _
    have eg : fnOf _ hpq ((LB.div (toLB D) L).g p q).val =
        fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val *
          (fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val)⁻¹ := by
      change fnOf _ hpq ((res _ ((toLB D).g p.1 q.1) * (res _ (L.g p.2 q.2))⁻¹ : Γ(X, _)ˣ).val) = _
      erw [Units.val_mul, map_mul, map_units_inv]
      exact congrArg₂ (· * ·) (fnOf_resG _ _ _) (congrArg _ (fnOf_resG _ _ _))
    have eL' : fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val =
        (r p.2 : X.functionField) / (r q.2 : X.functionField) :=
      (eq_div_of_mul_eq (r q.2).ne_zero eL.symm)
    rw [eg, e1, eL']
    have := (p.1.1.2).ne_zero; have := (q.1.1.2).ne_zero
    have := (r p.2).ne_zero; have := (r q.2).ne_zero
    field_simp
  · have hmem (p : (LB.div (toLB D) L).ι) (y : X) (hy : y ∈ (LB.div (toLB D) L).U p) :
        y ∈ X.basicOpen (a p) ↔ y ∈ V := by
      rw [← unitAt_fnOf_iff hy (gen_mem hy), ha p (gen_mem hy)]
      exact (local_of H (p.1.2.2 y hy.1) (hP.isEqn p.2 y hy.2)).2
    refine le_antisymm (iSup_le fun p y hy => (hmem p y (X.basicOpen_le _ hy)).1 hy) fun y hy => ?_
    obtain ⟨i, hi⟩ := exists_chart (isLB_toLB D) y
    obtain ⟨k, hk⟩ := exists_chart hP.isLB y
    exact Opens.mem_iSup.2 ⟨(i, k), (hmem (i, k) y ⟨hi, hk⟩).2 hy⟩
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
namespace GlobalTheory.LogCanon

theorem exOf_kapBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) :
    (fun ix : Ix Dw => Option.elim ix 0 fun x =>
      (fun τ : E →+* ℂ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) x.1) =
      AllWt.exOf Dw (kapBase Dw) 0 := by
  funext ix
  rcases ix with _ | ⟨τ, i⟩
  · rfl
  · by_cases h' : τ (H.rt : E) = H.rt0
    · have hi : (i : ℕ) < Dw.p := by
        have := i.2; simp only [Datum.mult, if_pos h'] at this; exact this
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_pos h', dif_pos h', dif_pos hi, kapBase, sub_zero,
        if_pos hi]
    · have hi : (i : ℕ) < Dw.q := by
        have := i.2; simp only [Datum.mult, if_neg h'] at this; exact this
      have hc : conjEmb τ (H.rt : E) = H.rt0 := by
        have := (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H τ).resolve_left h'
        unfold InPsi at this
        rw [ComplexEmbedding.conjugate_coe_eq] at this
        exact this
      have hn : ¬ (Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p) := by omega
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_neg h', dif_neg h', dif_pos hc, dif_pos hi, kapBase,
        if_neg hn, neg_neg, sub_zero]

theorem exists_kap_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim), ∃ (κ : LB (X₀ TF.Y Z)) (hκ : κ.IsLB), CechPic.pull (π₀ TF.X Z) (cls κ hκ) = cls (L₀ TF.X Z (kapBase Dw)) (isLB_L₀ TF.X Z _) ∧ ∃ θ : (LB.div κ K.bundle).Sec, nonzeroLocus θ = (j₀ TF.Y Z).opensRange := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hF _ K
  obtain ⟨hI, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  obtain ⟨φ₀, f₀, hgen, hdiv⟩ := GlobalTheory.T.exists_cartierDivisor_det_lieEigenparts_toroidal E H Dw l Xo c TF Z
  obtain ⟨D, hpull, hD⟩ := hdiv fun τ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p
  refine ⟨toLB D, isLB_toLB D, ?_, ?_⟩
  · rw [exOf_kapBase Dw] at hpull
    exact hpull
  · obtain ⟨i₀, hi₀⟩ : ∃ i, genericPoint (X₀ TF.Y Z) ∈ K.bundle.U i :=
      Opens.mem_iSup.1 (K.isLB.cover.ge (Set.mem_univ _))
    have hP := presents_ofLB K.isLB i₀ hi₀
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_logKodairaSpencer_divisor_toroidalComponent E H Dw l Xo c TF Z hpq hF K _ _ hP φ₀ f₀ hgen D hD
    exact GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq D _ K.bundle _ hP _ h hh
end GlobalTheory.LogCanon
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toroidalCanonicalBundle_weight_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim), ∃ (κ : LB (X₀ TF.Y Z)) (hκ : κ.IsLB), CechPic.pull (π₀ TF.X Z) (cls κ hκ) = cls (L₀ TF.X Z (kapBase Dw)) (isLB_L₀ TF.X Z _) ∧ ∃ θ : (LB.div κ K.bundle).Sec, nonzeroLocus θ = (j₀ TF.Y Z).opensRange := by
  atlas_forward_decl GlobalTheory.LogCanon.exists_kap_theta
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_separate_quotient_generic_fibre_descends : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [NumberField F] (σ : F →+* ℂ) (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → 1 ≤ n → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → letI := algebraΓOfHom sX; ∀ (K : CanonLB sX n) (δ N' B : LB X) (hδ : δ.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (N : LB W) (hN : N.IsLB) (m : ℕ), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → IsNef F δ → IsBig F δ → IsNef F N' → (n + 1).choose 2 < m → cls B hB = m • cls δ hδ + cls N' hN' → ∀ (J : Type) [Fintype J] (v : J → (Sp ℂ ⟶ V)), Function.Injective v → (∀ j, v j ≫ i ≫ sX = spMap σ) → (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 sX (tens K.bundle B) ⊤, ∑ j, a j * H0.val (v j ≫ i) (k j) le_top (hk j) g = 0) → a = 0 := by
  first | exact @GlobalTheory.QuotSep.sections_separate_quotient_fibre | exact GlobalTheory.QuotSep.sections_separate_quotient_fibre | (intros; apply GlobalTheory.QuotSep.sections_separate_quotient_fibre <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

section Transport

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {P B : LB Y}

def isoSec (w : LB.Iso P B) (hw : w.IsGen) : (LB.div B P).Sec := ⟨fun i => (w.s i : _), fun i j => by
  have := congrArg Units.val (hw i j)
  rw [Units.val_mul] at this
  exact this⟩

theorem val_congr_pt {O : Y.Opens} {R : Type} [CommRing R] {x x' : Sp R ⟶ Y} (h : x = x') (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hO' : ⊤ ≤ x' ⁻¹ᵁ O) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst h; rfl

theorem val_restr_eq {O O' : Y.Opens} (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ Y) (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

end Transport

set_option maxHeartbeats 1000000 in

theorem exists_rule_of_cls_pull : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)) (L : LB (X₀ TF.Y Z)) (hL : L.IsLB), CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z _) → ∃ Φ : H0 (s₀ TF.Y Z) L ⊤ → Rul Y.d.Xo₂ Y.d.c₂, (∀ t, nonzeroLocus (toSec t) ≤ (j₀ TF.Y Z).opensRange → Φ t ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) ∧ ∀ (y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ) (v : Sp ℂ ⟶ V₀ TF.Y Z), v ≫ i₀ TF.Y Z = ptF y → ∀ (k : L.ι) (hk : ⊤ ≤ (v ≫ j₀ TF.Y Z) ⁻¹ᵁ L.U k), ∃ lam : ℂˣ, ∀ t, evR Y.d.Xo₂ Y.d.c₂ (Φ t) y = lam * H0.val (v ≫ j₀ TF.Y Z) k le_top hk t := by
  intro D T j Y e o hG hE Z TF la L hL hc
  have hP : (L.pull (π₀ TF.X Z)).IsLB := LB.isLB_pull hL _
  have hB := isLB_L₀ TF.X Z la
  obtain ⟨w, hw⟩ := (cls_eq_iff hP hB).1 ((cls_pull hL _ hP).trans hc)
  let C := divChart hB hP
  let G : H0 (str₀ TF.X Z) (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))) ⊤ := H0.ofSec _ ⊤ (isoSec w hw)
  let sOf : H0 (s₀ TF.Y Z) L ⊤ → H0 (str₀ TF.X Z) (L₀ TF.X Z la) ⊤ := fun t =>
    C.mul (H0.pull (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) G
  choose f hf hf' using fun t => exists_suppOn_sec₀_eq _ _ _ _ _ _ _ _ _ (AllWt.exOf _ la 0) (H0.restr le_top (sOf t))
  refine ⟨fun t => (f t).1, fun t ht => ?_, fun yy v hv k hk => ?_⟩
  · have hs : sOf t ∈ vanBd TF.X Z la := (mem_vanBd _ _).2 fun y hy hn => by
      obtain ⟨τ, ha, hb, hcc⟩ := C.cover y
      have u1 : IsUnit (H0.germ (C.c τ) y (memTop y) hcc (sOf t)) := by
        rw [← ger_toSec]; exact (isUnit_ger_iff _ hcc).2 hn
      have e3 := C.germ_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G τ y (memTop y) ha hb hcc
      have u1' : IsUnit (H0.germ (C.a τ) y (memTop y) ha
          (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) *
          H0.germ (C.b τ) y (memTop y) hb G) := (congrArg IsUnit e3).mp u1
      have u2 := (congrArg IsUnit (H0.germ_pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top (C.a τ) y (memTop y) ha t)).mp
        (isUnit_of_mul_isUnit_left u1')
      have u3 := (isUnit_map_iff (Scheme.Hom.stalkMap (π₀ TF.X Z) y).hom _).1 u2
      rw [← ger_toSec] at u3
      obtain ⟨v', hv'⟩ := ht ((isUnit_ger_iff _ _).1 u3)
      refine hy (show TF.X.π (inc₀ TF.X Z y) ∈ LogKS.interior TF.Y from ⟨i₀ TF.Y Z v', ?_⟩)
      rw [← Scheme.Hom.comp_apply, ← j₀_ι, Scheme.Hom.comp_apply, hv', ← Scheme.Hom.comp_apply, morphismRestrict_ι,
        Scheme.Hom.comp_apply]
    obtain ⟨g, hg⟩ := vanBd_le_space D T j Y e o hG hE Z TF la hs
    have e0 : f t = Submodule.inclusion (cusp_le_secZ Z Y.U la) g := by
      refine sub_eq_zero.1 (eq_zero_of_sec₀ TF.X Z (Submodule.sub_mem _ (hf t) g.2.2) ?_)
      rw [map_sub, hf' t, ← hg]
      exact sub_self _
    show (f t).1 ∈ _
    rw [e0]
    exact g.2
  · have e1 : TF.X.ptY yy ≫ TF.X.π = v ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
      rw [(TF.X.lies_ptY yy).1, j₀_ι, ← Category.assoc, hv]
      rfl
    have hr : Set.range (TF.X.ptY yy) ⊆ Set.range (inc₀ TF.X Z) := by
      rintro _ ⟨s, rfl⟩
      refine ⟨⟨_, show TF.X.π (TF.X.ptY yy s) ∈ barComp TF.Y Z from ?_⟩, rfl⟩
      rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
      exact ((v ≫ j₀ TF.Y Z) s).2
    let zz := IsOpenImmersion.lift (inc₀ TF.X Z) (TF.X.ptY yy) hr
    have hzz : zz ≫ inc₀ TF.X Z = TF.X.ptY yy := IsOpenImmersion.lift_fac _ _ _
    have e2 : zz ≫ π₀ TF.X Z = v ≫ j₀ TF.Y Z := by
      have h1 : (zz ≫ π₀ TF.X Z) ≫ (barComp TF.Y Z).ι = (v ≫ j₀ TF.Y Z) ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, Category.assoc, ← e1, ← hzz, Category.assoc]
        exact congrArg (zz ≫ ·) (morphismRestrict_ι TF.X.π (barComp TF.Y Z))
      exact (cancel_mono _).1 h1
    obtain ⟨k', hk'⟩ := exists_chart_of_field (TF.X.F.isLB_LL (AllWt.exOf (T.Q.Dw j) la 0)) (TF.X.pt yy ≫ TF.X.inc)
    obtain ⟨Q, tt, hQ, htt⟩ := FlagCover.exists_chartFr_frBor TF.X yy k' hk'
    have hO : ⊤ ≤ (TF.X.pt yy ≫ TF.X.inc) ⁻¹ᵁ flagOpen TF.X :=
      FlagMod.le_preimage_map TF.X.inc (top_le_inc TF.X) le_top
    have hzO : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by rw [hzz, ← FlagCover.pt_inc]; exact hO
    have hzk : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ (TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0)).U k' := by
      rw [hzz, ← FlagCover.pt_inc]; exact hk'
    have hTop : ⊤ ≤ zz ⁻¹ᵁ (⊤ : (Y₀ TF.X Z).Opens) := fun _ _ => trivial
    have hz1 : ⊤ ≤ zz ⁻¹ᵁ U₀ TF.X Z := hzO
    have hz2 : ⊤ ≤ zz ⁻¹ᵁ (L₀ TF.X Z la).U (pIdx _ (inc₀ TF.X Z) k') := fun s hs => mem_pIdx.2 (hzk hs)
    have hπ1 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ (⊤ : (X₀ TF.Y Z).Opens) := fun _ _ => trivial
    have hπ2 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ L.U k := by rw [e2]; exact hk
    have hz3 : ⊤ ≤ zz ⁻¹ᵁ (L.pull (π₀ TF.X Z)).U (pIdx L (π₀ TF.X Z) k) := fun s hs => mem_pIdx.2 (hπ2 hs)
    have hz4 : ⊤ ≤ zz ⁻¹ᵁ (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))).U
        (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) := fun s hs => ⟨hz2 hs, hz3 hs⟩
    have hu : IsUnit (H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G) := by
      rw [H0.val_ofSec]
      exact (w.s (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)).isUnit.map (GlobalTheory.TangentOrigin.evalPt zz _ hz4)
    obtain ⟨c0, hc0⟩ : ∃ c0 : ℂˣ, ∀ g : AllWt.secZ Y.d.Xo₂ Y.d.c₂ (AllWt.exOf (T.Q.Dw j) la 0),
        evR _ _ g.1 yy = c0.val * H0.val (TF.X.pt yy ≫ TF.X.inc) k' hO hk' (secOf TF.X _ g) :=
      ⟨_, fun g => evR_eq_val_secOf g hO hQ htt⟩
    refine ⟨c0 * hu.unit, fun t => ?_⟩
    show evR _ _ (f t).1 yy = _
    rw [hc0 (f t)]
    rw [val_congr_pt (p := flagStr TF.X) (B := TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0))
      ((FlagCover.pt_inc TF.X yy).trans hzz.symm) k' hO hk' hzO hzk]
    rw [show H0.val (zz ≫ inc₀ TF.X Z) k' hzO hzk (secOf TF.X _ (f t)) =
        H0.val zz (pIdx _ (inc₀ TF.X Z) k') hz1 hz2 (sec₀ TF.X Z _ (f t)) from
      (H0.val_pull (inc₀ TF.X Z) le_rfl zz (pIdx _ _ k') hz1 hz2 hzO hzk _).symm]
    rw [hf' t, val_restr_eq le_top zz _ hTop hz1 hz2]
    have e4 : H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) =
        H0.val (v ≫ j₀ TF.Y Z) k le_top hk t :=
      (H0.val_pull (π₀ TF.X Z) le_top zz (pIdx _ _ k) hTop hz3 hπ1 hπ2 t).trans (val_congr_pt e2 k hπ1 hπ2 le_top hk t)
    have e5 : H0.val zz (pIdx _ (inc₀ TF.X Z) k') hTop hz2 (sOf t) =
        H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) *
          H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G :=
      C.val_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) zz
        hTop hz3 hz4 hz2
    rw [e5, e4, Units.val_mul, IsUnit.unit_spec]
    ring

end GlobalTheory.OrbitSep
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspRule_of_boundaryVanishing_componentSection : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)) (L : LB (X₀ TF.Y Z)) (hL : L.IsLB), CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z _) → ∃ Φ : H0 (s₀ TF.Y Z) L ⊤ → Rul Y.d.Xo₂ Y.d.c₂, (∀ t, nonzeroLocus (toSec t) ≤ (j₀ TF.Y Z).opensRange → Φ t ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) ∧ ∀ (y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ) (v : Sp ℂ ⟶ V₀ TF.Y Z), v ≫ i₀ TF.Y Z = ptF y → ∀ (k : L.ι) (hk : ⊤ ≤ (v ≫ j₀ TF.Y Z) ⁻¹ᵁ L.U k), ∃ lam : ℂˣ, ∀ t, evR Y.d.Xo₂ Y.d.c₂ (Φ t) y = lam * H0.val (v ≫ j₀ TF.Y Z) k le_top hk t := by
  atlas_forward_decl GlobalTheory.OrbitSep.exists_rule_of_cls_pull
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

theorem val_ofSec_ne_zero {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) {B : LB X} (θ : B.Sec) (z : Sp ℂ ⟶ X)
    (k : B.ι) (hk : ⊤ ≤ z ⁻¹ᵁ B.U k) (hz : ∀ s, z s ∈ nonzeroLocus θ) :
    H0.val z k le_top hk (H0.ofSec p ⊤ θ) ≠ 0 := by
  refine (H0.val_ofSec z k le_top hk θ).trans_ne ?_
  have h : ⊤ ≤ z ⁻¹ᵁ X.basicOpen (θ.f k) := fun s hs =>
    (X.mem_basicOpen _ _ (hk hs)).2 ((isUnit_ger_iff θ (hk hs)).2 (hz s))
  rw [← TangentOrigin.evalPt_res z (X.basicOpen_le _) hk h]
  exact ((X.toRingedSpace.isUnit_res_basicOpen (θ.f k)).map _).ne_zero

theorem exists_chart_pt {X : Scheme.{0}} {B : LB X} (hB : B.IsLB) (z : Sp ℂ ⟶ X) : ∃ k, ⊤ ≤ z ⁻¹ᵁ B.U k := by
  obtain ⟨k, hk⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hB (z (IsLocalRing.closedPoint ℂ))
  refine ⟨k, fun s _ => ?_⟩
  obtain rfl : s = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hk

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := GlobalTheory.HSApp.cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih => rw [succ_nsmul, GlobalTheory.HSApp.cls_common_add C, ih, succ_nsmul]

set_option maxHeartbeats 2000000 in

theorem separate_orbit (hP2 : Hypotheses2) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSg : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS)
    (hLie : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂))
    {I : Ideal (𝓞 D.host.E)} {g : ℕ} (hI : NeatPrime I g ((T.Q.Dw j).p + (T.Q.Dw j).q)) (hM : Y.d.l₂.Mb ≤ I)
    (hS : ∀ γ ∈ S, UnipAt I γ) (s : ℕ)
    (hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ s) (Z : Comp Y.d.Xo₂ Y.d.c₂) :
    ∃ y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z y ∧
      ∀ [Fintype {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)}]
        (a : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} → ℂ),
        (∀ u ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) ((s : ℤ) • hodgeWt (T.Q.Dw j)) 0),
          ∑ h, a h * evR Y.d.Xo₂ Y.d.c₂ u (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) = 0) → a = 0 := by
  have hP : Hypotheses₂ := GlobalTheory.T.stronger_published_hypotheses_imply hP2
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdim : 1 ≤ (T.Q.Dw j).dim := Nat.mul_pos (Nat.mul_pos (by omega) hp) hq
  have hfl : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) := by
    refine Nat.mul_pos (by omega) ?_
    exact Nat.choose_pos (by omega)
  obtain ⟨TF⟩ := GlobalTheory.T.toroidal_flag_nonempty hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hfl
  have hF := hY.geo
  have hV := GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hF
  obtain ⟨hint, hsm, hpr, hgc, hsurj, hnorm, hgen⟩ := GlobalTheory.T.compactificationComponent_integral_smooth_projective _ _ _ _ _ _ TF Z hF
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_complexFramedPoint_over_componentGenericPoint _ _ _ _ Y.d.Xo₂ Y.d.c₂ Z
  have hyZ : LiesOn Z y := fun s => hy s ▸ (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)).mem
  refine ⟨y, hyZ, fun a ha => ?_⟩
  have lift : ∀ w : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z w → ∃ v : Sp ℂ ⟶ V₀ TF.Y Z, v ≫ i₀ TF.Y Z = ptF w := fun w hw =>
    ⟨IsOpenImmersion.lift (i₀ TF.Y Z) (ptF w) (by
      rintro _ ⟨s, rfl⟩
      exact ⟨⟨_, (j_mem_barComp Z _).2 (hw s)⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨v₁, hv₁⟩ := lift y hyZ
  choose v hv using fun h : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} => lift _ h.2
  obtain ⟨Γ, ρ, hΓ, hρ, hmem⟩ := GlobalTheory.T.componentStabilizer_acts_by_levelChange _ _ _ _ _ _ TF.Y Z hpq hA S
  obtain ⟨X', W, φ, ℓ, ρ', q, sW, hint', n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ :=
    GlobalTheory.T.equivariant_normal_projective_compactification Y.d.c₂.F _ _ (s₀ TF.Y Z) (j₀ TF.Y Z) Γ ρ hpr ⟨v₁ (IsLocalRing.closedPoint ℂ)⟩ hnorm hρ.1
  obtain ⟨δ, hδ, eδ, hlin⟩ := GlobalTheory.T.exists_line_bundle_descends_hodge hP2 _ _ _ _ _ _ TF Z hpq hA hF
  obtain ⟨N, hN, eN⟩ := GlobalTheory.T.exists_descent_linearised_lineBundle_finiteGroup_quotient Y.d.c₂.F X' W q sW Γ ρ' _ _ (n7 ▸ n2) n6
    (hlin I g hI hM Γ Γ.subtype ρ (fun γ => hS _ (hΓ γ.2)) hρ X' φ ℓ ρ' n1 n2 n3 n4 n5)
  let K := CanonLB.all (s₀ TF.Y Z) (T.Q.Dw j).dim
  obtain ⟨κ, hκ, eκ, θ, hθ⟩ := GlobalTheory.T.exists_toroidalCanonicalBundle_weight_line _ _ _ _ _ _ TF Z hpq hF K
  set m := ((T.Q.Dw j).dim + 1).choose 2 + 1 with hm
  obtain ⟨t, rfl⟩ : ∃ t, s = m + t := Nat.exists_eq_add_of_le (by omega)
  obtain ⟨N', hN', eN'⟩ := cls_surj (t • cls δ hδ - cls κ hκ)
  obtain ⟨B, hB, eB⟩ := cls_surj (m • cls δ hδ + cls N' hN')
  have C := common₀ TF.X Z
  have nef : ∀ (L : LB (X₀ TF.Y Z)) (hL : L.IsLB) (w : AllWt.Weight (T.Q.Dw j)), GapGe 0 w →
      CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z w) (isLB_L₀ TF.X Z w) →
      (letI := algebraΓOfHom (s₀ TF.Y Z); IsNef Y.d.c₂.F L) := fun L hL w hw e =>
    GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective _ _ _ _ _ _ L hL _ _ (π₀_s₀ TF.X Z) hpr hV.2.1 hsurj e
      (GlobalTheory.T.nef_line_bundle_weight_gap hP hQ.nef hLie _ _ _ _ _ _ TF Z hF w hw)
  have ens : ∀ n : ℕ, cls (L₀ TF.X Z ((n : ℤ) • hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) =
      n • cls (L₀ TF.X Z (hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) := fun n => by
    rw [natCast_zsmul]; exact cls_nsmul (common₀ TF.X Z) n _
  have nefN' := nef N' hN' ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (gapGe_sub_kapBase _ (by omega)) (by
    have h := GlobalTheory.HSApp.cls_common_add (common₀ TF.X Z) ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (kapBase _)
    rw [sub_add_cancel] at h
    rw [eN', map_sub, map_nsmul, eδ, eκ, ← ens, sub_eq_iff_eq_add]
    exact h)
  have hKB := isLB_tens K.isLB hB
  have hθB := LB.isLB_div hκ K.isLB
  obtain ⟨Φ, hΦ, hval⟩ := GlobalTheory.T.exists_cuspRule_of_boundaryVanishing_componentSection D T j Y e o hY hf Z TF (((m + t : ℕ) : ℤ) • hodgeWt (T.Q.Dw j)) _
    (isLB_tens hθB hKB) (by
      rw [cls_tens hθB hKB, cls_div hκ K.isLB, cls_tens K.isLB hB, eB, eN', ens, ← eδ, ← map_nsmul]
      refine congrArg _ ?_
      have key : ∀ (A : Type 1) [AddCommGroup A] (a b k : A) (m t : ℕ),
          b - k + (k + (m • a + (t • a - b))) = (m + t) • a := fun A _ a b k m t => by
        rw [add_nsmul, ← add_assoc, sub_add_cancel, add_left_comm, add_sub_cancel]
      exact key _ _ _ _ _ _)
  choose k hk using fun h => exists_chart_pt hKB (v h ≫ j₀ TF.Y Z)
  choose k' hk' using fun h => exists_chart_pt hθB (v h ≫ j₀ TF.Y Z)
  choose lam hlam using fun h => hval _ (v h) (hv h) (k' h, k h) (fun s hs => ⟨hk' h hs, hk h hs⟩)
  have hc : ∀ h, H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ) ≠ 0 := fun h =>
    val_ofSec_ne_zero _ θ _ _ _ fun s => hθ ▸ ⟨v h s, rfl⟩
  have hvρ : ∀ h, v h = v₁ ≫ (ρ ⟨h.1, hmem _ h.1.2 y hyZ h.2⟩).hom := fun h => by
    rw [← cancel_mono (i₀ TF.Y Z), hv, Category.assoc, hρ.2 _ ℂ y v₁ hv₁]; rfl
  have h1 : LiesOn Z (move Y.d.Xo₂ Y.d.c₂ ((1 : S) : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
    rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ
  have key := GlobalTheory.T.sections_separate_quotient_generic_fibre_descends hP2.q15 hQ.nef hP2.q16 Y.d.c₂.F (algebraMap _ ℂ) (X₀ TF.Y Z) X' W (V₀ TF.Y Z) (s₀ TF.Y Z) _ φ q sW
    (j₀ TF.Y Z) ℓ hpr hgc hdim n2 n8 n10 n11 n7 inferInstance n3 n4 K δ N' B hδ hN' hB N hN m eN
    (nef δ hδ _ gapGe_hodgeWt eδ) (GlobalTheory.T.descended_bundle_hodge_class hP2 hG hQ hSg hKS _ _ _ _ _ _ TF Z hp hq hF δ hδ eδ) nefN' (by omega) eB _ v
    (fun h h' e => ?_) (fun h => ?_) (fun h h' => ?_) ⟨⟨1, h1⟩, fun s => hgen _ ?_⟩ k hk
    (fun h => a h * (lam h * H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ))) fun u => ?_
  · funext h
    exact (mul_eq_zero.1 (congrFun key h)).resolve_right (mul_ne_zero (lam h).ne_zero (hc h))
  · have e' := (hv h').symm.trans (e ▸ hv h)
    have e₂ : move Y.d.Xo₂ Y.d.c₂ (h'.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y =
        move Y.d.Xo₂ Y.d.c₂ ((h.1 * h'.1⁻¹ : S) : LevelAut (T.Q.Dw j) Y.d.l₂)
          (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
      rw [← LevDesc.move_mul hpq hA']; simp
    rw [e₂] at e'
    have := GlobalTheory.T.levelAutomorphism_unipotent_fixes_complexPoint_eq_one _ _ _ _ _ _ hpq hA I g hI hM _ (hS _ (h.1 * h'.1⁻¹).2) _ e'
    exact Subtype.ext (mul_inv_eq_one.1 (Subtype.ext this))
  · have e₁ : TF.Y.j ≫ TF.Y.s = pullback.snd _ _ := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over]
      exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
    rw [← Category.assoc (j₀ _ _), j₀_ι, Category.assoc, e₁, ← Category.assoc, hv]
    exact pullback.lift_snd _ _ _
  · rw [hvρ h, hvρ h', Category.assoc, Category.assoc, reassoc_of% n5, reassoc_of% n5, n6.comp_eq, n6.comp_eq]
  · change (v ⟨1, h1⟩ ≫ i₀ TF.Y Z) s = _
    rw [hv]
    simp only [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']
    exact hy s
  · let P := tensChart hθB hKB
    have hu := ha _ (hΦ (P.mul (H0.ofSec (s₀ TF.Y Z) ⊤ θ) u) fun x hx => ?_)
    · rw [← hu]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [hlam, mul_assoc, mul_assoc]
      exact congrArg (fun x => a h * (lam h * x)) (P.val_mul _ _ (k' h, k h) _ le_top (hk' h) (hk h) _).symm
    · obtain ⟨τ, ha', hb', hc'⟩ := P.cover x
      have hu := (isUnit_ger_iff _ hc').2 hx
      rw [ger_toSec, P.germ_mul _ _ τ x _ ha' hb' hc', H0.germ_ofSec] at hu
      exact hθ ▸ (isUnit_ger_iff θ ha').1 (isUnit_of_mul_isUnit_left hu)

end GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

open Formalism.MainNotions Formalism.L2.Theta GlobalTheory.DegVal GlobalTheory.DegCmp GlobalTheory.BadCount

theorem exists_cusp_levDet_regular : Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ S u * f = 0 → f = 0 := by
  classical
  intro hP2 hG hQ hSg hKS hLie D T hT j hp hq hf hj Y e o hY _ hg fr S hS
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdat := hT.pins.2.2.2 j hj
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hdat.1, hdat.2.1]; exact Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hT.pins.2.1.1]
  obtain ⟨I, g, hI, hMb, hU⟩ := GlobalTheory.T.exists_neatPrime_levelAutSubgroup_unipotent D _ (T.Q.Dw j) Y.d.l₂ ⟨_, hM⟩ (hr ▸ hg) fr S hS
  have hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ cZeroN D j := by
    have := (cZeroN_isLeast D j).1.2.1
    rw [hr, Datum.dim, GlobalTheory.FlagDim.finrank_host_div_two, hdat.1, hdat.2.1]
    omega
  choose y hyZ hy using separate_orbit hP2 hG hQ hSg hKS hLie Y hY hf hp hq S hI hMb hU _ hs
  have : Finite (Comp Y.d.Xo₂ Y.d.c₂) := CompFin.finite_comp _ _
  let G := wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0
  let ev : Comp Y.d.Xo₂ Y.d.c₂ → Y.V G →ₗ[Y.d.c₂.F] (S → ℂ) := fun Z => LinearMap.pi fun h =>
    evalL (K := Y.d.c₂.F) (fun R _ _ => FrPt Y.d.Xo₂ Y.d.c₂ R) (fun φ y z => FrMap φ y z)
      (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z)) ∘ₗ (Y.V G).subtype
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_vector_groupDeterminants_ne_zero Y.d.c₂.F (Y.V G) S _ ev
    (fun Z => {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z))}) (fun _ h => h.1)
    (fun Z => (AllWt.suppOn Z).comap (Y.V G).subtype)
    (fun Z => ⟨⟨1, by rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ Z⟩, rfl⟩)
    (fun Z v hv h hh => hv ℂ _ ((AllWt.liesOff_iff Z _).2 fun h' => hh ⟨⟨h, h'⟩, rfl⟩))
    (fun Z a ha => hy Z a fun u hu => ha ⟨u, hu.1⟩ hu.2)
  have hu' := AllWt.cuspW_le_secZ _ u.2
  refine ⟨u, u.2, GlobalTheory.T.integerExponentSection_mul_eq_zero_imp_eq_zero _ _ _ _ _ _ _ _ (LevDesc.levDet_mem_secZ hpq hA' hu') fun Z => ⟨y Z, hyZ Z, ?_⟩⟩
  have ht := GlobalTheory.FlagTan.fromTest_of_isLocalRing (y Z)
  let χ : Rul Y.d.Xo₂ Y.d.c₂ →+* ℂ :=
    { toFun := fun f => evR Y.d.Xo₂ Y.d.c₂ f (y Z)
      map_one' := evalAt_one _ _ _ ht
      map_mul' := fun f g => evalAt_mul _ _ f g _
      map_zero' := evalAt_zero _ _ _
      map_add' := fun f g => evalAt_add _ _ f g _ }
  have e₁ := χ.map_det (LevDesc.levMat Y.d.Xo₂ Y.d.c₂ S u)
  refine fun h0 => hu Z ?_
  rw [← h0]
  refine Eq.trans ?_ (e₁.symm.trans ?_)
  · congr 1
    ext h g
    exact (GlobalTheory.LevelKeeps.evR_transl hpq hA' _ hu' (y Z)).symm
  · change χ _ = χ _
    unfold levDet
    congr!

end GlobalTheory.OrbitSep
end
end
