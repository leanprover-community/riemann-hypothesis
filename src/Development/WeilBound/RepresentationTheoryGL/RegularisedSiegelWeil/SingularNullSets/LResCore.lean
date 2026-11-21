import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGoodCompatThree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LResCore

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

theorem kAt_le_kOff {v : Pl D} {S : Finset (Pl D)} (hv : v ∉ S) : KAt D n v ≤ KOff D n S := by
  intro k hk
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hk
  rw [mem_atPts] at hA
  rw [KOff, mem_levelOff]
  refine ⟨hA.1, fun w hw => hA.2 w ?_, fun w _ => ?_⟩
  · rw [Finset.mem_singleton]
    rintro rfl
    exact hv hw
  · by_cases hwv : w = v
    · subst hwv
      have h1 : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) := hK.1
      exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 w)
    · rw [hA.2 w (by rwa [Finset.mem_singleton])]
      exact one_mem _

theorem isCompact_kAt (v : Pl D) : IsCompact (KAt D n v : Set (G D n)) := by
  have : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  have hK : IsCompact (K D n : Set (G D n)) := isCompact_levelAll (isCMExt_host D) _ _ _
  have e : (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) = (finPts D.sp.cm.sig (Jst D n) : Set (G D n)) ∩
      ⋂ w, ⋂ (_ : w ∉ ({v} : Finset (Pl D))), (proj D.sp.cm.sig (Jst D n) w) ⁻¹' {1} := by
    ext k
    simp only [SetLike.mem_coe, mem_atPts, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  have hA : IsClosed (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) := by
    rw [e]
    exact (isClosed_finPts _ _).inter (isClosed_iInter fun w => isClosed_iInter fun _ =>
      isClosed_singleton.preimage (continuous_proj _ _ w))
  have e2 : (KAt D n v : Set (G D n)) = (K D n : Set (G D n)) ∩ (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) :=
    Subgroup.coe_inf _ _
  rw [e2]
  exact hK.inter_right hA

theorem exists_haar_prob {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] (K₀ : Subgroup X) (h : IsCompact (K₀ : Set X)) :
    ∃ ν : Measure K₀, ν.IsHaarMeasure ∧ IsProbabilityMeasure ν := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.mp h
  refine ⟨Measure.haarMeasure ⊤, inferInstance, ⟨?_⟩⟩
  simpa using Measure.haarMeasure_self (G := K₀) (K₀ := ⊤)

theorem isLaw_sw {t : ℕ} {B : HSp D} (hB : B.rank = n + t) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μB : Measure (Mx D B.rank n)} {ωB : G D n →* Module.End ℂ (schwartzA θ B.rank n)}
    (hω : IsWeilSch ψ χ θ B μB ωB) (Φ : schwartzA θ B.rank n) :
    IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, rfl, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  have e' : ωB (m * u * g) Φ = ωB m (ωB u (ωB g Φ)) := by
    rw [map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D B.rank n) ⬝ a.1 : Mx D B.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have e3 : ((B.rank : ℂ) / 2) = (t : ℂ) / 2 + (n : ℂ) / 2 := by
    rw [hB]; push_cast; ring
  show (ωB (m * u * g) Φ).1 0 = _ * _ * (ωB g Φ).1 0
  rw [e', hω.levi m a hm, hω.unip u b hu, z1, z2, e3]
  simp [halfTr]

theorem theta_mul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (Ψ : schwartzA θ V.rank n) (g u : G D n) (h : GA D V) : theta ω Ψ (g * u) h = theta ω (ω u Ψ) g h := by
  simp only [theta, map_mul]
  rfl

end PositivityTheory.Rg.Rsw.L.LResCore

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open PositivityTheory.Rg.Rsw.L.LResCore

theorem resCore : Polar → CfFJ → IdemEx → GoodEv → FixW → WMaj → JPos → CfRel → CfInv → CutLow → CutId → ThBdd → ThCoef →
    IkSch → IkEq → ResCore := by
  classical
  intro hPolar hCfFJ hIdem hGoodEv hFixW hWMaj hJPos hCfRel hCfInv hCutLow hCutId hThBdd hThCoef hIkSch hIkEq
    D n t B W hd hn hbig hlt hpos ψ hψ χ hχ hη θ hθ μB μW hμB hμW ωB ωW hωB hωW H hH hHlev Φ U d E σ hcont ε hrad
  obtain ⟨dd⟩ := hd
  have hBr : B.rank = n + t := by have := dd.rank_add; omega
  have hηB : ResEta D χ B.rank := GlobalTheory.HeckeCharsOfSquare.resEta_of_mod hη (by omega)
  have hφc : Continuous (fun g => (ωB g Φ).1 0) :=
    (hWMaj D n B ψ hψ χ hχ hηB θ hθ μB hμB ωB hωB Φ).1.comp (continuous_id.prodMk continuous_const)
  have hφlaw : IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := isLaw_sw hBr hωB Φ
  obtain ⟨-, hP2, -⟩ := hPolar D n W.rank t hn hbig ψ hψ χ hχ hη (fun h0 => absurd h0 (by omega)) θ hθ H hH _ hφc hφlaw
    U d E σ hcont ε hrad
  obtain ⟨UH, hUHo, hUH⟩ := hHlev
  have : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.PlaceGen.exists_levelOff_le D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) UH hUHo
  obtain ⟨S₂, hS₂⟩ := hFixW D n B ψ hψ χ hχ hηB θ hθ μB hμB ωB hωB
  obtain ⟨S₃, hS₃⟩ := hGoodEv D θ hθ B.rank n Φ.1 Φ.2
  obtain ⟨nb, lam, 𝓖, hnb, hlam⟩ := GlobalTheory.CompanionTheory.SWCoef.coefDataExists D n
  obtain ⟨v, hvS, C, cc, hKill, hcd, hc0, hcut⟩ := hJPos D n W.rank t hn hpos ψ hψ χ hχ hη nb hnb (S₁ ∪ S₂ ∪ S₃)
  obtain ⟨e, he⟩ := (hIdem D (S₁ ∪ S₂ ∪ S₃)).1
  have hsub2 : S₂ ⊆ S₁ ∪ S₂ ∪ S₃ := fun x hx => by simp [hx]
  have hsub3 : S₃ ⊆ S₁ ∪ S₂ ∪ S₃ := fun x hx => by simp [hx]
  have hv1 : v ∉ S₁ := fun h => hvS (by simp [h])
  have hgood : Good (S₁ ∪ S₂ ∪ S₃) e Φ.1 := hS₃ _ hsub3 e he
  have hKΦ : ∀ k ∈ KAt D n v, ωB k Φ = Φ := fun k hk => hS₂ _ hsub2 e he Φ hgood k (kAt_le_kOff hvS hk)
  have hKH : ∀ k ∈ KAt D n v, ∀ g, H (g * k) = H g := fun k hk g =>
    hUH k (hS₁ (kAt_le_kOff hv1 hk)) (mem_atPts.1 (Subgroup.mem_inf.1 hk).2).1 g
  have hKφ : ∀ k ∈ KAt D n v, ∀ g, (ωB (g * k) Φ).1 0 = (ωB g Φ).1 0 := fun k hk g => by
    rw [map_mul, Module.End.mul_apply, hKΦ k hk]
  obtain ⟨νv, hνH, hνP⟩ := exists_haar_prob (KAt D n v) (isCompact_kAt v)
  have hfam : ∀ z g, ∫ k, cutR nb C (fam H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) z) (g * k) ∂νv =
      cc z * fam H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) z g := by
    intro z g
    refine hcut νv hνH hνP z _ (GlobalTheory.CompanionTheory.RswPolar.continuous_fam hH hφc _ z) (GlobalTheory.CompanionTheory.RswPolar.isLaw_fam hH hφlaw z) ?_ g
    intro k hk g'
    simp only [fam, hKH k hk g', hKφ k hk g']
  have hrel := hCfRel D n χ hχ H hH _ _ hφc hφlaw U d E σ hcont ε hrad nb hnb v C cc hcd νv hνP hfam
  obtain ⟨hcfCA, ⟨N, hN⟩, -⟩ := hCfFJ D n H _ _ U d E σ hcont ε hrad
  have hcfK : ∀ k, ∀ u ∈ KAt D n v, ∀ g, cf d E ((t : ℂ) / 2) ε k (g * u) = cf d E ((t : ℂ) / 2) ε k g :=
    fun k u hu g => hCfInv D n H _ _ U d E σ hcont ε hrad u (hKH u hu) (hKφ u hu) k g
  have hhigh : ∀ k, 2 ≤ k → cf d E ((t : ℂ) / 2) ε k = 0 := by
    have key : ∀ m k, 2 ≤ k → N < k + m → cf d E ((t : ℂ) / 2) ε k = 0 := by
      intro m
      induction m with
      | zero => intro k _ hk; exact hN k (by omega)
      | succ m ih =>
        intro k hk2 hkm
        have hj : ∀ j, k < j → cf d E ((t : ℂ) / 2) ε j = 0 := fun j hj => ih j (by omega) (by omega)
        have h1 := hrel k (by omega) hj
        have h2 := (hCutLow D n W.rank ψ hψ nb hnb v C hKill (cf d E ((t : ℂ) / 2) ε k) (hcfCA k).1 (hcfCA k).2
          (fun u hu g => hcfK k u hu g)).1 (hP2 k hk2)
        funext g
        have h3 := h1 g
        simp only [h2, Pi.zero_apply, integral_zero] at h3
        exact (mul_eq_zero.1 h3.symm).resolve_left hc0
    intro k hk
    exact key (N + 1) k hk (by omega)
  refine ⟨hhigh, ?_⟩
  intro X _ π _ cX κ hcX hcomp hκ hkill
  obtain ⟨a, ha⟩ := GlobalTheory.RegSch.exists_good_frameLat D B
  obtain ⟨νK, hνK, hνK1⟩ := exists_haar_prob _ ha.isCompact_K
  obtain ⟨μ₁, 𝓕₁, hμ₁⟩ := GlobalTheory.MixModel.exists_isCovolOne D t n
  have : LocallyCompactSpace (GA D W) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).1
  let I : IkD dd n := IkD.mk _ ha νK hνK hνK1 μ₁ ⟨𝓕₁, hμ₁⟩ Measure.haar inferInstance
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D W I.m I.haar
  let Ψ : schwartzA θ W.rank n := ⟨ikp I Φ.1, (hIkSch D n t B W dd I θ hθ Φ.1 Φ.2).2⟩
  let Ψ' : schwartzA θ W.rank n := ∑ x ∈ C.s, C.co x • ωW (nb x) Ψ
  have hStg : Stg dd hn ψ χ θ μB μW ωB ωW := ⟨hbig, hlt, hpos, hψ, hχ, hη, hθ, hμB, hμW, hωB, hωW⟩
  obtain ⟨κ', hκ'⟩ := hCutId D n t B W dd hn ψ χ θ μB μW ωB ωW hStg I H hH Φ U d E σ hcont ε hrad nb hnb v C hKill
    (fun k hk => ⟨hKΦ k hk, hKH k hk⟩) 𝓕 h𝓕 Ψ Ψ' rfl rfl
  have hΨinv : ∀ k ∈ KAt D n v, ωW k Ψ = Ψ := fun k hk => Subtype.ext (by
    rw [hIkEq D n t B W dd hn ψ χ θ μB μW ωB ωW hStg I Φ Ψ rfl k, hKΦ k hk])
  obtain ⟨hθc, -, -, hθb, -⟩ := hThBdd D n W ψ hψ χ hχ hη θ hθ μW hμW ωW hωW nb hnb v C hKill Ψ Ψ' hΨinv rfl
  have h𝓕fin : I.m 𝓕 ≠ ⊤ := (hThCoef D n W ψ hψ θ hθ I.m 𝓕 I.haar h𝓕 lam 𝓖 hlam Ψ.1 Ψ.2).1
  have : IsFiniteMeasure (I.m.restrict 𝓕) := isFiniteMeasure_restrict.2 h𝓕fin
  obtain ⟨b, hb⟩ := hθb _ (hcomp.mul (isCompact_kAt (n := n) v))
  have hbound : ∀ x (p : KAt D n v × GA D W), ‖theta ωW Ψ' (cX x * p.1) p.2‖ ≤ b := fun x p =>
    hb _ (Set.mul_mem_mul (subset_closure (Set.mem_range_self x)) p.1.2) p.2
  have hmeas : Measurable (fun q : X × (KAt D n v × GA D W) => theta ωW Ψ' (cX q.1 * q.2.1) q.2.2) :=
    hθc.measurable.comp (((hcX.comp measurable_fst).mul
      (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd))
  have hintx : ∀ x, Integrable (fun p : KAt D n v × GA D W => theta ωW Ψ' (cX x * p.1) p.2)
      (νv.prod (I.m.restrict 𝓕)) := fun x =>
    Integrable.of_bound (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable b
      (ae_of_all _ (hbound x))
  have hint : Integrable (Function.uncurry fun (x : X) (p : KAt D n v × GA D W) =>
      theta ωW Ψ' (cX x * p.1) p.2 * κ x) (π.prod (νv.prod (I.m.restrict 𝓕))) := by
    refine Integrable.mono' ((hκ.norm.const_mul b).comp_fst (νv.prod (I.m.restrict 𝓕)))
      (hmeas.aestronglyMeasurable.mul hκ.aestronglyMeasurable.comp_fst) (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry, norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound q.1 q.2) (norm_nonneg _)
  have hpt : ∀ x, cf d E ((t : ℂ) / 2) ε 1 (cX x) * κ x =
      (cc ((t : ℂ) / 2))⁻¹ * κ' * ∫ p, theta ωW Ψ' (cX x * p.1) p.2 * κ x ∂(νv.prod (I.m.restrict 𝓕)) := by
    intro x
    have h1 := hrel 1 le_rfl (fun j hj => hhigh j hj) (cX x)
    simp only [hκ'] at h1
    rw [integral_const_mul] at h1
    have e2 : ∫ p, theta ωW Ψ' (cX x * p.1) p.2 ∂(νv.prod (I.m.restrict 𝓕)) =
        ∫ u, ∫ h in 𝓕, theta ωW Ψ' (cX x * u) h ∂I.m ∂νv := integral_prod _ (hintx x)
    rw [integral_mul_const, e2, (eq_inv_mul_iff_mul_eq₀ hc0).2 h1.symm]
    ring
  have hzero : ∀ p : KAt D n v × GA D W, ∫ x, theta ωW Ψ' (cX x * p.1) p.2 * κ x ∂π = 0 := by
    intro p
    simp only [theta_mul]
    exact hkill (ωW p.1 Ψ') p.2
  simp only [hpt]
  rw [integral_const_mul, integral_integral_swap hint]
  simp only [hzero, integral_zero, mul_zero]

end PositivityTheory.Rg.Rsw.L

end
end
