import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.IpEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.StableIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.TypeIDisc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ThickNonSS
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CoefficientExtensionPreservesConditionsAndDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConstMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charK (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI := hp
  have hpp : p.Prime := CharP.char_is_prime K p
  by_contra hne
  have hpl : p ≠ l := fun h => hne (h ▸ hp)
  have hu : IsUnit (p : ℤ_[l]) := by
    by_contra h
    rw [PadicInt.not_isUnit_iff, ← Int.cast_natCast, PadicInt.norm_int_lt_one_iff_dvd,
      Int.natCast_dvd_natCast] at h
    exact hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out) hpp).mp h).symm
  have := hu.map (algebraMap ℤ_[l] K)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

private theorem unip_pow (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [CharP K l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hM : (M.map (PowerSeries.constantCoeff : PowerSeries K →+* K)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n * m) - 1) i j ∈ maximalIdeal (PowerSeries K) ^ m := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact (IsEmpty.false i).elim
  haveI : CharP (PowerSeries K) l :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective l
  set N := M - 1 with hN
  have hMN : M = 1 + N := by rw [hN]; abel
  have hfrob : M ^ l ^ (n * m) - 1 = N ^ l ^ (n * m) := by
    rw [hMN, add_pow_char_pow_of_commute (p := l) (h := Commute.one_left N), one_pow, add_sub_cancel_left]
  let f := (PowerSeries.constantCoeff : PowerSeries K →+* K).mapMatrix (m := Fin n)
  have hNn : f (N ^ n) = 0 := by
    rw [map_pow, hN, map_sub, map_one, RingHom.mapMatrix_apply]
    have := Matrix.aeval_self_charpoly (M.map PowerSeries.constantCoeff)
    rw [hM] at this
    simpa [map_pow, map_sub] using this
  have h1 : ∀ a b, (N ^ n) a b ∈ maximalIdeal (PowerSeries K) := by
    intro a b
    have h0 : PowerSeries.constantCoeff ((N ^ n) a b) = 0 := by
      have := congrFun (congrFun hNn a) b
      simpa [f, RingHom.mapMatrix_apply] using this
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, h0]
    exact not_isUnit_zero
  have hpow : ∀ (I : Ideal (PowerSeries K)) (P : Matrix (Fin n) (Fin n) (PowerSeries K)),
      (∀ a b, P a b ∈ I) → ∀ k : ℕ, ∀ a b, (P ^ k) a b ∈ I ^ k := by
    intro I P hP k
    induction k with
    | zero => intro a b; simp [Ideal.one_eq_top]
    | succ k ih =>
      intro a b
      rw [pow_succ P, Matrix.mul_apply, pow_succ I]
      exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (ih a c) (hP c b)
  have hle : n * m ≤ l ^ (n * m) := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  rw [hfrob, show l ^ (n * m) = n * m + (l ^ (n * m) - n * m) by omega, pow_add, pow_mul,
    Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hpow _ _ h1 m i c)

theorem UpperTheory.V.Pa.rhoPL :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (H : OpenNormalSubgroup F.Γ), (∀ g ∈ H, ∃ h : F.η g = 1, ((mat x.ρ ⟨g, h⟩).map (PowerSeries.constantCoeff : x.A →+* x.K)).charpoly = (Polynomial.X - 1) ^ n) → ∀ g : F.G₀, (g : F.Γ) ∈ PL l H.toSubgroup → x.ρ g = 1 := by
  intro l _ F n x H hH g hg
  haveI : CharP x.K l := charK l x.K
  have key : ∀ m : ℕ, ∀ i j, (mat x.ρ g - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m := by
    intro m
    let φ : F.G₀ →* Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m) :=
      (Ideal.Quotient.mk (maximalIdeal (PowerSeries x.K) ^ m)).mapMatrix.toMonoidHom.comp (mat x.ρ)
    have hφ : ∀ y, φ y = 1 ↔ ∀ i j, (mat x.ρ y - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m := by
      intro y
      rw [← Matrix.ext_iff]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
      show Ideal.Quotient.mk _ (mat x.ρ y i j) =
          (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j ↔ _
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    let T : Subgroup F.Γ := φ.ker.map F.η.ker.subtype
    have hTopen : IsOpen (T : Set F.Γ) := by
      have hK : IsOpen (φ.ker : Set F.G₀) := by
        have e : (φ.ker : Set F.G₀) = ⋂ i, ⋂ j, {y : F.G₀ | φ y i j =
            (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j} := by
          ext y
          simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
          exact Matrix.ext_iff.symm
        rw [e]
        exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
          (x.cont i j m : IsLocallyConstant fun y : F.G₀ => φ y i j).isOpen_fiber _
      rw [Subgroup.coe_map]
      exact F.η_open.isOpenMap_subtype_val _ hK
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hTopen T.one_mem
    let W : OpenNormalSubgroup F.Γ :=
      { toSubgroup := T.normalCore
        isOpen' := Subgroup.isOpen_mono (H₁ := V.toSubgroup)
          (Subgroup.normal_le_normalCore.mpr fun a ha => hV ha) V.toOpenSubgroup.isOpen
        isNormal' := Subgroup.normalCore_normal T }
    have hW : ∀ h ∈ H.toSubgroup, ∃ e, h ^ l ^ e ∈ W := by
      intro h hh
      refine ⟨n * m, ?_⟩
      show ∀ b : F.Γ, b * h ^ l ^ (n * m) * b⁻¹ ∈ T
      intro b
      rw [← conj_pow]
      have hbh : b * h * b⁻¹ ∈ H.toSubgroup := H.isNormal'.conj_mem h hh b
      obtain ⟨he, hchar⟩ := hH _ hbh
      refine Subgroup.mem_map.mpr ⟨⟨b * h * b⁻¹, he⟩ ^ l ^ (n * m), ?_, by simp⟩
      rw [MonoidHom.mem_ker, hφ, map_pow]
      exact unip_pow l x.K n m _ hchar
    have hgW : (g : F.Γ) ∈ T.normalCore := by
      have h2 := hg
      simp only [UpperTheory.V.Pa.PL, Subgroup.mem_iInf] at h2
      exact h2 W hW
    have h1 := T.normalCore_le hgW
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp h1
    have hyg' : y = g := Subtype.ext hyg
    rw [← hyg']
    exact (hφ y).mp hy
  apply Units.ext
  show mat x.ρ g = 1
  refine Matrix.ext fun i j => ?_
  have h0 : (mat x.ρ g - 1) i j ∈ ⨅ m, maximalIdeal (PowerSeries x.K) ^ m :=
    Submodule.mem_iInf _ |>.mpr fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
    Ideal.mem_bot, Matrix.sub_apply, sub_eq_zero] at h0
  exact h0
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2

theorem chain_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) (P : CohP)
    (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (hn : 0 < n) (hS : V0.S' = s.S)
    (hL : LocCFT s) (hμ : ∃ g : V0.frame.G₀, PadicInt.toZMod ((V0.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) (hA : HasAut B J)
    (h : ℕ) (x : Fin (h + 1) → Point r) (f : ∀ i, B.B →ₐ[O] (x i).A) (hx : ∀ i, (x i).NiceI ∨ (x i).NiceE)
    (hf : ∀ i, B.IsPt (x i) (f i)) :
    ChainConcl (pairOf B.u) J (fun i => RingHom.ker (f i)) ∧
      ∀ i, (x i).TypeI → ∀ q : Ideal B.B, q ≤ RingHom.ker (f i) → DiscSt B.u.D q := by
  haveI := IsCoef.char (l := l) (O := O)
  haveI := IsCoef.finite (l := l) (O := O)
  haveI := IsCoef.complete (l := l) (O := O)
  obtain ⟨hΦ, hT⟩ := hP P l L Ω s V0 O n r hS
  have hI := (ipEq l L Ω s V0 O n r).1
  choose y j jinj jloc _ jD jψ y3 y4 yI using fun i => hN l V0.frame O n r (x i) (globOf r V0).frame.Iu s.odd hn
    (fun u => ((hI u).2.symm.trans (hI u).1).le) (hx i)
  obtain ⟨q, sg, z, j', k, al, hsg, hE, hcard, hdet, heig⟩ := hC l (globOf r V0).frame n h y s.odd hΦ hμ y3
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := hT q sg hsg
  obtain rfl : T.sg = sg := funext hTs
  obtain ⟨A⟩ := hA T Pl
  choose ι hι using fun i => Det.constMap ((j' i).comp (j i))
  have hD : ∀ i, GDet.ofRep (mat (z i).ρ) = (GDet.ofRep (mat (x i).ρ)).map ((j' i).comp (j i)) := fun i => by
    exact (Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).2.2.trans (congrArg (·.map (j' i)) (jD i))
  have hker : ∀ i, ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → (z i).ρ g = 1 := fun i => by
    refine rhoPL l (globOf r V0).frame n (z i) T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    refine ⟨e1, ?_⟩
    have hcc : (PowerSeries.constantCoeff : (z i).A →+* (z i).K).comp ((j' i).comp (j i)) =
        (ι i).comp PowerSeries.constantCoeff := RingHom.ext fun a => by
      haveI := jloc i
      haveI := (hE i).2.1
      have m1 : ¬ IsUnit (a - PowerSeries.C (PowerSeries.constantCoeff a)) := by
        simp [PowerSeries.isUnit_iff_constantCoeff]
      have m2 : ¬ IsUnit (j' i (j i (a - PowerSeries.C (PowerSeries.constantCoeff a)))) := fun u =>
        m1 (IsLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ u))
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not, map_sub, map_sub, map_sub, sub_eq_zero] at m2
      have m3 := congrArg PowerSeries.constantCoeff (hι i (PowerSeries.constantCoeff a))
      exact m2.trans (m3.trans (PowerSeries.constantCoeff_C _))
    have e3 : (GDet.ofRep (mat (z i).ρ)).map (PowerSeries.constantCoeff : (z i).A →+* (z i).K) =
        r.Dbar.map ((ι i).comp (algebraMap (ResidueField O) (x i).K)) := by
      rw [hD i]
      refine Eq.trans (b := (GDet.ofRep (mat (x i).ρ)).map ((ι i).comp PowerSeries.constantCoeff)) (by rw [← hcc]; rfl) ?_
      exact congrArg (·.map (ι i)) (x i).red
    rw [map_ofRep, Resid.Dbar, map_ofRep] at e3
    have e4 := congrArg (·.chi (MonoidAlgebra.single ⟨g, e1⟩ 1)) e3
    simp only [chi_ofRep] at e4
    refine e4.trans ?_
    have e5 : W.diagRep r.chib ⟨g, e1⟩ = 1 := by
      change Matrix.diagonal _ = _
      simp only [e2, Units.val_one, Matrix.diagonal_one]
    refine (chi_ofRep _ _).trans ?_
    change ((RingHom.mapMatrix ((ι i).comp (algebraMap (ResidueField O) (x i).K))) (W.diagRep r.chib ⟨g, e1⟩)).charpoly = _
    rw [e5, map_one, Matrix.charpoly_one, Fintype.card_fin]
  let pt : ∀ i, Pt T (pairOf B.u) (n * Module.finrank ℚ (Lp L) + n * T.q) := fun i =>
    letI : Algebra O (z i).K := ((ι i).comp (algebraMap O (x i).K)).toAlgebra
    { x := z i
      k := k i
      al := al i
      eig := heig i
      b1 := h1 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hL hμ (hker i)
        ((Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).1 _ (y4 i)) (heig i) (hdet i)
      b2 := h2 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hμ (hker i) (heig i)
      f := { ((j' i).comp (j i)).comp (f i : B.B →+* (x i).A) with
        commutes' := fun a => by
          change ((j' i).comp (j i)) (f i (algebraMap O B.B a)) = _
          rw [AlgHom.commutes]
          rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]
          exact hι i _ }
      maps := ⟨by rw [hD i, ← (hf i).1]; rfl, fun v a => by
        rw [(hE i).2.2.2.2.2 v a, jψ i v a, ← (hf i).2 v a]; rfl⟩ }
  have hk : ∀ i, RingHom.ker (pt i).f = RingHom.ker (f i) := fun i => by
    ext b
    change j' i (j i (f i b)) = 0 ↔ f i b = 0
    rw [map_eq_zero_iff _ (hE i).1, map_eq_zero_iff _ (jinj i)]
  refine ⟨?_, fun i hi q hq => ?_⟩
  · have := hR l _ (globOf r V0) T n O (residOf r) B.B (pairOf B.u) J _ A s.odd
      ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
      (fun N b => by
        obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
        refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
        rintro _ (⟨a, g, -, -, rfl⟩ | e)
        · exact Or.inl ⟨a, g, rfl⟩
        · exact Or.inr e) h pt hcard
    simpa only [hk] using this
  · exact Det.typeIDisc (z i) B.u.D (((j' i).comp (j i)).comp (f i : B.B →+* (x i).A)) ((hE i).2.2.2.2.1.trans (yI i hi)) (pt i).maps.1 q (hq.trans (hk i).ge)

theorem pFromAut_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) : PfromAut := by
  intro P l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J hn hS hL hμ hA
  have key := chain_of hN hC hP h1 h2 hR P l L Ω s V0 O n r B J hn hS hL hμ hA
  have hE : augmentationIdealKernel (pairOf B.u) = augmentationIdealKernel B.u := by
    rw [(ipEq l L Ω s V0 O n r).2 B]
    ext z
    simp only [augmentationIdealKernel, UniversalOrdinaryDeterminantRing.GroupAlgebraKernelIdeal, GDet.chBar, pairGens, UniversalOrdinaryDeterminantRing.E0gens, Set.mem_setOf_eq, Set.union_assoc]
  refine ⟨fun x f hx hf hJ q hq => ?_, fun h x f e hx hf he h₁ q hq hs => ?_⟩
  · obtain ⟨k1, k2⟩ := key 0 (fun _ => x) (fun _ => f) (fun _ => Or.inl hx) fun _ => hf
    exact k1 Fin.elim0 (fun i => i.elim0) ⟨_, RingHom.ker_isPrime f, k2 0 hx.2.1 _ le_rfl, hJ, le_rfl⟩ q.asIdeal q.isPrime hq
      (Or.inl (k2 0 hx.2.1 _ hq))
  · obtain ⟨k1, -⟩ := key h x f (fun i => Or.inr (hx i)) hf
    obtain ⟨q₁, a1, a2, a3⟩ := h₁
    refine k1 (fun i => (e i).asIdeal) (fun i => ⟨(e i).isPrime, hE ▸ Det.thickNonSS B _ (he i).1, (he i).2⟩)
      ⟨_, q₁.isPrime, (Det.stableIff B _).1 a1, a2, a3⟩ q.asIdeal q.isPrime hq ?_
    exact hs.imp (Det.stableIff B _).1 fun t => hE ▸ Det.thickNonSS B _ t

end UpperTheory.V.Pa
end
