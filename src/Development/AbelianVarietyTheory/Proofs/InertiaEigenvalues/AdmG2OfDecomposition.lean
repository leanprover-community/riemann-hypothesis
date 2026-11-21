import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import BuildAid.ForwardExisting
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDecompIffDecomp

section
noncomputable section

namespace GlobalTheory.BlockEnl

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.BlockJumps GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount GlobalTheory.HTW.SumJumps GlobalTheory.Cmp.SmallJumps

theorem multV_oneByOne {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [Algebra.IsSeparable Qp K] [FiniteDimensional Qp LL]
    (hF : IsField BdR) (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1)
    (σ : Representation LL G (Fin 1 → LL)) (e : ℕ)
    (he : ∀ g u c, σ g u c = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e * u c)
    (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD σ τ a = if a = e then 1 else 0 := by
  let χ : Fin 1 → G →* LLˣ := fun _ => ((cycLL PD LL)⁻¹) ^ e
  have hχ : ∀ c g, ((χ c g : LLˣ) : LL) = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e := fun c g => by
    simp [χ, cycLL]
  have hσ : σ = diagRep χ := by
    refine MonoidHom.ext fun g => LinearMap.ext fun u => funext fun c => ?_
    rw [he, diagRep_apply, hχ c]
  rw [hσ, multV_diagRep PD hF, Fin.sum_univ_one]
  exact multV_twist PD hs (Formalism.WeaklyAdmissibleFiltrations.charRep (χ 0)) e (fun g x => by rw [← hχ 0]; rfl) τ a

theorem twistM_one_apply {O Γ : Type} [CommRing O] [Group Γ] (χ : Γ →* Oˣ) (g : Γ) :
    twistM (1 : Γ →* Matrix (Fin 1) (Fin 1) O) χ g 0 0 = ((χ g : Oˣ) : O) := by
  simp [twistM]

set_option maxHeartbeats 1000000 in

theorem blockE_of_isBlockSum (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π) : BlockE D i r ρ π := by
  obtain ⟨e, he⟩ := hB
  intro w hw L' hL τ
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : FiniteDimensional ℚ_[D.nd.l i] ↥L'.1 := L'.2
  let s : Br.G D.nbr i w hw → Formalism.MainNotions.N.GE D.nd := fun g => decS D.nd w (Br.iota D.nbr i w hw g)
  let j := inc D i w hw L' hL
  let f := j.comp (Br.toLLK (D.nbr i w hw))
  have hf : ∀ c, f (toK D.nd i c) = j ((D.nbr i w hw).toLL c) :=
    fun c => congrArg j (Br.toLLK_alg (D.nbr i w hw) c)
  have hχ0 : ∀ (c : ℕ), c + 1 ≤ D.R.t → ∀ g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i (c + 1) g =
      (epsU D.nd i g)⁻¹ ^ c := fun c hc g => by
    have h := D.nd.chi_def i (c + 1) (by omega) hc
    change (D.nd.chi i 1)⁻¹ g * D.nd.chi i (c + 1) g = _
    rw [h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl
  have hχ : ∀ (c : Fin D.R.t) g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i ((c : ℕ) + 1) g =
      (epsU D.nd i g)⁻¹ ^ (c : ℕ) := fun c g => hχ0 c c.2 g
  have hε : ∀ g, j ((D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i)) =
      algebraMap ℚ_[D.nd.l i] ↥L'.1 ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
    intro g
    have h1 : (D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i) =
        algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
      rw [Br.PD, (D.loc _).PD_χ, ← cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
      exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)
    rw [h1]
    exact (IntermediateField.inclusion hL).commutes _
  have hM : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) g v,
      matRep (locE D i w hw L' hL M) g v = ((mapM (toK D.nd i) M (s g)).map f).mulVec v := fun M g v => by
    rw [show (mapM (toK D.nd i) M (s g)).map f = locE D i w hw L' hL M g from
      Matrix.ext fun a b => hf _]
    rfl
  have hs : ∃ x ∈ (Br.PD D.loc D.nbr i w hw).Fil (-1),
      (Br.PD D.loc D.nbr i w hw).ι (Br.PD D.loc D.nbr i w hw).t * x = 1 := by
    obtain ⟨x, hx, hx1⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one (D.locT (D.nd.l i))
    refine ⟨x, ?_, by rw [Br.PD, (D.loc _).PD_ι, (D.loc _).period_datum_t_eq, hx1]⟩
    exact ((D.locT _).fil _ _ _).2 (((D.locT _).fil _ _ _).1 hx)
  have hpow : ∀ g (n : ℕ), f (toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ n : (D.nd.O i)ˣ) : D.nd.O i)) =
      (algebraMap ℚ_[D.nd.l i] ↥L'.1 ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]))⁻¹ ^ n := fun g n => by
    rw [hf, Units.val_pow_eq_pow_val, map_pow, map_pow, map_units_inv, map_inv₀, hε]
  refine ⟨fun a => ?_, fun c hc a => ?_⟩
  · obtain ⟨e', he'⟩ := split_map f (fun g => mapM (toK D.nd i) (rTwO D.nd i r π) (s g))
      (fun g => mapM (toK D.nd i) (WpO D.nd i ρ π) (s g))
      (fun g c => toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ (c : ℕ) : (D.nd.O i)ˣ) : D.nd.O i)) e (fun g u => by
        have h1 : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) v,
            (mapM (toK D.nd i) (twistM M (chiU D.nd i 1)⁻¹) (s g)).mulVec v =
              toK D.nd i (((chiU D.nd i 1)⁻¹ (s g) : (D.nd.O i)ˣ) : D.nd.O i) •
                (mapM (toK D.nd i) M (s g)).mulVec v := fun M v => by
          rw [← Matrix.smul_mulVec]
          congr 1
          ext a b
          exact map_mul (toK D.nd i) _ _
        rw [rTwO, WpO, h1, h1, map_smul, he]
        refine Prod.ext rfl (funext fun c => ?_)
        simp only [← hχ, Units.val_mul, map_mul, mul_assoc]
        rfl)
    obtain ⟨J, h1, h2⟩ := jumps_of_split (Br.PD D.loc D.nbr i w hw) (GlobalTheory.SmallJumpExample.isField_bdR D _) hs
      (matRep (locE D i w hw L' hL (rTwO D.nd i r π))) (matRep (locE D i w hw L' hL (WpO D.nd i ρ π))) e'
      (fun g u => by
        rw [hM, hM, he']
        exact Prod.ext rfl (funext fun c => congrArg (· * (e' u).2 c) (hpow g c))) τ
    rw [h1.2, h2.2, Multiset.count_add, count_blockJumps]
    push_cast
    rfl
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    rw [multV_oneByOne (Br.PD D.loc D.nbr i w hw) (GlobalTheory.SmallJumpExample.isField_bdR D _) hs _ n
      (fun g u b => ?_) τ a, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [hM, ← hpow, ← hχ0 n hc2, Subsingleton.elim b 0]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.isValue]
    congr 1
    change f (toK D.nd i (chiRatO D.nd i (n + 1) (s g) 0 0)) = _
    rw [chiRatO, twistM_one_apply, MonoidHom.mul_apply, mul_comm]

end GlobalTheory.BlockEnl
end
end

section
section
noncomputable section

namespace GlobalTheory.AmbBlockDecomp

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem sum_ind_block (t : ℕ) (a : ℤ) :
    (∑ c ∈ Finset.Icc 1 t, (if a = (c : ℤ) - 1 then (1 : ℤ) else 0)) =
      if 0 ≤ a ∧ a < t then 1 else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n := ⟨a.toNat, (Int.toNat_of_nonneg h.1).symm⟩
    rw [Finset.sum_eq_single (n + 1)]
    · simp
    · intro b _ hb
      rw [if_neg]
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_Icc]
      omega
  · apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg]
    omega

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  intro D i r ρ π hD _ _ _ w hw C τ
  have hB : GlobalTheory.PtCore.BlockE D i r ρ π :=
    GlobalTheory.BlockEnl.blockE_of_isBlockSum D i r ρ π (by
      obtain ⟨e, he⟩ := hD
      exact ⟨e, fun g u => he g u⟩)
  obtain ⟨h1, h2⟩ := hB w hw C.LL C.le τ
  have hl : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)),
      TruncatedSeriesCountingIdentities.locC C M = GlobalTheory.PtCore.locE D i w hw C.LL C.le M := fun _ => rfl
  simp only [hl]
  refine ⟨fun a => ?_, fun c hc a => h2 c hc a⟩
  rw [h1 a]
  congr 1
  rw [Finset.sum_congr rfl (fun c hc => h2 c hc a)]
  exact (sum_ind_block D.R.t a).symm

end GlobalTheory.AmbBlockDecomp
end
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  atlas_forward_decl GlobalTheory.AmbBlockDecomp.main
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InvJump

open Module

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def qRep (ρ : Representation LL G V) (p : Submodule LL V) (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p) :
    Representation LL G (V ⧸ p) where
  toFun g := p.mapQ p (ρ g) (fun x hx => hp g x hx)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

end Gen

theorem h0V_eq_bot_of_multV_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), IsDR (P.PD K) ρ → multV (P.PD K) ρ τ 0 = 0 → H0V ρ = ⊥ := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ hdR hm
  haveI := K.2
  haveI := LL.2
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := Submodule.ne_bot_iff _ |>.1 hne
  have hinv : ∀ g, ρ g v = v := by
    intro g
    have := (Submodule.mem_iInf _).1 hv g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this

  let σ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) := 1
  let ι : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] V := (LinearMap.proj 0).smulRight v
  have hι : ∀ u, ι u = u 0 • v := fun u => rfl
  have hιeq : ∀ g x, ι (σ g x) = ρ g (ι x) := by
    intro g x
    rw [hι, hι, map_smul, hinv]
    rfl
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker, hι] at hu
    have h0 : u 0 = 0 := (smul_eq_zero.1 hu).resolve_right hv0
    funext c
    rw [Subsingleton.elim c 0, h0]
    rfl
  let p : Submodule ↥LL.1 V := LinearMap.range ι
  have hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨σ g u, hιeq g u⟩
  let ρ₂ := GlobalTheory.InvJump.qRep ρ p hp
  have hπeq : ∀ g x, p.mkQ (ρ g x) = ρ₂ g (p.mkQ x) := fun g x => rfl
  obtain ⟨-, -, hadd⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI T K LL (Fin 1 → ↥LL.1) σ V ρ (V ⧸ p) ρ₂
    ι p.mkQ hιeq hπeq hιinj (Submodule.mkQ_surjective p) (Submodule.ker_mkQ p).symm hdR
  have h1 : multV (P.PD K) σ τ 0 = 1 := by
    have := GlobalTheory.PtCore.multV_cycPow_line (P.PD K) (GlobalTheory.DRFil.isField_dR T)
      (GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K) σ 0 (fun g u => by simp [σ]) τ 0
    simpa using this
  have h2 := (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL (V ⧸ p) ρ₂ τ 0).2.1
  have h3 := (hadd τ 0).2.1
  omega

end GlobalTheory.InvJump
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_vanish_of_zero_multiplicity : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), IsDR (P.PD K) ρ → multV (P.PD K) ρ τ 0 = 0 → H0V ρ = ⊥ := by
  atlas_forward_decl GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero
end

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.GTwoTheta

open Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

theorem zero_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hjm ρ
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union, reflS, Set.mem_setOf_eq, AdmissibleParameterJ.refl]
    rintro (h | h)
    · have := hcl _ h; linarith
    · rcases hlow _ h with ⟨-, h2⟩ | ⟨h2, -⟩ <;> linarith
  · simpa only [JW, cloudT, lowT, ↓reduceIte] using h0

theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, Bool.false_eq_true, ↓reduceIte, Jm, Jp]
    rcases hq with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · simp only [JW, cloudT, lowT, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, ↓reduceIte, Jp, Set.mem_union]
    exact Or.inl hq

theorem neg_one_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (-1 : ℚ) ∉ JW D up j ρ :=
  fun h => ((hc j hj1 hjm ρ).2.1 up).1 (JW_sub_JJ up j ρ h)

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem dR_WT (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧
      IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  have := D.nd.lPrime i
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e :=
    (GlobalTheory.DecompForms.main D i r ρ π).1 hD
  have hsum := (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hdec).1 hc
  exact ⟨(GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.1).1,
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.2).1⟩

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem twistedRep_no_invariants_purity (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (hr : GoodR D.nd i r)
    (hπ : π ∈ D.nd.Z i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    H0V (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) = ⊥ ∧ H0V (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) = ⊥ := by
  have := D.nd.lPrime i
  have hjr := D.nd.j_range i
  obtain ⟨hdrW, hdrT⟩ := dR_WT D i r ρ π w hw C hD hc
  obtain ⟨τ₀⟩ := GlobalTheory.PtCore.nonempty_embE D i w hw C.LL C.le
  obtain ⟨g, ρ', -, -, hW⟩ := hJ i r hr w hw C τ₀
  obtain ⟨-, hW0, -, hT0⟩ := hW ρ π hπ hD 0
  constructor
  · refine GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrW ?_
    refine hW0.trans ?_
    rw [if_neg]
    push_cast
    exact zero_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _
  · refine GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrT ?_
    refine hT0.trans ?_
    rw [if_neg]
    rw [GlobalTheory.JumpSets.dualS_int]
    push_cast
    exact neg_one_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem chi_jump (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hamb : ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∀ c ∈ Finset.Icc 1 D.R.t, ∀ a,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0)
    (c : ℕ) (hc1 : 1 ≤ c) (hct : c ≤ D.R.t) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ) :
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a ↔ a = (c : ℤ) - 1 := by
  have := D.nd.lPrime i
  have hm := hamb τ c (Finset.mem_Icc.2 ⟨hc1, hct⟩) a
  refine (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ (D.locT _) _ _ _
    (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a).2.2.trans ?_
  refine (Iff.of_eq (congrArg (· ≠ 0) hm)).trans ?_
  split_ifs with h <;> simp [h]

theorem tw_jumps (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) :
    (∀ (x y : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a =
        multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r y)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a) ∧
    (∀ (x : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a ≤ 1) ∧
    (∀ x : D.nd.X i,
      ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ (-1)) := by
  have hjr := D.nd.j_range i
  obtain ⟨g, ρ', -, hx, -⟩ := hJ i r hr w hw C τ
  refine ⟨fun x y a => ?_, fun x a => ?_, fun x => ?_⟩
  · rw [← locC_rTwO, ← locC_rTwO, (hx x a).2.1, (hx y a).2.1]
  · rw [← locC_rTwO, (hx x a).2.1]
    split_ifs <;> norm_num
  · rw [← locC_rTwO, (hx x (-1)).1]
    push_cast
    exact ((hJc _ hjr.1 hjr.2 ρ').2.1 _).1

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π := by
  intro hF D L hG2 hJa hJc i r ρ π hr h0 h1 hπ hD w hw C
  obtain ⟨ep, hJ⟩ := hJa
  have hcrys := GlobalTheory.CrysFromGTwo.main hF D i r ρ π hr (hG2 i r hr) h0 h1 hD w hw C
  have hamb := GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i r ρ π hD hπ h0 h1 w hw C
  have hH := twistedRep_no_invariants_purity D L ep hJ hJc i r ρ π hr hπ w hw C hD (hcrys.2 π).2
  refine ⟨⟨fun x => (hcrys.2 x).1, fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).1,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.1,
    fun c hc1 hct τ a => chi_jump D i r ρ π w hw C (fun τ => (hamb τ).2) c hc1 hct τ a,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.2, hH.1, hH.2⟩, fun x => ?_⟩
  rw [← locC_rTwO]
  exact (hcrys.2 x).2

end GlobalTheory.GTwoTheta
end
end
