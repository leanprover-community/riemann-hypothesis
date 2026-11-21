import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPair
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLatticeSpanEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfHeisenbergFreeActionDecompositionStatement

section
section
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.DefRead

theorem bcLin_sub_smul_apply {K W : Type} [Field K] [AddCommGroup W] [Module K W] (σ : K →+* ℂ)
    (f : W →ₗ[K] W) (a : K) (v : VC σ W) :
    bcLin σ (f - a • LinearMap.id) v = bcLin σ f v - σ a • v := by
  letI : Algebra K ℂ := σ.toAlgebra
  revert v
  show ∀ v : ℂ ⊗[K] W, LinearMap.baseChange ℂ (f - a • LinearMap.id) v = LinearMap.baseChange ℂ f v - σ a • v
  intro v
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  congr 1

theorem bcLin_sum_smul {K W G : Type} [Field K] [AddCommGroup W] [Module K W] [Fintype G] (σ : K →+* ℂ)
    (f : G → W →ₗ[K] W) (a : G → K) :
    bcLin σ (∑ g, a g • f g) = ∑ g, σ (a g) • bcLin σ (f g) := by
  letI : Algebra K ℂ := σ.toAlgebra
  show LinearMap.baseChangeHom K ℂ W W (∑ g, a g • f g) = ∑ g, σ (a g) • LinearMap.baseChange ℂ (f g)
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  show LinearMap.baseChange ℂ (a g • f g) = _
  rw [LinearMap.baseChange_smul]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, ← algebraMap_smul ℂ (a g)]
  rfl

end GlobalTheory.DefRead

namespace GlobalTheory.DefRead

theorem finrank_eig_twBC : ∀ (K W G : Type) [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Group G] [Fintype G]
    (σ : K →+* ℂ) (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) (J : Subgroup G) (μ : J →* Kˣ) (c : G → K),
    Module.finrank K (⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ)) ∧
    Module.finrank K ((⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id)) ⊓
        LinearMap.ker (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) ⊓
        LinearMap.ker (Representation.asAlgebraHom (GlobalTheory.DefRead.twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g)))) :
          Submodule ℂ (GlobalTheory.DefRead.VC σ W)) := by
  intro K W G _ _ _ _ _ _ σ ρ0 χ J μ c
  letI : Algebra K ℂ := σ.toAlgebra
  set a : J → W →ₗ[K] W := fun p => ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id with ha
  have hker : ∀ p : J, LinearMap.ker (twBC σ ρ0 χ (p : G) -
      ((((Units.map σ.toMonoidHom).comp μ) p : ℂˣ) : ℂ) • LinearMap.id) = LinearMap.ker (bcLin σ (a p)) := by
    intro p
    ext v
    have hμ : ((((Units.map σ.toMonoidHom).comp μ) p : ℂˣ) : ℂ) = σ (μ p) := rfl
    have hu : σ (((χ p)⁻¹ : Kˣ) : K) * σ ((χ p * μ p : Kˣ) : K) = σ (μ p) := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel_left]
    have hu0 : σ (((χ p)⁻¹ : Kˣ) : K) ≠ 0 := (map_ne_zero σ).2 (Units.ne_zero _)
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ha, bcLin_sub_smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, twBC_apply, LinearMap.smul_apply, hμ, ← hu, ← smul_smul, ← smul_sub, smul_eq_zero,
      or_iff_right hu0]
  have heig : eig (twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) = ⨅ p : J, LinearMap.ker (bcLin σ (a p)) :=
    iInf_congr hker
  have halg : Representation.asAlgebraHom (twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g))) =
      bcLin σ (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) := by
    rw [map_sum, bcLin_sum_smul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.asAlgebraHom_single, twBC_apply, smul_smul, map_mul]
  have hbc := TensorProduct.isBaseChange K W ℂ
  have h1 := finrank_iInf_ker_baseChange K ℂ W (ℂ ⊗[K] W) J (TensorProduct.mk K ℂ W 1) hbc a
    (fun p => (bcLin σ (a p) : ℂ ⊗[K] W →ₗ[ℂ] ℂ ⊗[K] W)) (fun p v => complexificationBaseChangeLinear_one_tmul σ (a p) v)
  set b : Option J → W →ₗ[K] W := fun o => o.elim (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) a with hb
  have h2 := finrank_iInf_ker_baseChange K ℂ W (ℂ ⊗[K] W) (Option J) (TensorProduct.mk K ℂ W 1) hbc b
    (fun o => (bcLin σ (b o) : ℂ ⊗[K] W →ₗ[ℂ] ℂ ⊗[K] W)) (fun o v => complexificationBaseChangeLinear_one_tmul σ (b o) v)
  rw [iInf_option, iInf_option] at h2
  refine ⟨?_, ?_⟩
  · rw [heig]
    exact h1.1.symm
  · rw [heig, halg, inf_comm]
    conv_rhs => rw [inf_comm]
    exact h2.1.symm

end GlobalTheory.DefRead
end

open GlobalTheory.BadCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_characterEigenspace_twistedComplexification : ∀ (K W G : Type) [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Group G] [Fintype G]
    (σ : K →+* ℂ) (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) (J : Subgroup G) (μ : J →* Kˣ) (c : G → K),
    Module.finrank K (⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ)) ∧
    Module.finrank K ((⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id)) ⊓
        LinearMap.ker (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) ⊓
        LinearMap.ker (Representation.asAlgebraHom (GlobalTheory.DefRead.twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g)))) :
          Submodule ℂ (GlobalTheory.DefRead.VC σ W)) := by
  atlas_forward_decl GlobalTheory.DefRead.finrank_eig_twBC
end

section
namespace GlobalTheory.NonzeroMultipleInSpan

open NumberField

theorem exists_ne_zero_smul_mem_span {LL : Type} [Field LL] [NumberField LL] {n : ℕ}
    (T : Set (Fin n → LL)) :
    ∀ x ∈ Submodule.span LL T, ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm b a]
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ b hay) (Submodule.smul_mem _ a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 LL)) c
    refine ⟨(q : 𝓞 LL) * a, mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩
    have h : ((q : 𝓞 LL) * a) • (c • y) = p • (a • y) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      simp only at hpq
      rw [← hpq]
      ring
    rw [h]
    exact Submodule.smul_mem _ p hay

end GlobalTheory.NonzeroMultipleInSpan
end

section
section
open NumberField

namespace GlobalTheory.IntFormsRank

variable {LL : Type} [Field LL] [NumberField LL] {n : ℕ}

theorem smul_eq_algebraMap_smul (r : 𝓞 LL) (z : Fin n → LL) : r • z = (algebraMap (𝓞 LL) LL r) • z :=
  (algebraMap_smul LL r z).symm

theorem exists_den_smul_mem (T : Set (Fin n → LL)) (x : Fin n → LL) (hx : x ∈ Submodule.span LL T) :
    ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  first
  | exact @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | (apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span ..)

theorem span_inf_eq (T : Set (Fin n → LL)) (hT : Submodule.span LL T = ⊤) (S : Submodule LL (Fin n → LL)) :
    Submodule.span LL ((Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) :
      Set (Fin n → LL)) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    have hxT : x ∈ Submodule.span LL T := by rw [hT]; exact Submodule.mem_top
    obtain ⟨d, hd, hdx⟩ := exists_den_smul_mem T x hxT
    have hdL : algebraMap (𝓞 LL) LL d ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 LL) LL)]; exact hd
    have hmem : d • x ∈ (Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) := by
      refine ⟨hdx, ?_⟩
      show d • x ∈ S
      rw [smul_eq_algebraMap_smul]; exact S.smul_mem _ hx
    have hx' : x = (algebraMap (𝓞 LL) LL d)⁻¹ • (d • x) := by
      rw [smul_eq_algebraMap_smul, smul_smul, inv_mul_cancel₀ hdL, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.IntFormsRank

theorem GlobalTheory.IntFormsRank.rkK_Mall : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  intro LL Ks _ _ _ _ _ n Wσ _ _ G0 _ _ A J0 lam0 f hsp
  constructor
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    rw [GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    have e : (Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓ (A.typeP J0 lam0).restrictScalars (𝓞 LL) ⊓
        (LinearMap.ker f).restrictScalars (𝓞 LL)) =
        Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓
          (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)).restrictScalars (𝓞 LL) := by
      rw [inf_assoc]; rfl
    rw [e, GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_forms_span_invariant : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  atlas_forward_decl GlobalTheory.IntFormsRank.rkK_Mall
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.DefRead

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem typeSubspace_eq_iInf_ker {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] {n : ℕ}
    {Wσ : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) :
    A.typeP J0 lam0 = ⨅ p : J0, LinearMap.ker (A.ρ p - ((A.chi p * lam0 p : LLˣ) : LL) • LinearMap.id) := by
  ext F
  simp [Formalism.IndefR.Arith.FormsL.mem_typeP, Submodule.mem_iInf, sub_eq_zero]

set_option maxHeartbeats 1000000 in

theorem point_read (p : PtAt ex Csz) (i : Fin D.R.m) (hp : RowsT p) (hg : GramAt p i)
    (hfree : ∀ k : Fin 2, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH D k) X)
      (A : X → Submodule ℂ (VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), ∀ v ∈ A y, repAt p i (h : G0g D.nd) v ∈ A (h • y)) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
      (π : Γ →* G0g D.nd) (s : G0g D.nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ)
      (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ)
      (H : Fin 2 → Subgroup (G0g D.nd)), IsSplit π s ∧ IsWhit D Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧
      (∀ k, IsHalf D k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X)
        (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
        ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧
      Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧
      Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) := by
  classical
  obtain ⟨lam, ψ, hW, hlam, -⟩ := GlobalTheory.ShareOn.baseLevel_isWhit D L hT Gi Gl Kc Y0 cX ex Csz p hp.1
  have hfin : Finite (G0g D.nd) := Finite.of_equiv _ (p.R.eG.trans p.cG).toEquiv
  let e := p.R.eG.trans p.cG
  let Pb := p.P.P0.map e.toMonoidHom
  let lamb : Pb.comap (MonoidHom.id (G0g D.nd)) →* ℂˣ :=
    lam.comp (MulEquiv.subgroupCongr (Subgroup.comap_id Pb)).toMonoidHom

  have hEig : eig (repAt p i) (Pb.comap (MonoidHom.id (G0g D.nd))) lamb =
      eig (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi) (p.F.lv2.lvl false).P
        ((Units.map D.what₂.embLL.toMonoidHom).comp (p.F.lv2.lvl false).ψ⁻¹) := by
    ext v
    rw [mem_eig, mem_eig]
    constructor
    · intro h g
      have hm : e g ∈ Pb := ⟨g, g.2, rfl⟩
      have := h ⟨e g, hm⟩
      rw [repAt_apply] at this
      simp only [e, MulEquiv.symm_apply_apply] at this
      rw [this]
      congr 2
      exact Units.ext (hlam g hm)
    · intro h γ
      obtain ⟨g, hg, hge⟩ := γ.2
      have := h ⟨g, hg⟩
      rw [repAt_apply]
      have h1 : (p.R.eG.trans p.cG).symm (γ : G0g D.nd) = g := by
        rw [MulEquiv.symm_apply_eq]; exact hge.symm
      rw [h1, this]
      congr 2
      apply Units.ext
      have h2 := hlam ⟨g, hg⟩ ⟨g, hg, rfl⟩
      have h3 : lamb γ = lam ⟨e g, ⟨g, hg, rfl⟩⟩ := by
        show lam ⟨(γ : G0g D.nd), _⟩ = _
        congr 1
        exact Subtype.ext hge.symm
      rw [h3, h2]
      rfl
  refine ⟨G0g D.nd, inferInstance, hfin, VAt p i, inferInstance, inferInstance, inferInstance, MonoidHom.id _, MonoidHom.id _,
    repAt p i, Pb, lam, ψ, lamb, GlobalTheory.BadCount.Inh.halfH D, ⟨fun g => rfl, fun g γ hγ => ?_⟩, hW, fun γ => rfl,
    fun k => GlobalTheory.BadCount.Inh.isHalf_halfH D k, fun k => ?_, ?_, ?_⟩
  · have : γ = 1 := hγ
    subst this; simp
  · obtain ⟨X, hX, hXd, hact, A, hf, hA, hc⟩ := hfree k
    let f : (GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd)) →* GlobalTheory.BadCount.Inh.halfH D k :=
      { toFun := fun h => ⟨h.1, h.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    letI : MulAction ((GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd))) X := MulAction.compHom X f
    refine ⟨X, hX, hXd, this, A, fun h y hy => ?_, hA, fun h y v hv => hc (f h) y v hv⟩
    have := hf (f h) y hy
    exact Subtype.ext (congrArg Subtype.val this)
  · have hC := GlobalTheory.T.gram_lattice_span_eq_top p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _) = _
    rw [hB.1, typeSubspace_eq_iInf_ker, hA.1, hEig]
  · have hC := GlobalTheory.T.gram_lattice_span_eq_top p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    obtain ⟨-, -, -, hc, -, -⟩ := p.grpRecPin
    have hsum : ∀ x : MonoidAlgebra ℂ (G0g D.nd), x = ∑ h, MonoidAlgebra.single h (x.coeff h) := fun x =>
      MonoidAlgebra.ext (by
        rw [MonoidAlgebra.coeff_sum]
        simp only [MonoidAlgebra.coeff_single]
        exact (Finsupp.univ_sum_single _).symm)
    have he0 : D.ntypes.e0 = ∑ g : p.P.Gp,
        MonoidAlgebra.single (e g) (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)) := by
      rw [hsum D.ntypes.e0, ← Equiv.sum_comp e.toEquiv]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hc g]
      rfl
    have hK : Representation.asAlgebraHom ((repAt p i).comp (MonoidHom.id (G0g D.nd))) D.ntypes.e0 =
        Representation.asAlgebraHom (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi)
          (∑ g, MonoidAlgebra.single g (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g))) := by
      rw [he0, map_sum, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
      have hee : (p.R.eG.trans p.cG).symm (e g) = g := MulEquiv.symm_apply_apply _ _
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, repAt_apply, hee]
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _ ⊓ (LinearMap.ker (eGood p.R.toRealDat i)).restrictScalars _) = _
    have hEG : eGood p.R.toRealDat i = ∑ g, ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g *
        (((p.R.toRealDat.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (p.R.toRealDat.FW i).ρ g := by
      unfold eGood Formalism.IndefR.Arith.FormsL.eOp; rfl
    rw [hB.2, typeSubspace_eq_iInf_ker, hEG, hA.2]
    rw [hEig, hK]
end GlobalTheory.DefRead

namespace GlobalTheory.DefRead

set_option maxHeartbeats 1000000 in

theorem exists_rep_def : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (π : Γ →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X) (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧ ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) V) (Fm.D x ι).ntypes.e0) : Submodule ℂ V) := by
  intro hP hG
  have h1 := GlobalTheory.T.half_heisenberg_free_action_decomposition hP hG
  have h2 := hG
  unfold Gram at h2
  unfold Lifts at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  exact point_read p i hp (a2 i) (a1 i hi)

end GlobalTheory.DefRead
end
