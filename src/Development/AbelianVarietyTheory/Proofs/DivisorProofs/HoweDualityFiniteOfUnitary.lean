import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForClosure

section
noncomputable section

open GlobalTheory.WeilM
open scoped TensorProduct

namespace GlobalTheory.HoweTrivial

theorem chain_bound_of_finiteLength {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule R M), StrictMono N → m ≤ L := by
  obtain ⟨h1, h2⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1 (Module.length_ne_top (R := R) (M := M))
  refine ⟨l + 1, fun m N hN => ?_⟩
  rcases m with _ | m
  · omega
  have h3 := Order.LTSeries.length_le_krullDim (LTSeries.mk m N hN)
  rw [← Module.coe_length, ← hl] at h3
  have h4 : m ≤ l := by exact_mod_cast h3
  omega

theorem sup_ne_top {H T : Type} [Group H] [AddCommGroup T] [Module ℂ T] (Θ : Representation ℂ H T)
    (h : IsFiniteLength (MonoidAlgebra ℂ H) Θ.asModule)
    (hc : ∀ N N' : Subrepresentation Θ, IsCoatom N → IsCoatom N' → N = N')
    (A B : Subrepresentation Θ) (hA : A ≠ ⊤) (hB : B ≠ ⊤) : A ⊔ B ≠ ⊤ := by
  obtain ⟨h1, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have hw : WellFoundedGT (Subrepresentation Θ) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).strictMono.wellFoundedGT
  have hco : IsCoatomic (Subrepresentation Θ) := inferInstance
  obtain ⟨C, hC, hAC⟩ := (eq_top_or_exists_le_coatom A).resolve_left hA
  obtain ⟨C', hC', hBC⟩ := (eq_top_or_exists_le_coatom B).resolve_left hB
  obtain rfl := hc C C' hC hC'
  exact ne_top_of_le_ne_top hC.1 (sup_le hAC hBC)

theorem trivial_irreducible (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation (Representation.trivial ℂ G ℂ)) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ ℂ) this
  refine { eq_bot_or_eq_top := fun a => ?_ }
  rcases eq_bot_or_eq_top a.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem trivial_admissible (G : Type) [Group G] [TopologicalSpace G] :
    GlobalTheory.PRep.IsAdmissible (Representation.trivial ℂ G ℂ) := by
  refine ⟨fun v => ?_, fun K _ _ => inferInstance⟩
  simp

section

variable {Y G H T : Type} [Group G] [Group H] [TopologicalSpace Y] [AddCommGroup T] [Module ℂ T]

theorem mem_span_of_eq_zero (om : G × H →* Module.End ℂ (Y → ℂ)) (hom : ∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y)
    {Θ : Representation ℂ H T} {p : SB Y →ₗ[ℂ] ℂ ⊗[ℂ] T}
    (hp : GlobalTheory.Published.IsBigTheta om (Representation.trivial ℂ G ℂ) Θ p) (φ : SB Y) (hφ : p φ = 0) :
    (φ : Y → ℂ) ∈ Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} := by
  set A := Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} with hA
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  refine (hp.2.2 φ).1 hφ (f ∘ₗ A.mkQ ∘ₗ (SB Y).subtype) fun g ψ ψ₁ h => ?_
  have : A.mkQ (ψ₁ : Y → ℂ) = A.mkQ ψ := by
    rw [h]
    exact (Submodule.Quotient.eq A).2 (Submodule.subset_span ⟨g, ψ, ψ.2, rfl⟩)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, this, Representation.trivial_apply]

def image (om : G × H →* Module.End ℂ (Y → ℂ)) (hom : ∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y)
    {Θ : Representation ℂ H T} {p : SB Y →ₗ[ℂ] ℂ ⊗[ℂ] T}
    (hp : GlobalTheory.Published.IsPairHom om (Representation.trivial ℂ G ℂ) Θ p) (N : Submodule ℂ (Y → ℂ))
    (hN : ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N) : Subrepresentation Θ where
  toSubmodule := (N.comap (SB Y).subtype).map ((TensorProduct.lid ℂ T).toLinearMap ∘ₗ p)
  apply_mem_toSubmodule h := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨⟨om (1, h) φ, hom _ _ φ.2⟩, hN h _ hφ, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hp 1 h φ _ rfl]
    generalize p φ = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_image_iff (om : G × H →* Module.End ℂ (Y → ℂ)) (hom : ∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y)
    {Θ : Representation ℂ H T} {p : SB Y →ₗ[ℂ] ℂ ⊗[ℂ] T}
    (hp : GlobalTheory.Published.IsBigTheta om (Representation.trivial ℂ G ℂ) Θ p) (N : Submodule ℂ (Y → ℂ))
    (hA : Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N)
    (hN : ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N) (φ : SB Y) :
    TensorProduct.lid ℂ T (p φ) ∈ (image om hom hp.1 N hN).toSubmodule ↔ (φ : Y → ℂ) ∈ N := by
  refine ⟨?_, fun h => ⟨φ, h, rfl⟩⟩
  rintro ⟨ψ, hψ, e⟩
  have e1 : p ψ = p φ := (TensorProduct.lid ℂ T).injective e
  have e2 : p (φ - ψ) = 0 := by rw [map_sub, e1, sub_self]
  have h3 := N.add_mem (hA (mem_span_of_eq_zero om hom hp _ e2)) hψ
  simpa using h3

end

theorem chain_bounded_and_sup_proper :
    ∀ {Y G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace Y]
    (om : G × H →* Module.End ℂ (Y → ℂ)), GlobalTheory.Published.HoweDualityFor om → (∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y) →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (Y → ℂ)), StrictMono N →
      (∀ i, Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N i ∧ N i ≤ SB Y ∧
        ∀ h, ∀ φ ∈ N i, om (1, h) φ ∈ N i) → m ≤ L) ∧
    ∀ N N' : Submodule ℂ (Y → ℂ),
      (Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N ∧ N ≤ SB Y ∧ ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N) →
      (Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N' ∧ N' ≤ SB Y ∧ ∀ h, ∀ φ ∈ N', om (1, h) φ ∈ N') →
      N ≠ SB Y → N' ≠ SB Y → N ⊔ N' ≠ SB Y := by
  intro Y G H _ _ _ _ _ om hH hom
  obtain ⟨⟨T, _, _, Θ, p, hp, -, hfl, hco⟩, -⟩ :=
    hH ℂ (Representation.trivial ℂ G ℂ) (trivial_irreducible G) (trivial_admissible G)
  constructor
  · obtain ⟨L, hL⟩ := chain_bound_of_finiteLength hfl
    refine ⟨L, fun m N hN hs => hL m (fun i => Subrepresentation.subrepresentationSubmoduleOrderIso
      (image om hom hp.1 (N i) (hs i).2.2)) fun i j hij => ?_⟩
    refine (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).strictMono ?_
    have hlt := hN hij
    refine lt_of_le_of_ne ?_ fun e => hlt.not_ge fun φ hφ => ?_
    · exact Submodule.map_mono (Submodule.comap_mono hlt.le)
    · have h1 := (mem_image_iff om hom hp (N j) (hs j).1 (hs j).2.2 ⟨φ, (hs j).2.1 hφ⟩).2 hφ
      rw [← e] at h1
      exact (mem_image_iff om hom hp (N i) (hs i).1 (hs i).2.2 _).1 h1
  · have key : ∀ (N : Submodule ℂ (Y → ℂ))
        (hs : Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N ∧ N ≤ SB Y ∧
          ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N), N ≠ SB Y → image om hom hp.1 N hs.2.2 ≠ ⊤ := by
      intro N hs hne e
      refine hne (le_antisymm hs.2.1 fun φ hφ => ?_)
      refine (mem_image_iff om hom hp N hs.1 hs.2.2 ⟨φ, hφ⟩).1 ?_
      rw [e]
      exact Submodule.mem_top
    intro N N' hs hs' hne hne' e
    refine sup_ne_top Θ hfl hco _ _ (key N hs hne) (key N' hs' hne') ?_
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun t _ => ?_)
    obtain ⟨φ, hφ⟩ := hp.2.1 ((TensorProduct.lid ℂ T).symm t)
    have hm : (φ : Y → ℂ) ∈ N ⊔ N' := by rw [e]; exact φ.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hm
    have e1 : φ = (⟨a, hs.2.1 ha⟩ : SB Y) + ⟨b, hs'.2.1 hb⟩ := Subtype.ext hab.symm
    have e2 : t = TensorProduct.lid ℂ T (p ⟨a, hs.2.1 ha⟩) + TensorProduct.lid ℂ T (p ⟨b, hs'.2.1 hb⟩) := by
      rw [← map_add, ← map_add, ← e1, hφ, LinearEquiv.apply_symm_apply]
    rw [e2]
    exact Submodule.add_mem_sup ⟨_, ha, rfl⟩ ⟨_, hb, rfl⟩

end GlobalTheory.HoweTrivial

end
end

section
noncomputable section

section LocalHomAux

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThK.LocalHom

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E}
    {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W} (hw : M.IsWeil ψ χX χW om) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hx1 : x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v)) (hx2 : x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om x Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  set w := M.co.e.symm (p, q) with hw'
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw', LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h1 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 - 1) = 0 := hx1 u hu
  have h2 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2 - 1) = 0 := hx2 u hu
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 * (u • w) = u • w := by
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h1, Matrix.zero_mul, sub_eq_zero] at this
    exact this
  have e2 : (u • w) * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2)ᵀ = u • w := by
    have : (u • w) * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2)ᵀ - u • w = w * (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2 - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) x (u • w) = u • w := by
    simp only [GlobalTheory.WeilM.actAB]
    have := e1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] at this e2
    rw [this, e2]
  have h3 := hW.impl x (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem acts_exists {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E}
    {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W} (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hw : M.IsWeil ψ χX χW om)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hx1 : x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v)) (hx2 : x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁ := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  set T := om x with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres x Φ hΦ
  have hcomm := comm_off hw v x hx1 hx2
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ x Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin n × Fin d → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  refine ⟨(R 0)⁻¹ • fun t => T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin n × Fin d → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.ThK.LocalHom

end LocalHomAux

section LocalHomAux2

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ThK.LocalHom

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_mul (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)}
    (h₁ : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T₁ Φ ∈ GlobalTheory.WeilM.schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T₁ φ φ₁) (b : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T₂ φ₁ φ₂) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (T₂ * T₁) φ φ₂ := by
  intro r hr
  have hr1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ₁ r := ⟨hr.1, by rw [← a r hr]; exact h₁ _ hr.2⟩
  show T₂ (T₁ _) = _
  rw [a r hr, b r hr1]

theorem acts_lin (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hex : ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁)
    {φ ψ φ₁ ψ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) (hψ : ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁) (h₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T ψ ψ₁) (a b : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T (a • φ + b • ψ) (a • φ₁ + b • ψ₁) := by
  have hs : a • φ + b • ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
    add_mem ((GlobalTheory.WeilM.SB _).smul_mem a hφ) ((GlobalTheory.WeilM.SB _).smul_mem b hψ)
  obtain ⟨χ, -, hχ⟩ := hex _ hs
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (a • φ + b • ψ) R =
      a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R + b • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) ψ R := by
    funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (a • φ₁ + b • ψ₁) R =
      a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ₁ R + b • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) ψ₁ R := by
    funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) χ R = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (a • φ₁ + b • ψ₁) R := by
    rw [← hχ R (hR _ hs), e, map_add, map_smul, map_smul, h₁ R (hR φ hφ), h₂ R (hR ψ hψ), e']
  have hχe : χ = a • φ₁ + b • ψ₁ := by
    funext t
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
      intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
      simpa using (hR φ hφ).1 0 _ hz
    have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
    exact mul_right_cancel₀ hR0 this
  rw [← hχe]
  exact hχ

section Grp

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem mat_mul {J : Matrix (Fin n) (Fin n) E} (a b : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (a * b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat b := rfl

theorem mat_one {J : Matrix (Fin n) (Fin n) E} : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) = 1 := rfl

variable (σ) in

def uAtSub (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) where
  carrier := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v)
  one_mem' := by
    show ∀ u, evFin F v u = 0 → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) - 1) = 0
    intro u _
    rw [mat_one, sub_self, smul_zero]
  mul_mem' := by
    intro a b ha hb
    have ha' : ∀ u, evFin F v u = 0 → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a - 1) = 0 := ha
    have hb' : ∀ u, evFin F v u = 0 → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat b - 1) = 0 := hb
    show ∀ u, evFin F v u = 0 → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (a * b) - 1) = 0
    intro u hu
    have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (a * b) - 1 = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a - 1) * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat b - 1) +
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a - 1) + (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat b - 1) := by
      rw [mat_mul]; noncomm_ring
    rw [e, smul_add, smul_add, ← Matrix.smul_mul, ha' u hu, hb' u hu, Matrix.zero_mul, add_zero, add_zero]
  inv_mem' := by
    intro a ha
    have ha' : ∀ u, evFin F v u = 0 → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a - 1) = 0 := ha
    show ∀ u, evFin F v u = 0 → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a⁻¹ - 1) = 0
    intro u hu
    have hinv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a = 1 := by
      rw [← mat_mul, inv_mul_cancel, mat_one]
    have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a⁻¹ - 1 = -(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a⁻¹ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, ha' u hu, Matrix.mul_zero, neg_zero]

theorem mem_of_closure {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (g : Subgroup.closure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v))) : g.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) :=
  (Subgroup.closure_le (uAtSub σ X v)).2 (fun _ hx => hx) g.2

end Grp

theorem ext_hom {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V)
    (ρ : G →* Module.End ℂ S) : ∃ ρ' : G →* Module.End ℂ V, ∀ g (s : S), ρ' g s = ρ g s := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  set P := Submodule.linearProjOfIsCompl S C hC with hPdef
  have hP : ∀ s : S, P s = s := fun s => Submodule.linearProjOfIsCompl_apply_left hC s
  let f : G → Module.End ℂ V := fun g => S.subtype ∘ₗ (ρ g) ∘ₗ P + (LinearMap.id - S.subtype ∘ₗ P)
  have hf : ∀ g x, f g x = (ρ g (P x) : V) + (x - P x) := fun g x => rfl
  have hPf : ∀ g x, P (f g x) = ρ g (P x) := by
    intro g x; rw [hf, map_add, map_sub, hP, hP, sub_self, add_zero]
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [hf, map_one, Module.End.one_apply, Module.End.one_apply]
    abel
  · intro g h
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, hf, hf g (f h x), hPf, map_mul, Module.End.mul_apply, hf h x]
    abel
  · intro g s
    show f g s = _
    rw [hf, hP, sub_self, add_zero]

end GlobalTheory.ThK.LocalHom

end LocalHomAux2

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem GlobalTheory.ThK.LocalHom.exists_localHom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ v : Pl F,
    ∃ om' : Subgroup.closure (UAt σ X (evFin F v)) × Subgroup.closure (UAt σ W (evFin F v)) →*
        Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
      ∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
        Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hstd hw v
  classical
  let S := SB (Fin n × Fin d → Fv F v)
  let Gp := Subgroup.closure (UAt σ X (evFin F v)) × Subgroup.closure (UAt σ W (evFin F v))
  have hex : ∀ (x : Gp) (φ : S), ∃ φ₁ ∈ S, Acts (evFin F v) (om (x.1.1, x.2.1)) φ φ₁ := fun x φ =>
    GlobalTheory.ThK.LocalHom.acts_exists hstd hw v (x.1.1, x.2.1) (GlobalTheory.ThK.LocalHom.mem_of_closure x.1)
      (GlobalTheory.ThK.LocalHom.mem_of_closure x.2) φ.1 φ.2
  let T : Gp → S → S := fun x φ => ⟨(hex x φ).choose, (hex x φ).choose_spec.1⟩
  have hT : ∀ (x : Gp) (φ : S), Acts (evFin F v) (om (x.1.1, x.2.1)) (φ : (Fin n × Fin d → Fv F v) → ℂ)
      (T x φ : (Fin n × Fin d → Fv F v) → ℂ) := fun x φ => (hex x φ).choose_spec.2
  have huniq : ∀ x (φ : S) (φ₁ : (Fin n × Fin d → Fv F v) → ℂ), Acts (evFin F v) (om (x.1.1, x.2.1)) φ φ₁ →
      (T x φ : (Fin n × Fin d → Fv F v) → ℂ) = φ₁ := fun x φ φ₁ h =>
    GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ.1 _ φ₁ φ.2 fun r hr => (hT x φ r hr).symm.trans (h r hr)
  let L : Gp → Module.End ℂ S := fun x =>
    { toFun := T x
      map_add' := fun φ ψ => Subtype.ext (by
        have := GlobalTheory.ThK.LocalHom.acts_lin v (om (x.1.1, x.2.1)) (fun φ hφ => hex x ⟨φ, hφ⟩) φ.2 ψ.2
          (hT x φ) (hT x ψ) 1 1
        simp only [one_smul] at this
        exact huniq x (φ + ψ) _ this)
      map_smul' := fun c φ => Subtype.ext (by
        have := GlobalTheory.ThK.LocalHom.acts_lin v (om (x.1.1, x.2.1)) (fun φ hφ => hex x ⟨φ, hφ⟩) φ.2 φ.2
          (hT x φ) (hT x φ) c 0
        simp only [zero_smul, add_zero] at this
        exact huniq x (c • φ) _ this) }
  have hone : om (((1 : Gp).1 : UA σ X.J), ((1 : Gp).2 : UA σ W.J)) = 1 := map_one om
  have hmul : ∀ x y : Gp, om (((x * y).1 : UA σ X.J), ((x * y).2 : UA σ W.J)) =
      om ((x.1 : UA σ X.J), (x.2 : UA σ W.J)) * om ((y.1 : UA σ X.J), (y.2 : UA σ W.J)) :=
    fun x y => map_mul om ((x.1 : UA σ X.J), (x.2 : UA σ W.J)) ((y.1 : UA σ X.J), (y.2 : UA σ W.J))
  have hpres := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw).pres
  let ρ : Gp →* Module.End ℂ S :=
    { toFun := L
      map_one' := LinearMap.ext fun φ => Subtype.ext (huniq 1 φ φ (by
          intro r hr
          rw [hone]
          rfl))
      map_mul' := fun x y => LinearMap.ext fun φ => Subtype.ext (huniq (x * y) φ _ (by
          rw [hmul]
          exact GlobalTheory.ThK.LocalHom.acts_mul v (fun Φ hΦ => hpres ((y.1 : UA σ X.J), (y.2 : UA σ W.J)) Φ hΦ)
            (hT y φ) (hT x (T y φ)))) }
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.ThK.LocalHom.ext_hom S ρ
  refine ⟨ρ', fun g h φ hφ => ?_⟩
  have e : ρ' (g, h) φ = (T (g, h) (⟨φ, hφ⟩ : S) : (Fin n × Fin d → Fv F v) → ℂ) := hρ' (g, h) (⟨φ, hφ⟩ : S)
  rw [e]
  exact ⟨(T (g, h) (⟨φ, hφ⟩ : S)).2, hT (g, h) (⟨φ, hφ⟩ : S)⟩

end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

open GlobalTheory.HoweAdelic in
theorem _root_.GlobalTheory.T.howe_duality_finite_of_unitary : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityFinite := by
  intro hP hH F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe v hv
  have memX : ∀ g, g ∈ Subgroup.closure (UAt σ X (evFin F v)) ↔ g ∈ UAt σ X (evFin F v) := fun g =>
    ⟨fun hg => (mem_UAtGrp σ X _ g).1 ((Subgroup.closure_le (K := UAtGrp σ X (evFin F v))).2
      (fun x hx => (mem_UAtGrp σ X _ x).2 hx) hg), fun hg => Subgroup.subset_closure hg⟩
  have memW : ∀ h, h ∈ Subgroup.closure (UAt σ W (evFin F v)) ↔ h ∈ UAt σ W (evFin F v) := fun h =>
    ⟨fun hh => (mem_UAtGrp σ W _ h).1 ((Subgroup.closure_le (K := UAtGrp σ W (evFin F v))).2
      (fun x hx => (mem_UAtGrp σ W _ x).2 hx) hh), fun hh => Subgroup.subset_closure hh⟩
  obtain ⟨om', hact⟩ := GlobalTheory.ThK.LocalHom.exists_localHom F E σ n d X W M ψ χX χW om hψ hwe v
  have hHD := GlobalTheory.HoweLocal.howeDualityFor_closure hP hH F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW
    hwe v hv om' hact
  have hpres : ∀ x, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' x φ ∈ SB _ := fun x φ hφ => (hact x.1 x.2 φ hφ).1
  obtain ⟨⟨L, hL⟩, hsum⟩ := GlobalTheory.HoweTrivial.chain_bounded_and_sup_proper om' hHD hpres
  have uniq : ∀ (T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ) (φ φ₁ φ₂ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB _ → Acts (evFin F v) T φ φ₁ → Acts (evFin F v) T φ φ₂ → φ₁ = φ₂ := fun T φ φ₁ φ₂ hφ h1 h2 =>
    GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ φ₂ hφ fun r hr => (h1 r hr).symm.trans (h2 r hr)
  have haug : augAt om v = locAug om' := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
      have h2 := (hact ⟨g, (memX g).2 hg⟩ 1 φ hφ).2
      rw [show ((1 : Subgroup.closure (UAt σ W (evFin F v))) : UA σ W.J) = 1 from rfl] at h2
      rw [uniq _ φ φ₁ _ hφ hA h2]
      exact Submodule.subset_span ⟨⟨g, (memX g).2 hg⟩, φ, hφ, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro z ⟨g, φ, hφ, rfl⟩
      have h2 := hact g 1 φ hφ
      exact Submodule.subset_span ⟨g.1, (memX _).1 g.2, φ, hφ, _, h2.1, h2.2, rfl⟩
  have hsub : ∀ N, ThetaSub om v N ↔ IsLocSub om' N := by
    intro N
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨haug ▸ h1, h2, fun h φ hφ => ?_⟩, fun ⟨h1, h2, h3⟩ => ⟨haug ▸ h1, h2, ?_⟩⟩
    · have h4 := hact 1 h φ (h2 hφ)
      exact h3 h.1 ((memW _).1 h.2) φ hφ _ h4.1 h4.2
    · intro h hh φ hφ φ₁ hφ₁ hA
      have h4 := hact 1 ⟨h, (memW h).2 hh⟩ φ (h2 hφ)
      rw [uniq _ φ φ₁ _ (h2 hφ) hA h4.2]
      exact h3 ⟨h, (memW h).2 hh⟩ φ hφ
  refine ⟨⟨L, fun m N hN hT => hL m N hN fun i => (hsub _).1 (hT i)⟩, fun N N' h h' hN hN' => ?_⟩
  exact hsum N N' ((hsub N).1 h) ((hsub N').1 h') hN hN'
end
