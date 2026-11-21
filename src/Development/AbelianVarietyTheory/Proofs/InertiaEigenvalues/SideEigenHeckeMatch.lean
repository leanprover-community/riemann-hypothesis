import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMonoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSetStatement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LocalisationCoefficientExtensionIsWildInertiaCyc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
import BuildAid.ForwardExisting

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LiveDescent

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

theorem isLocalHom_of_nonunit {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
    [IsLocalRing B] (f : A →+* B) {a : A} (ha : a ≠ 0) (hf : f a ∈ IsLocalRing.maximalIdeal B) : IsLocalHom f := by
  have hne : (IsLocalRing.maximalIdeal B).comap f ≠ ⊥ := fun h => ha (by
    have : a ∈ (IsLocalRing.maximalIdeal B).comap f := hf
    rwa [h, Ideal.mem_bot] at this)
  have hm : ((IsLocalRing.maximalIdeal B).comap f).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have he := IsLocalRing.eq_maximalIdeal hm
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have : x ∈ (IsLocalRing.maximalIdeal B).comap f := by rw [he]; exact h
  exact this hx

theorem continuous_of_isLocalHom {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A →+* B)
    [IsLocalHom f] : Continuous f := by
  have hm : Ideal.map f (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit f x hx
  refine continuous_of_continuousAt_zero f.toAddMonoidHom ?_
  intro s hs
  rw [map_zero] at hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
  refine Filter.mem_map.2 (Filter.mem_of_superset (((isAdic_iff.1 hA).1 n).mem_nhds (Ideal.zero_mem _))
    fun x hx => hn ?_)
  have h1 : f x ∈ Ideal.map f (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

theorem span_eq_top_of_map {ι k K : Type} [Field k] [Field K] (f : k →+* K) {r : ℕ}
    (M : ι → Matrix (Fin r) (Fin r) k) (h : Submodule.span K (Set.range fun g => (M g).map f) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hexp : ∀ Y : Matrix (Fin r) (Fin r) k, l Y = ∑ p, ∑ q, Y p q * l (Matrix.single p q 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have key : ∀ Y : Matrix (Fin r) (Fin r) K, ∑ p, ∑ q, Y p q * f (l (Matrix.single p q 1)) = 0 := by
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range fun g => (M g).map f) := h ▸ Submodule.mem_top
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨g, rfl⟩ := hY
      have h0 : l (M g) = 0 := hl (Submodule.subset_span ⟨g, rfl⟩)
      have := congrArg f ((hexp (M g)).symm.trans h0)
      simpa [map_sum] using this
    | zero => simp
    | add Y Z _ _ hY hZ => simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, hY, hZ, add_zero]
    | smul a Y _ hY => simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hY, mul_zero]
  apply hl0
  refine LinearMap.ext fun Y => ?_
  rw [hexp, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  have h1 := key (Matrix.single p q 1)
  rw [Finset.sum_eq_single p (fun a _ ha => by simp [Matrix.single_apply_of_row_ne (Ne.symm ha)]) (by simp),
    Finset.sum_eq_single q (fun a _ ha => by simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm ha)]) (by simp)] at h1
  simp only [Matrix.single_apply_same, one_mul, map_eq_zero] at h1
  rw [h1, mul_zero]

theorem trace_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (h : ∃ e, IsDecomp (t := t) σ ρ χ e)
    (g : Γ) : (mat σ g).trace = (mat ρ g).trace + ∑ c : Fin t, ((χ ((c : ℕ) + 1) g : Aˣ) : A) := by
  obtain ⟨e, he⟩ := h
  apply IsFractionRing.injective A (FractionRing A)
  let d : Fin t → FractionRing A := fun c => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A)
  have h1 : Matrix.toLin' ((mat σ g).map (toFr A)) =
      e.symm.conj ((Matrix.toLin' ((mat ρ g).map (toFr A))).prodMap (Matrix.toLin' (Matrix.diagonal d))) := by
    apply LinearMap.ext
    intro u
    apply e.injective
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm,
      LinearMap.prodMap_apply]
    refine (he g u).trans ?_
    ext c
    · rfl
    · simp [Matrix.mulVec_diagonal, d]
  have h2 := congrArg (LinearMap.trace _ _) h1
  rw [LinearMap.trace_conj', LinearMap.trace_prodMap', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq,
    Matrix.trace_toLin'_eq, Matrix.trace_diagonal] at h2
  rw [map_add, map_sum, AddMonoidHom.map_trace, AddMonoidHom.map_trace]
  exact h2

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem charZero_O (N : NData R H what₂) (A : NAut N) (i : N.Loc) : CharZero (N.O i) :=
  (iotaO N A i).charZero

theorem l_mem_maximalIdeal (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    ((N.l i : ℕ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i) := by
  have hinj : Function.Injective (algebraMap ℤ_[N.l i] (N.O i)) := by
    intro x y h
    have hx := A.iotaQ_alg i x
    rw [h, A.iotaQ_alg i y] at hx
    exact (Subtype.ext ((algebraMap ℚ_[N.l i] (Qbar (N.l i))).injective hx)).symm
  have : FaithfulSMul ℤ_[N.l i] (N.O i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := PadicInt.p_nonunit
  have := map_nonunit (algebraMap ℤ_[N.l i] (N.O i)) _ h
  rwa [map_natCast] at this

variable {N₀ N₁ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁} {i₀ : N₀.Loc} {i₁ : N₁.Loc}

theorem isLocalHom_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : IsLocalHom a.φ := by
  have := charZero_O N₀ A₀ i₀
  have hl : (N₁.l i₁).Prime := Fact.out
  refine isLocalHom_of_nonunit a.φ (a := ((N₁.l i₁ : ℕ) : N₀.O i₀)) (Nat.cast_ne_zero.2 hl.ne_zero) ?_
  rw [map_natCast]
  exact l_mem_maximalIdeal N₁ A₁ i₁

theorem continuous_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : Continuous a.φ :=
  haveI := isLocalHom_φ a
  continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ

theorem trace_eq (hC : GlobalTheory.TwSys.Cheb) (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (x : N₁.X i₁)
    (r₀ : GE N₀ →* GL (Fin R.nV) (N₀.O i₀)) (r₁ : GE N₁ →* GL (Fin R.nV) (N₁.O i₁))
    (h₀ : IsHeckeGalois N₀ i₀ (a.e x) r₀) (h₁ : IsHeckeGalois N₁ i₁ x r₁) (g : GE N₁) :
    a.φ (mat r₀ (a.γ g)).trace = (mat r₁ g).trace := by
  haveI := (N₁.O_complete i₁).toIsHausdorff
  haveI : T2Space (N₁.O i₁) := (N₁.O_adic i₁).isHausdorff_iff.1 inferInstance
  refine congrFun (GlobalTheory.BlockComplement.AE.eq_of_continuous (N := N₁) hC
    (f := fun g => a.φ (mat r₀ (a.γ g)).trace) (f' := fun g => (mat r₁ g).trace)
    ((continuous_φ a).comp (h₀.1.matrix_trace.comp a.γ_cont)) h₁.1.matrix_trace ?_) g
  filter_upwards [GlobalTheory.BlockComplement.eventually_out i₁] with w h hw B σ hB hσ
  obtain ⟨B₀, hB₀, hσ₀⟩ := (a.frob w σ).1 ⟨B, hB, hσ⟩
  have e₀ := h₀.2.2 w ((a.out w).1 (h hw)) B₀ _ hB₀ hσ₀
  have e₁ := h₁.2.2 w (h hw) B σ hB hσ
  rw [GlobalTheory.CoefDuty.Model.heckePol_map a x w (h hw), ← e₀, ← Matrix.charpoly_map] at e₁
  rw [AddMonoidHom.map_trace, Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, e₁]

end Record

theorem live_of_locExt : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → (∃ r, GoodR N₀ i₀ r) → ZDecomp N₀ i₀ → Live N₁ i₁ → Live N₀ i₀ := by
  rintro hC R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a ⟨r₀, hr₀⟩ hZ ⟨π, hπ, r, ρ, hr, hd, habs⟩
  have hπ₀ := (a.Z π).1 hπ
  obtain ⟨ρ₀, hd₀⟩ := hZ _ hπ₀ _ (hr₀ _)
  refine ⟨_, hπ₀, _, ρ₀, hr₀ _, hd₀, ?_⟩
  have htr : ∀ g, a.φ (mat ρ₀ (a.γ g)).trace = (mat ρ g).trace := by
    intro g
    have h := trace_eq hC a π _ r (hr₀ _) hr g
    rw [trace_of_isDecomp _ _ _ hd₀, trace_of_isDecomp _ _ _ hd, map_add, map_sum,
      Finset.sum_congr rfl fun (c : Fin R.t) _ => a.chi ((c : ℕ) + 1) (by omega) c.2 g] at h
    exact add_right_cancel h
  haveI := isLocalHom_φ a
  have hpos := pos_of_absIrrSub _ habs
  haveI : Nonempty (Fin R.r) := ⟨⟨0, hpos⟩⟩
  refine absIrrSub_of_span_eq_top hpos _ (span_eq_top_of_map (IsLocalRing.ResidueField.map a.φ) _ ?_)
  have h := span_eq_top_of_trace_eq
    ((mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀)).comp a.γ.toMonoidHom)
    (mapRep (IsLocalRing.residue (N₁.O i₁)) ρ) (fun g => ?_) (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
  · rw [eq_top_iff, ← h]
    refine Submodule.span_mono ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨a.γ g, (mat_mapRep _ _ _).symm⟩
  · change (mat (mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀))
      (a.γ g)).trace = _
    rw [mat_mapRep, mat_mapRep, mat_mapRep, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace,
      ← AddMonoidHom.map_trace, ← htr, IsLocalRing.ResidueField.map_residue]

end GlobalTheory.LiveDescent

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleResidualPoint_descends_coefficientExtension : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → (∃ r, GoodR N₀ i₀ r) → ZDecomp N₀ i₀ → Live N₁ i₁ → Live N₀ i₀ := by
  atlas_forward_decl GlobalTheory.LiveDescent.live_of_locExt
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.Take

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

section Plain

variable {Γ₀ Γ₁ : Type} [Group Γ₀] [Group Γ₁] {X₀ X₁ : Type} {A : Type} [CommRing A] {n r t : ℕ}

def pull (A : Type) [CommRing A] (e : X₁ ≃ X₀) : (X₀ → A) ≃ₐ[A] (X₁ → A) where
  toFun f := fun x => f (e x)
  invFun f := fun x => f (e.symm x)
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def pullT (e : X₁ ≃ X₀) (T : Subalgebra A (X₀ → A)) : Subalgebra A (X₁ → A) :=
  T.map (pull A e : (X₀ → A) →ₐ[A] (X₁ → A))

theorem pull_mem (e : X₁ ≃ X₀) {T : Subalgebra A (X₀ → A)} {f : X₀ → A} (hf : f ∈ T) :
    (fun x => f (e x)) ∈ pullT e T := ⟨f, hf, rfl⟩

def pullR (e : X₁ ≃ X₀) (γ : Γ₁ ≃* Γ₀) (rep : X₀ → (Γ₀ →* GL (Fin n) A)) : X₁ → (Γ₁ →* GL (Fin n) A) :=
  fun x => (rep (e x)).comp γ.toMonoidHom

variable (e : X₁ ≃ X₀) (γ : Γ₁ ≃* Γ₀)

theorem inRing_pull {T : Subalgebra A (X₀ → A)} {rep : X₀ → (Γ₀ →* GL (Fin n) A)}
    {a : X₀ → Matrix (Fin n) (Fin n) A} (h : InRing T rep a) :
    InRing (pullT e T) (pullR e γ rep) (fun x => a (e x)) := by
  obtain ⟨m, f, g, hf, rfl⟩ := h
  refine ⟨m, fun k x => f k (e x), fun k => γ.symm (g k), fun k => pull_mem e (hf k), ?_⟩
  funext x
  simp [pullR, mat, Finset.sum_apply]

theorem inCongruenceModule_pull_equivPoints {T : Subalgebra A (X₀ → A)} {rep : X₀ → (Γ₀ →* GL (Fin n) A)} {π : X₁}
    {a s : X₀ → Matrix (Fin n) (Fin n) A} (h : InMatrixCongruenceModule T rep (e π) a s) :
    InMatrixCongruenceModule (pullT e T) (pullR e γ rep) π (fun x => a (e x)) (fun x => s (e x)) := by
  obtain ⟨m, j, b, hj, rfl⟩ := h
  refine ⟨m, fun k x => j k (e x), fun k x => b k (e x),
    fun k => ⟨pull_mem e (hj k).1, (hj k).2.1, inRing_pull e γ (hj k).2.2⟩, ?_⟩
  funext x
  simp [Finset.sum_apply]

theorem mapRep_comp {B : Type} [CommRing B] (f : A →+* B) (ρ : Γ₀ →* GL (Fin n) A) (γ : Γ₁ →* Γ₀) :
    mapRep f (ρ.comp γ) = (mapRep f ρ).comp γ := rfl

theorem overK_comp (ρ : Γ₀ →* GL (Fin n) A) (γ : Γ₁ →* Γ₀) :
    overK (ρ.comp γ) = (overK ρ).comp γ := rfl

section Rep
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem isSS_comp {ρ : Representation K Γ₀ V} (h : IsSS ρ) : IsSS (ρ.comp γ.toMonoidHom : Representation K Γ₁ V) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W fun g v hv => by simpa using hW (γ.symm g) v hv
  exact ⟨W', fun g v hv => h1 (γ g) v hv, h2⟩

theorem absIrrDistinct_comp {ρ : Representation K Γ₀ V} (h : AbsIrrDistinct ρ) :
    AbsIrrDistinct (ρ.comp γ.toMonoidHom : Representation K Γ₁ V) := by
  obtain ⟨ι, i1, i2, Vs, hs, h1, h2, h3, h4⟩ := h
  refine ⟨ι, i1, i2, Vs, fun j g => hs j (γ g), h1, h2, fun j => ?_, fun j j' hj f hf => h4 j j' hj f fun g v => ?_⟩
  · rw [← h3 j]
    congr 1
    exact γ.surjective.range_comp fun g => (ρ g).restrict (hs j g)
  · obtain ⟨g, rfl⟩ := γ.surjective g
    exact hf g v

theorem isInv_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} {W : Submodule K (Fin a → K)} :
    IsInv (ρ.comp γ.toMonoidHom) W ↔ IsInv ρ W :=
  ⟨fun h g => by obtain ⟨g, rfl⟩ := γ.surjective g; exact h g, fun h g => h (γ g)⟩

theorem isSSRep_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} (h : IsSSRep ρ) : IsSSRep (ρ.comp γ.toMonoidHom) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_comp γ).1 hW)
  exact ⟨W', (isInv_comp γ).2 h1, h2⟩

theorem isIrrSub_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} {W : Submodule K (Fin a → K)} (h : IsIrrSub ρ W) :
    IsIrrSub (ρ.comp γ.toMonoidHom) W :=
  ⟨h.1, (isInv_comp γ).2 h.2.1, fun W' h1 h2 => h.2.2 W' h1 ((isInv_comp γ).1 h2)⟩

theorem absIrrSub_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} {W : Submodule K (Fin a → K)} (h : AbsIrrSub ρ W) :
    AbsIrrSub (ρ.comp γ.toMonoidHom) W := by
  unfold AbsIrrSub at h ⊢
  rw [mapRep_comp]
  exact isIrrSub_comp γ h

end Rep

variable [IsDomain A] [IsLocalRing A]

theorem setting_pull {T : Subalgebra A (X₀ → A)} {Z₀ : Finset X₀} {Z₁ : Finset X₁} (hZ : ∀ x ∈ Z₁, e x ∈ Z₀)
    {rep : X₀ → (Γ₀ →* GL (Fin n) A)} {ρ : X₀ → (Γ₀ →* GL (Fin r) A)} {χ : ℕ → (Γ₀ →* Aˣ)}
    (h : HidaSetting t T Z₀ rep ρ χ) :
    HidaSetting t (pullT e T) Z₁ (pullR e γ rep) (pullR e γ ρ) (fun c => (χ c).comp γ.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨((pull A e).subalgebraMap T).toRingEquiv.isLocalRing, fun x y hxy => ?_, fun x => ?_,
    fun g d => pull_mem e (h4 (γ g) d), fun x => ?_, fun x y g => h6 (e x) (e y) (γ g),
    fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨f, hf, hne⟩ := h2 (e x) (e y) (e.injective.ne hxy)
    exact ⟨_, pull_mem e hf, hne⟩
  · rw [pullR, overK_comp]
    exact isSS_comp γ (h3 (e x))
  · rw [pullR, overK_comp]
    exact absIrrDistinct_comp γ (h5 (e x))
  · obtain ⟨d, hd⟩ := h7 _ (hZ x hx)
    exact ⟨d, fun g => hd (γ g)⟩
  · rw [pullR, mapRep_comp]
    exact absIrrSub_comp γ (h8 _ (hZ x hx))

omit [IsLocalRing A] in
theorem isChoice_pull {T : Subalgebra A (X₀ → A)}
    {rep : X₀ → (Γ₀ →* GL (Fin n) A)} {ρ : X₀ → (Γ₀ →* GL (Fin r) A)} {χ : ℕ → (Γ₀ →* Aˣ)} {π : X₁} {g : Γ₁} {L : ℕ}
    {eB e1 X0 : X₀ → Matrix (Fin n) (Fin n) A} (h : IsChoice t T rep ρ χ (e π) (γ g) L eB e1 X0) :
    IsChoice t (pullT e T) (pullR e γ rep) (pullR e γ ρ) (fun c => (χ c).comp γ.toMonoidHom) π g L
      (fun x => eB (e x)) (fun x => e1 (e x)) (fun x => X0 (e x)) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨d, hd, hd'⟩, ⟨ϖ, s, hϖ, hs, hX⟩, h9⟩ := h
  refine ⟨⟨inRing_pull e γ h1, inRing_pull e γ h2, funext fun x => congrFun h3 (e x), funext fun x => congrFun h4 (e x),
    funext fun x => congrFun h5 (e x), funext fun x => congrFun h6 (e x)⟩, ⟨d, fun g => hd (γ g), hd'⟩,
    ⟨ϖ, fun x => s (e x), hϖ, inCongruenceModule_pull_equivPoints e γ hs, funext fun x => congrFun hX (e x)⟩, fun x => h9 (e x)⟩

end Plain

theorem exists_algebra {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [Algebra ℤ_[q] B] [Algebra A B]
    (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → algebraMap A B (algebraMap _ _ z) = algebraMap _ _ z') :
    ∃ (_ : Algebra ℤ_[q] A), Module.Finite ℤ_[q] A ∧ IsScalarTower ℤ_[q] A B := by
  subst h
  exact ⟨inferInstance, inferInstance, IsScalarTower.of_algebraMap_eq fun z => (hφ z z HEq.rfl).symm⟩

theorem continuous_of_isLocalHom {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] [IsLocalRing R] [IsLocalRing S]
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) (hS : IsAdic (IsLocalRing.maximalIdeal S))
    (f : R →+* S) [IsLocalHom f] : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, hR.hasBasis_nhds_zero.tendsto_iff hS.hasBasis_nhds_zero]
  intro n _
  refine ⟨n, trivial, fun x hx => ?_⟩
  have h1 : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S :=
    Ideal.map_le_iff_le_comap.2 (fun y hy => map_nonunit f y hy)
  have h2 := Ideal.mem_map_of_mem f hx
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

theorem adjoin_eq_span {A B X : Type} [CommRing A] [CommRing B] (φ : A →+* B) (s : Set (X → A)) :
    Subalgebra.toSubmodule (Algebra.adjoin B ((fun f : X → A => fun x => φ (f x)) '' s)) =
      Submodule.span B ((fun f : X → A => fun x => φ (f x)) '' (Algebra.adjoin A s : Set (X → A))) := by
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    refine Submodule.span_mono fun f hf => ?_
    induction hf using Submonoid.closure_induction with
    | mem f hf => exact Set.image_mono Algebra.subset_adjoin hf
    | one => exact ⟨1, one_mem _, by ext; simp⟩
    | mul f g _ _ hf hg =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, rfl⟩ := hg
      exact ⟨f * g, mul_mem hf hg, by ext; simp⟩
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    change _ ∈ Algebra.adjoin B _
    induction hf using Algebra.adjoin_induction with
    | mem f hf => exact Algebra.subset_adjoin ⟨f, hf, rfl⟩
    | algebraMap c => exact Subalgebra.algebraMap_mem _ (φ c)
    | add f g _ _ hf hg => convert add_mem hf hg using 1; ext; simp
    | mul f g _ _ hf hg => convert mul_mem hf hg using 1; ext; simp

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N₀ N₁ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁}
  {i₀ : N₀.Loc} {i₁ : N₁.Loc} (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁)

theorem continuous_φ : Continuous a.φ := by
  letI := a.φ.toAlgebra
  obtain ⟨_, _, _⟩ := exists_algebra a.l_eq (N₀.O i₀) (N₁.O i₁) a.φ_alg
  haveI : Algebra.IsIntegral (N₀.O i₀) (N₁.O i₁) := Algebra.IsIntegral.tower_top ℤ_[N₁.l i₁]
  haveI : FaithfulSMul (N₀.O i₀) (N₁.O i₁) := (faithfulSMul_iff_algebraMap_injective _ _).2 (Model.φ_injective a)
  haveI : IsLocalHom a.φ := Algebra.IsIntegral.isLocalHom (N₀.O i₀) (N₁.O i₁)
  exact continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ

theorem goodR_ext {rep : N₀.X i₀ → (GE N₀ →* GL (Fin R.nV) (N₀.O i₀))} (h : GoodR N₀ i₀ rep) :
    GoodR N₁ i₁ fun x => mapRep a.φ (pullR a.e a.γ rep x) := by
  intro x
  obtain ⟨h1, h2, h3⟩ := h (a.e x)
  refine ⟨(h1.comp a.γ_cont).matrix_map (continuous_φ a), ?_, fun w hw B σ hB hσ => ?_⟩
  · let ψ : Kf N₀ i₀ →+* Kf N₁ i₁ := IsFractionRing.map (Model.φ_injective a)
    have hψ : ∀ z, ψ (algebraMap _ _ z) = algebraMap _ _ (a.φ z) := fun z => by simp [ψ, IsFractionRing.map]
    letI := ψ.toAlgebra
    haveI : CharZero (Kf N₀ i₀) := ((A₀.iotaQC i₀).toRingHom.comp (A₀.iotaQ i₀)).charZero
    have h4 : IsSSRep (mapRep ψ _) := ssAscent (Kf N₀ i₀) (Kf N₁ i₁) _ _ _ (isSSRep_comp a.γ h2)
    convert h4 using 1
    ext g b c
    exact (hψ _).symm
  · obtain ⟨B', hB', hσ'⟩ := (a.frob w σ).1 ⟨B, hB, hσ⟩
    rw [Model.heckePol_map a x w hw, ← h3 w ((a.out w).1 hw) B' _ hB' hσ', ← Matrix.charpoly_map]
    rfl

theorem T_ext : Subalgebra.toSubmodule (N₁.T i₁) = Submodule.span (N₁.O i₁)
    ((fun f : N₁.X i₁ → N₀.O i₀ => fun x => a.φ (f x)) '' (pullT a.e (N₀.T i₀) : Set _)) := by
  rw [← N₁.T_gen i₁, ← N₀.T_gen i₀, pullT, AlgHom.map_adjoin, ← adjoin_eq_span]
  congr 2
  ext f
  constructor
  · rintro ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩
    obtain ⟨k1, k2, k3, k4⟩ := (a.out v).1 ⟨h1, h2, h3, h4⟩
    exact ⟨_, ⟨_, ⟨v, k, k1, k2, k3, k4, h5, h6, rfl⟩, rfl⟩, funext fun x => (a.hT v k x ⟨h1, h2, h3, h4⟩ h5 h6).symm⟩
  · rintro ⟨_, ⟨_, ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨k1, k2, k3, k4⟩ := (a.out v).2 ⟨h1, h2, h3, h4⟩
    exact ⟨v, k, k1, k2, k3, k4, h5, h6, funext fun x => (a.hT v k x ⟨k1, k2, k3, k4⟩ h5 h6).symm⟩

end Record

theorem takenWild_of_locExt : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → ∀ S : Set ℂ, Chosen N₀ A₀ i₀ S → Contains N₁ A₁ i₁ S → ∃ r ρ, GoodR N₁ i₁ r ∧ TakenWild N₁ i₁ r ρ := by
  intro R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a S hC hS
  obtain ⟨rep, ρ, hG, hSet, hch⟩ := hC
  letI := a.φ.toAlgebra
  obtain ⟨j1, j2, j3⟩ := exists_algebra a.l_eq (N₀.O i₀) (N₁.O i₁) a.φ_alg
  refine ⟨_, fun x => mapRep a.φ (pullR a.e a.γ ρ x), goodR_ext a hG, N₀.O i₀, inferInstance, inferInstance,
    inferInstance, j1, j2, inferInstance, j3, pullT a.e (N₀.T i₀), pullR a.e a.γ rep, pullR a.e a.γ ρ,
    fun c => (N₀.chi i₀ c).comp a.γ.toMonoidHom,
    ⟨Model.φ_injective a, T_ext a, fun _ => rfl, fun _ _ => rfl, a.chi⟩,
    setting_pull a.e a.γ (fun x => (a.Z x).1) hSet, fun π hπ => ?_⟩
  obtain ⟨g0, L, eB, e1, X0, hg, hc, hr⟩ := hch _ ((a.Z π).1 hπ)
  obtain ⟨g, rfl⟩ := a.γ.surjective g0
  refine ⟨g, L, _, _, _, (Model.localisationCoefficientExtension_isWildInertiaCyclotomic_iff a g).2 hg, isChoice_pull a.e a.γ hc, fun x => ?_⟩
  obtain ⟨α, hα, hP⟩ := hr (a.e x)
  choose β hβ using fun c => hS (α c) (hα c)
  refine ⟨β, ?_⟩
  apply Polynomial.map_injective ((A₁.iotaQC i₁).toRingHom.comp (A₁.iotaQ i₁)) (RingHom.injective _)
  rw [Polynomial.map_map, Polynomial.map_prod]
  refine Eq.trans ?_ (hP.trans ?_)
  · congr 1
    exact RingHom.ext a.φ_iota
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp [← hβ c]

end GlobalTheory.CoefDuty.Take

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefRingTaken_of_localisationCoefficientExtension : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → ∀ S : Set ℂ, Chosen N₀ A₀ i₀ S → Contains N₁ A₁ i₁ S → ∃ r ρ, GoodR N₁ i₁ r ∧ TakenWild N₁ i₁ r ρ := by
  atlas_forward_decl GlobalTheory.CoefDuty.Take.takenWild_of_locExt
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.TakenLarge

set_option maxHeartbeats 4000000 in

theorem evO_takenAll : GlobalTheory.TwSys.Cheb → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → BuiltEx A M C tp.tup → EvO A M C tp.tup (fun D' => SumRepresentations.Conclusion41 D' ∧ GlobalTheory.SplitCoef.OSplit D' ∧ ∀ i, ZDecomp D'.nd i) → EvO A M C tp.tup TakenAll := by
  intro hCh hHS D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hE hsplit hCS2 hB hQ
  classical
  obtain ⟨bigA, hA⟩ := hQ
  obtain ⟨L₀, hL₀⟩ := hB bigA
  have hQ₀ := hA L₀ hL₀
  obtain ⟨big₁, h₁⟩ :=
    GlobalTheory.T.side_eigen_integrality hHS D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hE hsplit hCS2 bigA L₀ hL₀
  have hc₀ := GlobalTheory.T.contains_after_localization D cf jE A M C tp.tup bigA L₀ hL₀
  let S0 : L₀.X.nd.Loc → Finset ℂ := fun i =>
    if h : ∃ S : Finset ℂ, Chosen (withLoc L₀).nd (withLoc L₀).naut i ↑S then h.choose else ∅
  let big : D.what₂.places.Pl → Finset ℂ := fun w =>
    big₁ w ∪ (Finset.range (D.R.m + 1)).biUnion (fun j => (L₀.X.nd.locs j w).biUnion S0)
  refine ⟨big, fun L₁ hL₁ => ?_⟩
  have hL₁' : Built A M C tp.tup big₁ L₁ :=
    (GlobalTheory.T.eventually_conjunction_mono D cf jE A M C tp.tup (fun _ => True) (fun _ => True)).2.2.2 big₁ big L₁
      (fun w => Finset.subset_union_left) hL₁
  have hc₁ := GlobalTheory.T.contains_after_localization D cf jE A M C tp.tup big L₁ hL₁
  intro i₁ hlive₁
  obtain ⟨i₀, hw, ⟨e⟩⟩ := h₁ L₁ hL₁' i₁
  have hc₀i := hc₀ i₀
  have hc₁i := hc₁ i₁
  have hgood₀ : ∃ r, GoodR L₀.lay.fixZ.nd i₀ r := hc₀i.2.2.2.2.2.1.1 (hQ₀.1 i₀).1.2
  have hZ₀ : ZDecomp L₀.lay.fixZ.nd i₀ := hc₀i.2.2.2.1.1 (hQ₀.2.2 i₀)
  have hlive₀ : Live L₀.lay.fixZ.nd i₀ :=
    GlobalTheory.T.irreducibleResidualPoint_descends_coefficientExtension hCh _ _ _ _ i₀ i₁ e hgood₀ hZ₀ (hc₁i.2.2.1.1 hlive₁)
  have hex : ∃ S : Finset ℂ, Chosen (withLoc L₀).nd (withLoc L₀).naut i₀ ↑S :=
    GlobalTheory.T.exists_finite_chosen_set hCh (withLoc L₀) hQ₀.1 hQ₀.2.1 i₀ (hQ₀.2.2 i₀) (hc₀i.2.2.1.2 hlive₀)
  have hch : Chosen (withLoc L₀).nd (withLoc L₀).naut i₀ ↑(S0 i₀) := by
    simp only [S0, dif_pos hex]
    exact hex.choose_spec
  have hch' := (hc₀i.2.2.2.2.1 _).1 hch
  have hsub : S0 i₀ ⊆ big (L₁.X.nd.w i₁) := by
    intro z hz
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨L₀.X.nd.j i₀, ?_, Finset.mem_biUnion.2 ⟨i₀, ?_, hz⟩⟩)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (L₀.X.nd.j_range i₀).2)
    · exact (L₀.X.nd.locs_mem _ _ _).2 ⟨rfl, hw⟩
  have hcont : Contains L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ↑(S0 i₀) := fun z hz => hc₁i.2.1 z (hsub hz)
  exact (hc₁i.2.2.2.2.2.2).2 (GlobalTheory.T.exists_coefRingTaken_of_localisationCoefficientExtension _ _ _ _ i₀ i₁ e _ hch' hcont)

end GlobalTheory.CoefDuty.TakenLarge

end
end
