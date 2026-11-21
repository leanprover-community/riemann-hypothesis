import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankinSelbergTestFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.BlockTriangularLevi
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import Development.DiscreteGroups.GlobalIrreducibility.LConv
import Development.DiscreteGroups.GlobalIrreducibility.LConvComm
import Development.DiscreteGroups.GlobalIrreducibility.LConvUnif
import Development.DiscreteGroups.GlobalIrreducibility.LConvSep
import Development.DiscreteGroups.GlobalIrreducibility.LConvGen
import Development.DiscreteGroups.GlobalIrreducibility.LConvKir
import Development.DiscreteGroups.GlobalIrreducibility.LConvBig

section
set_option linter.unusedSectionVars false

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConv

section Theta

variable {k : Type} [Field k]

theorem longElt_mul_self (n : ℕ) : longElt n k * longElt n k = 1 := Units.ext (antidiag_mul_self n k)

variable (k) in

def theta (n : ℕ) : GL (Fin n) k →* GL (Fin n) k :=
  (MulAut.conj (longElt n k)).toMonoidHom.comp (GlobalTheory.CuspRep.invT n k)

theorem theta_apply {n : ℕ} (g : GL (Fin n) k) :
    theta k n g = longElt n k * GlobalTheory.CuspRep.invT n k g * longElt n k := by
  simp [theta, MulAut.conj_apply, inv_eq_of_mul_eq_one_right (longElt_mul_self (k := k) n)]

theorem theta_theta {n : ℕ} (g : GL (Fin n) k) : theta k n (theta k n g) = g := by
  rw [theta_apply, theta_apply, GlobalTheory.T.long_element_conj_involutive]

theorem tilde_eq {n : ℕ} (g : GL (Fin n) k) : tilde g = theta k n g * longElt n k := by
  rw [theta_apply, mul_assoc, longElt_mul_self, mul_one]
  rfl

theorem corner_mul {m : ℕ} (g h : GL (Fin m) k) : corner (g * h) = corner g * corner h := by
  simp only [corner]
  rw [← map_mul, Prod.mk_mul_mk, mul_one]

theorem corner_one {m : ℕ} : corner (1 : GL (Fin m) k) = 1 := map_one (emb₂ k (stdSum (rfl : m + 1 = m + 1)))

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isFunctional_theta {ψ : AddChar k Circle} {ρ : Representation ℂ (GL (Fin n) k) V} {l : Module.Dual ℂ V}
    (hl : IsFunctional ψ ρ l) : IsFunctional ψ⁻¹ (ρ.comp (theta k n)) l := by
  intro u hu x
  obtain ⟨h1, h2⟩ := GlobalTheory.T.long_element_conj_unipotent_borel k n u hu
  show l (ρ (theta k n u) x) = _
  rw [theta_apply, hl _ h1, h2, AddChar.inv_apply]

theorem isIrreducible_comp_surjective {G G' : Type} [Group G] [Group G'] {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) (f : G' →* G) (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G' V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G' V) ≃o Subrepresentation ρ :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact W.apply_mem_toSubmodule g' hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.2 hρ

end Theta

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_theta (n : ℕ) : Continuous (theta k n) := by
  have hinvc : Continuous (GlobalTheory.CuspRep.invT n k) :=
    Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩
  have : (theta k n : GL (Fin n) k → GL (Fin n) k) =
      fun g => longElt n k * GlobalTheory.CuspRep.invT n k g * longElt n k := funext theta_apply
  rw [this]
  exact (continuous_const.mul hinvc).mul continuous_const

theorem continuous_corner (m : ℕ) : Continuous (corner : GL (Fin m) k → GL (Fin (m + 1)) k) :=
  (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (continuous_id.prodMk continuous_const))

def thetaIrr {n : ℕ} (σ : IrrRep (GL (Fin n) k)) : IrrRep (GL (Fin n) k) :=
  ⟨σ.V, σ.ρ.comp (theta k n), fun x => (σ.smooth x).preimage (continuous_theta n),
    isIrreducible_comp_surjective σ.irr _ fun g => ⟨_, theta_theta g⟩⟩

theorem isLocallyConstant_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hs : IsSmooth ρ) (v : V) :
    IsLocallyConstant fun g => ρ g v := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun x => g⁻¹ * x) ⁻¹' {x | ρ x v = v},
    (hs v).preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩
  have h : ρ (g⁻¹ * x) v = v := hx
  conv_rhs => rw [← h]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem continuous_inv_addChar {ψ : AddChar k Circle} (h : Continuous ψ) :
    Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun x => ψ (-x) := funext (AddChar.inv_apply ψ)
  rw [this]
  exact h.comp continuous_neg

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem IsWhitTest.sub {m : ℕ} {ψ : AddChar k Circle} {f f' : GL (Fin m) k → ℂ} (h : IsWhitTest ψ f)
    (h' : IsWhitTest ψ f') : IsWhitTest ψ fun g => f g - f' g :=
  _root_.UpperTheory.Reformulated.B.P6.BlockTriangularLevi.DiscreteGroups.sglob.LConv.IsWhitTest.sub h h'

theorem isWhitTest_tilde {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ}
    (π : IrrRep (GL (Fin (m + 1)) k)) (hcusp : IsCuspidal π.ρ) {l : Module.Dual ℂ π.V} (hl : IsFunctional ψ π.ρ l)
    (v : π.V) : IsWhitTest ψ⁻¹ fun g : GL (Fin m) k => l (π.ρ (tilde (corner g)) v) := by
  have hs2 : IsSmooth (π.ρ.comp (theta k (m + 1))) := (thetaIrr π).smooth
  have hl2 := isFunctional_theta hl
  have hJ : ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b →
      ∀ x : π.V, x ∈ twKer π.ρ (unipRad k (stdBlocks ![a, b] h)) 1 := by
    intro a b h ha hb x
    have := Submodule.Quotient.subsingleton_iff.1
      (hcusp.2 2 ![a, b] (stdBlocks ![a, b] h) (GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' k (m + 1) a b h ha hb))
    rw [this]
    exact Submodule.mem_top
  have hJ2 : ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b →
      ∀ x : π.V, x ∈ twKer (π.ρ.comp (theta k (m + 1))) (unipRad k (stdBlocks ![a, b] h)) 1 := by
    intro a b h ha hb x
    have h' : ∑ i, ![b, a] i = m + 1 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
      omega
    refine (Submodule.span_le.2 ?_) (hJ b a h' hb ha x)
    rintro _ ⟨n, y, rfl⟩
    refine Submodule.subset_span ⟨⟨theta k (m + 1) n, ?_⟩, y, ?_⟩
    · rw [theta_apply]
      exact GlobalTheory.T.long_element_conj_unipotent_radical k (m + 1) b a h' h n n.2
    · simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply]
      rw [theta_theta]
  have hψ'1 : (ψ⁻¹ : AddChar k Circle) ≠ 1 := fun h => hψ1 (inv_eq_one.1 h)
  obtain ⟨C2, hC2, hsupp2⟩ := exists_compact_mod_unipB_whittaker k ψ⁻¹ (continuous_inv_addChar hψc) hψ'1 m π.V
    (π.ρ.comp (theta k (m + 1))) hs2 hJ2 l hl2 (π.ρ (longElt (m + 1) k) v)
  have key : (fun g : GL (Fin m) k => l (π.ρ (tilde (corner g)) v)) =
      fun g => l ((π.ρ.comp (theta k (m + 1))) (corner g) (π.ρ (longElt (m + 1) k) v)) := by
    funext g
    rw [tilde_eq, map_mul, Module.End.mul_apply]
    rfl
  rw [key]
  refine ⟨fun u hu g => ?_, ?_, C2, hC2, hsupp2⟩
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum k m u hu
    beta_reduce
    rw [corner_mul, map_mul, Module.End.mul_apply, hl2 _ h1, h2]
  · exact ((isLocallyConstant_orbit hs2 _).comp_continuous (continuous_corner m)).comp l

end Local

theorem glue : Glue := by
  intro hGen hKir hBig hSep k _ _ _ _ _ ψ hψc hψ1 m hm π₁ π₂ hc₁ hc₂ H
  have hn₁ : Nontrivial π₁.V := nontrivial_of_irreducible π₁.irr
  have hn₂ : Nontrivial π₂.V := nontrivial_of_irreducible π₂.irr
  obtain ⟨l₁, hl₁0, hl₁⟩ := hGen k ψ hψc hψ1 _ _ π₁.ρ hn₁ hc₁
  obtain ⟨l₂, hl₂0, hl₂⟩ := hGen k ψ hψc hψ1 _ _ π₂.ρ hn₂ hc₂
  refine hBig k ψ m hm π₁ π₂ l₁ l₂ hl₁ hl₂ (fun v₁ v₂ hv => ?_) ?_
  · obtain ⟨I, hI, hS⟩ := hSep k m
    have hT := (isWhitTest_tilde hψc hψ1 π₁ hc₁ hl₁ v₁).sub (isWhitTest_tilde hψc hψ1 π₂ hc₂ hl₂ v₂)
    have h0 := hS ψ⁻¹ (continuous_inv_addChar hψc) _ hT fun σ l hl v => by
      rw [inv_inv] at hl
      obtain ⟨e, he₁, he₂⟩ := H (thetaIrr σ)
      obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar (thetaIrr σ).smooth (thetaIrr σ).irr
      have hl' : IsFunctional ψ⁻¹ (thetaIrr σ).ρ l := isFunctional_theta hl
      have e₁ := he₁ ω hω l₁ l hl₁ hl' I hI v₁ (σ.ρ (theta k m (longElt m k))⁻¹ v)
      have e₂ := he₂ ω hω l₂ l hl₂ hl' I hI v₂ (σ.ρ (theta k m (longElt m k))⁻¹ v)
      have ht : ∀ g : GL (Fin m) k,
          (thetaIrr σ).ρ (tilde g) (σ.ρ (theta k m (longElt m k))⁻¹ v) = σ.ρ g v := fun g => by
        show σ.ρ (theta k m (tilde g)) (σ.ρ (theta k m (longElt m k))⁻¹ v) = σ.ρ g v
        rw [tilde_eq, map_mul, theta_theta, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
      simp only [ht] at e₁ e₂
      simp only [hv] at e₁
      have e₃ := sub_eq_zero.2 (e₁.trans e₂.symm)
      rw [← map_sub] at e₃
      rw [← e₃]
      congr 1
      funext g
      exact sub_mul _ _ _
    have h1 := congrFun h0 1
    have hw : tilde (corner (1 : GL (Fin m) k)) = longElt (m + 1) k := by
      rw [corner_one, tilde_eq, map_one, one_mul]
    simp only [hw, Pi.zero_apply] at h1
    exact sub_eq_zero.1 h1
  · obtain ⟨a₁, ha₁⟩ : ∃ a, l₁ a = 1 := by
      obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 hl₁0
      exact ⟨(l₁ a)⁻¹ • a, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (by simpa using ha)]⟩
    obtain ⟨a₂, ha₂⟩ : ∃ a, l₂ a = 1 := by
      obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 hl₂0
      exact ⟨(l₂ a)⁻¹ • a, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (by simpa using ha)]⟩
    let ρ : Representation ℂ (GL (Fin (m + 1)) k) (π₁.V × π₂.V) :=
      { toFun := fun g => (π₁.ρ g).prodMap (π₂.ρ g)
        map_one' := by ext <;> simp
        map_mul' := fun g h => by ext <;> simp }
    have hρ : ∀ g v, ρ g v = (π₁.ρ g v.1, π₂.ρ g v.2) := fun _ _ => rfl
    have hs : IsSmooth ρ := fun v => by
      have : {g | ρ g v = v} = {g | π₁.ρ g v.1 = v.1} ∩ {g | π₂.ρ g v.2 = v.2} := by
        ext g
        simp [hρ, Prod.ext_iff]
      rw [this]
      exact (π₁.smooth _).inter (π₂.smooth _)
    obtain ⟨v, hv⟩ := hKir k ψ hψc hψ1 m _ ρ hs (a₁, a₂)
    have hA := (hv (l₁.comp (LinearMap.fst ℂ _ _)) fun u hu x => hl₁ u hu x.1).1
    have hB := (hv (l₁.comp (LinearMap.fst ℂ _ _) - l₂.comp (LinearMap.snd ℂ _ _)) fun u hu x => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, hρ,
        hl₁ u hu, hl₂ u hu]
      ring).2 (by simp [ha₁, ha₂])
    refine ⟨v.1, v.2, fun g => sub_eq_zero.1 (hB g), ?_⟩
    have : l₁ v.1 = 1 := hA.trans ha₁
    rw [this]
    exact one_ne_zero

end DiscreteGroups.sglob.LConv

end
end

section
noncomputable section

open ValuativeRel

namespace DiscreteGroups.sglob.LConv

theorem countable_quotient_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace.SeparableSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) : Countable (G ⧸ K) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable D := hDc.to_subtype
  refine Function.Surjective.countable (f := fun d : D => ((d : G) : G ⧸ K)) fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have ho : IsOpen ((fun x => x⁻¹ * g) ⁻¹' (K : Set G)) := hK.preimage (continuous_inv.mul continuous_const)
  obtain ⟨d, hd, hdD⟩ := hDd.inter_open_nonempty _ ho ⟨g, by simp⟩
  exact ⟨⟨d, hdD⟩, QuotientGroup.eq.2 hd⟩

theorem separableSpace_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) : TopologicalSpace.SeparableSpace (GL (Fin m) k) := by
  have : SecondCountableTopology (GL (Fin m) k) := inferInstance
  infer_instance

theorem unitOfUnif : UnitOfUnif := by
  intro hAlt hFin hUnif k _ _ _ _ m K hKo hKc H _ _ _ π hπ hcomm
  have := separableSpace_GL k m
  obtain ⟨N, hN⟩ := hUnif k m K hKo
  let F : Submodule ℂ H :=
    { carrier := {x | ∀ κ ∈ K, π κ x = x}
      add_mem' := fun {a b} ha hb κ hκ => by rw [map_add, ha κ hκ, hb κ hκ]
      zero_mem' := fun κ _ => map_zero _
      smul_mem' := fun c x hx κ hκ => by rw [map_smul, hx κ hκ] }
  have hF : IsClosed (F : Set H) := by
    have : (F : Set H) = ⋂ κ ∈ K, {x | π κ x = x} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_biInter fun κ _ => isClosed_eq (π κ).continuous continuous_id
  have : CompleteSpace F := hF.completeSpace_coe
  have h1 : ∀ x, F.starProjection x ∈ F := fun x => F.starProjection_apply_mem x
  have h2 : ∀ x ∈ F, F.starProjection x = x := fun x hx => Submodule.starProjection_eq_self_iff.2 hx
  obtain ⟨s, hs⟩ := hFin _ H π hπ hcomm F.starProjection (by ext x; exact h2 _ (h1 x)) (N ^ 2 + 1)
    (hAlt _ K hKo hKc (countable_quotient_of_isOpen K hKo) N hN H π hπ F.starProjection
      (isSelfAdjoint_starProjection F) h1 h2 _ (Nat.lt_succ_self _))
  exact ⟨s, fun x hx => h2 x hx ▸ hs x⟩

end DiscreteGroups.sglob.LConv

end
end

section
open scoped InnerProductSpace

noncomputable section

namespace DiscreteGroups.sglob.LConv

open CompanionTheory.D.gk.admitted

theorem irred_of_scalar {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖)
    (hsc : ∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (S : Submodule ℂ H) (hcl : IsClosed (S : Set H)) (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have : CompleteSpace S := hcl.completeSpace_coe
  have hcomm : ∀ g, S.starProjection * π g = π g * S.starProjection := by
    intro g
    ext z
    show S.starProjection (π g z) = π g (S.starProjection z)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hS g _ (S.starProjection_apply_mem z)
    · intro w hw
      rw [← map_sub, FinOfPIAux.inner_left π hπ]
      exact S.starProjection_inner_eq_zero z _ (hS _ _ hw)
  obtain ⟨c, hc⟩ := hsc _ hcomm
  have hP : ∀ z, S.starProjection z = c • z := fun z => by rw [hc]; rfl
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have h1 : c • x = x := by rw [← hP, Submodule.starProjection_eq_self_iff.mpr hx]
    have hc1 : c = 1 := by
      have h2 : (c - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hx0
    rw [eq_top_iff]
    intro z _
    have h3 := S.starProjection_apply_mem z
    rwa [hP, hc1, one_smul] at h3

theorem word_eq_mul_prod {R : Type*} [Ring R] (e : R) (he : e * e = e) (l : List R) :
    word e l = e * (l.map fun a => e * a * e).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [word_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc, he]

theorem finiteOfAlt : FiniteOfAlt := by
  intro G _ H _ _ _ π hπ hsc e he d hd
  have h : ∀ g : Fin d → G, stdPoly e (fun i => π (g i)) = 0 := by
    intro g
    have h0 := congrArg (fun X => e * X) (hd g)
    simp only [mul_zero] at h0
    rw [← h0, stdPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [word_eq_mul_prod e he, List.map_ofFn, mul_smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  obtain ⟨hfd, -⟩ := finite_rank_of_irreducible_unitary G H π hπ (irred_of_scalar π hπ hsc) e d h
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional _).mpr hfd
  refine ⟨s, fun x => ?_⟩
  rw [hs]
  exact LinearMap.mem_range_self (e : H →ₗ[ℂ] H) x

end DiscreteGroups.sglob.LConv

end
end

section
open Set ComplexConjugate

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace DiscreteGroups.sglob.LConvKM

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def InvF {G : Type*} [Group G] (ρ : Representation ℂ G M) (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, (starRingEnd ℂ) (B x y) = B y x) ∧ (∀ x, 0 ≤ (B x x).re) ∧ ∀ g x y, B (ρ g x) (ρ g y) = B x y

lemma InvF.smul {G : Type*} [Group G] {ρ : Representation ℂ G M} {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ}
    (hB : InvF ρ B) {r : ℝ} (hr : 0 ≤ r) : InvF ρ ((r : ℂ) • B) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, hB.1 x y]
  · simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_nonneg hr (hB.2.1 x)
  · simp only [LinearMap.smul_apply, smul_eq_mul, hB.2.2 g x y]

section form

variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)

lemma im_diag (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (x : M) : (B x x).im = 0 := by
  have h := congrArg Complex.im (herm x x)
  rw [Complex.conj_im] at h
  linarith

lemma norm_diag (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re) (x : M) :
    ‖B x x‖ = (B x x).re := by
  have h : B x x = ((B x x).re : ℂ) := (Complex.conj_eq_iff_re.mp (herm x x)).symm
  conv_lhs => rw [h]
  rw [Complex.norm_real, Real.norm_of_nonneg (psd x)]

lemma diag_expand_add (x y : M) :
    B (x + y) (x + y) + B (x - y) (x - y) = B x x + B x x + (B y y + B y y) := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  ring

lemma re_add_le (psd : ∀ x, 0 ≤ (B x x).re) (x y : M) :
    (B (x + y) (x + y)).re ≤ 2 * (B x x).re + 2 * (B y y).re := by
  have h := congrArg Complex.re (diag_expand_add B x y)
  simp only [Complex.add_re] at h
  linarith [psd (x - y)]

lemma apply_smul_smul (a : ℂ) (x y : M) : B (a • x) (a • y) = (starRingEnd ℂ) a * a * B x y := by
  simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  ring

lemma re_smul (a : ℂ) (x : M) : (B (a • x) (a • x)).re = Complex.normSq a * (B x x).re := by
  rw [apply_smul_smul, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]

lemma polar (x y : M) :
    4 * B x y = B (x + y) (x + y) - B (x - y) (x - y) - Complex.I * B (x + Complex.I • y) (x + Complex.I • y)
      + Complex.I * B (x - Complex.I • y) (x - Complex.I • y) := by
  simp only [map_add, map_sub, map_smulₛₗ, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.conj_I]
  linear_combination (2 * (B x y - B y x)) * Complex.I_sq

lemma norm_le_polar (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (x y : M) :
    4 * ‖B x y‖ ≤ (B (x + y) (x + y)).re + (B (x - y) (x - y)).re
      + (B (x + Complex.I • y) (x + Complex.I • y)).re + (B (x - Complex.I • y) (x - Complex.I • y)).re := by
  have h0 : ‖(4 : ℂ) * B x y‖ = 4 * ‖B x y‖ := by rw [norm_mul]; norm_num
  have h1 := norm_add_le (B (x + y) (x + y) - B (x - y) (x - y)
    - Complex.I * B (x + Complex.I • y) (x + Complex.I • y)) (Complex.I * B (x - Complex.I • y) (x - Complex.I • y))
  have h2 := norm_sub_le (B (x + y) (x + y) - B (x - y) (x - y))
    (Complex.I * B (x + Complex.I • y) (x + Complex.I • y))
  have h3 := norm_sub_le (B (x + y) (x + y)) (B (x - y) (x - y))
  simp only [norm_mul, Complex.norm_I, one_mul] at h1 h2
  rw [← polar B x y, h0] at h1
  simp only [norm_diag B herm psd] at h1 h2 h3
  linarith

lemma apply_eq_zero_of_re (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (u : M) (hu : (B u u).re = 0) (y : M) : B u y = 0 := by
  by_contra ha
  have hN : 0 < Complex.normSq (B u y) := Complex.normSq_pos.mpr ha
  have hN' : Complex.normSq (B u y) ≠ 0 := hN.ne'
  have huu : B u u = 0 := Complex.ext (by simpa using hu) (by simpa using im_diag B herm u)
  have hyu : B y u = (starRingEnd ℂ) (B u y) := (herm u y).symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 2 * t * Complex.normSq (B u y) = (B y y).re + 1 :=
    ⟨((B y y).re + 1) / (2 * Complex.normSq (B u y)), by field_simp⟩
  have ex : B (y - ((t : ℂ) * B u y) • u) (y - ((t : ℂ) * B u y) • u)
      = B y y - ((t : ℂ) * B u y) * B y u - (starRingEnd ℂ) ((t : ℂ) * B u y) * B u y
        + (starRingEnd ℂ) ((t : ℂ) * B u y) * ((t : ℂ) * B u y) * B u u := by
    simp only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring
  have key : B (y - ((t : ℂ) * B u y) • u) (y - ((t : ℂ) * B u y) • u)
      = B y y - ((2 * t * Complex.normSq (B u y) : ℝ) : ℂ) := by
    rw [ex, hyu, huu, map_mul, Complex.conj_ofReal]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have h := psd (y - ((t : ℂ) * B u y) • u)
  rw [key, Complex.sub_re, Complex.ofReal_re, ht] at h
  linarith

lemma eq_zero_of_re (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (xs : ℕ → M) (hsp : Submodule.span ℂ (Set.range xs) = ⊤)
    (h : ∀ i, (B (xs i) (xs i)).re = 0) (x y : M) : B x y = 0 := by
  have hle : Submodule.span ℂ (Set.range xs) ≤ LinearMap.ker B := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    ext z
    rw [LinearMap.zero_apply]
    exact apply_eq_zero_of_re B herm psd (xs i) (h i) z
  have hx : x ∈ LinearMap.ker B := hle (by rw [hsp]; exact Submodule.mem_top)
  rw [LinearMap.mem_ker] at hx
  rw [hx, LinearMap.zero_apply]

end form

lemma continuous_eval (a b : M) : Continuous fun F : M → M → ℂ => F a b :=
  (continuous_apply b).comp (continuous_apply a)

lemma comb_apply (F G : M → M → ℂ) (a b : ℝ) (x y : M) :
    (a • F + b • G) x y = (a : ℂ) * F x y + (b : ℂ) * G x y := by
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]

def ev (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : M → M → ℂ := fun x y => B x y

def sesqSet : Set (M → M → ℂ) :=
  {F | ∀ x y z, F (x + y) z = F x z + F y z} ∩ {F | ∀ (a : ℂ) x z, F (a • x) z = (starRingEnd ℂ) a * F x z} ∩
    {F | ∀ x y z, F x (y + z) = F x y + F x z} ∩ {F | ∀ (a : ℂ) x y, F x (a • y) = a * F x y}

def mkForm (F : M → M → ℂ) (h : F ∈ (sesqSet : Set (M → M → ℂ))) : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F h.1.1.1 (fun a x z => h.1.1.2 a x z) h.1.2
    (fun a x y => h.2 a x y)

@[simp] lemma mkForm_apply (F : M → M → ℂ) (h : F ∈ (sesqSet : Set (M → M → ℂ))) (x y : M) :
    mkForm F h x y = F x y := rfl

lemma ev_mem_sesq (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : ev B ∈ (sesqSet : Set (M → M → ℂ)) := by
  refine ⟨⟨⟨fun x y z => ?_, fun a x z => ?_⟩, fun x y z => ?_⟩, fun a x y => ?_⟩ <;>
    simp [ev]

lemma isClosed_sesqSet : IsClosed (sesqSet : Set (M → M → ℂ)) := by
  simp only [sesqSet, Set.ofPred_forall]
  refine ((IsClosed.inter ?_ ?_).inter ?_).inter ?_
  · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_eq (continuous_eval _ _) ((continuous_eval _ _).add (continuous_eval _ _))
  · exact isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun z =>
      isClosed_eq (continuous_eval _ _) (continuous_const.mul (continuous_eval _ _))
  · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_eq (continuous_eval _ _) ((continuous_eval _ _).add (continuous_eval _ _))
  · exact isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_eval _ _) (continuous_const.mul (continuous_eval _ _))

section cap

variable {G : Type*} [Group G] (ρ : Representation ℂ G M) (c : ℕ → ℝ) (xs : ℕ → M)

def Cap (F : M → M → ℂ) : Prop := ∀ n, ∑ i ∈ Finset.range n, c i * (F (xs i) (xs i)).re ≤ 1

def capSet : Set (M → M → ℂ) :=
  (sesqSet : Set (M → M → ℂ)) ∩ {F | ∀ x y, (starRingEnd ℂ) (F x y) = F y x} ∩ {F | ∀ x, 0 ≤ (F x x).re} ∩
    {F | ∀ g x y, F (ρ g x) (ρ g y) = F x y} ∩ {F | Cap c xs F}

lemma invF_mkForm {F : M → M → ℂ} (h : F ∈ capSet ρ c xs) : InvF ρ (mkForm F h.1.1.1.1) :=
  ⟨h.1.1.1.2, h.1.1.2, h.1.2⟩

lemma ev_mem {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ} (hB : InvF ρ B) (hc : Cap c xs (ev B)) : ev B ∈ capSet ρ c xs :=
  ⟨⟨⟨⟨ev_mem_sesq B, hB.1⟩, hB.2.1⟩, hB.2.2⟩, hc⟩

lemma isClosed_capSet : IsClosed (capSet ρ c xs) := by
  simp only [capSet, Cap, Set.ofPred_forall]
  refine (((isClosed_sesqSet.inter ?_).inter ?_).inter ?_).inter ?_
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (Complex.continuous_conj.comp (continuous_eval _ _)) (continuous_eval _ _)
  · exact isClosed_iInter fun x => isClosed_le continuous_const (Complex.continuous_re.comp (continuous_eval _ _))
  · exact isClosed_iInter fun g => isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_eval _ _) (continuous_eval _ _)
  · exact isClosed_iInter fun n => isClosed_le
      (continuous_finsetSum _ fun i _ => continuous_const.mul (Complex.continuous_re.comp (continuous_eval _ _)))
      continuous_const

lemma convex_capSet : Convex ℝ (capSet ρ c xs) := by
  intro F hF G hG a b ha hb hab
  obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, fh⟩, fp⟩, fi⟩, fk⟩ := hF
  obtain ⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, gh⟩, gp⟩, gi⟩, gk⟩ := hG
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro x y z; simp only [comb_apply, f1 x y z, g1 x y z]; ring
  · intro α x z; simp only [comb_apply, f2 α x z, g2 α x z]; ring
  · intro x y z; simp only [comb_apply, f3 x y z, g3 x y z]; ring
  · intro α x y; simp only [comb_apply, f4 α x y, g4 α x y]; ring
  · intro x y; simp only [comb_apply, map_add, map_mul, Complex.conj_ofReal, fh x y, gh x y]
  · intro x
    simp only [comb_apply, Complex.add_re, Complex.re_ofReal_mul]
    exact add_nonneg (mul_nonneg ha (fp x)) (mul_nonneg hb (gp x))
  · intro g x y; simp only [comb_apply, fi g x y, gi g x y]
  · intro n
    have e : ∑ i ∈ Finset.range n, c i * ((a • F + b • G) (xs i) (xs i)).re
        = a * ∑ i ∈ Finset.range n, c i * (F (xs i) (xs i)).re
          + b * ∑ i ∈ Finset.range n, c i * (G (xs i) (xs i)).re := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [comb_apply, Complex.add_re, Complex.re_ofReal_mul]
      ring
    rw [e]
    linarith [mul_le_mul_of_nonneg_left (fk n) ha, mul_le_mul_of_nonneg_left (gk n) hb]

lemma diag_bound (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (x : M) :
    ∃ R, ∀ F ∈ capSet ρ c xs, (F x x).re ≤ R := by
  have hx : x ∈ Submodule.span ℂ (Set.range xs) := by rw [hsp]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨1 / c i, fun F hF => ?_⟩
    have h1 := Finset.single_le_sum (f := fun j => c j * (F (xs j) (xs j)).re)
      (fun j _ => mul_nonneg (hc j).le (hF.1.1.2 (xs j))) (Finset.self_mem_range_succ i)
    have h2 := hF.2 (i + 1)
    rw [le_div_iff₀ (hc i)]
    linarith [mul_comm (F (xs i) (xs i)).re (c i)]
  | zero =>
    refine ⟨0, fun F hF => ?_⟩
    have h : mkForm F hF.1.1.1.1 0 0 = 0 := by simp only [map_zero, LinearMap.zero_apply]
    rw [mkForm_apply] at h
    rw [h, Complex.zero_re]
  | add x y _ _ hx hy =>
    obtain ⟨R₁, h₁⟩ := hx
    obtain ⟨R₂, h₂⟩ := hy
    refine ⟨2 * R₁ + 2 * R₂, fun F hF => ?_⟩
    have := re_add_le (mkForm F hF.1.1.1.1) hF.1.1.2 x y
    simp only [mkForm_apply] at this
    linarith [h₁ F hF, h₂ F hF]
  | smul a x _ hx =>
    obtain ⟨R, h⟩ := hx
    refine ⟨Complex.normSq a * R, fun F hF => ?_⟩
    have := re_smul (mkForm F hF.1.1.1.1) a x
    simp only [mkForm_apply] at this
    rw [this]
    exact mul_le_mul_of_nonneg_left (h F hF) (Complex.normSq_nonneg a)

lemma off_bound (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (x y : M) :
    ∃ R, ∀ F ∈ capSet ρ c xs, ‖F x y‖ ≤ R := by
  obtain ⟨R₁, h₁⟩ := diag_bound ρ c xs hsp hc (x + y)
  obtain ⟨R₂, h₂⟩ := diag_bound ρ c xs hsp hc (x - y)
  obtain ⟨R₃, h₃⟩ := diag_bound ρ c xs hsp hc (x + Complex.I • y)
  obtain ⟨R₄, h₄⟩ := diag_bound ρ c xs hsp hc (x - Complex.I • y)
  refine ⟨(R₁ + R₂ + R₃ + R₄) / 4, fun F hF => ?_⟩
  have := norm_le_polar (mkForm F hF.1.1.1.1) hF.1.1.1.2 hF.1.1.2 x y
  simp only [mkForm_apply] at this
  linarith [h₁ F hF, h₂ F hF, h₃ F hF, h₄ F hF]

lemma isCompact_capSet (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) :
    IsCompact (capSet ρ c xs) := by
  choose R hR using off_bound ρ c xs hsp hc
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun x => isCompact_univ_pi fun y => isCompact_closedBall (0 : ℂ) (R x y))
    (isClosed_capSet ρ c xs) fun F hF => ?_
  simp only [Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  exact fun x y => hR x y F hF

lemma ray (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (hB : ev B ∈ (capSet ρ c xs).extremePoints ℝ) (B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (h1 : InvF ρ B') (h2 : InvF ρ (B - B')) : ∃ k : ℂ, ∀ x y, B' x y = k * B x y := by
  obtain ⟨hBm, hBx⟩ := mem_extremePoints.mp hB
  have hcapB : ∀ n, ∑ i ∈ Finset.range n, c i * (B (xs i) (xs i)).re ≤ 1 := hBm.2
  have hsplit : ∀ i, c i * (B (xs i) (xs i)).re
      = c i * (B' (xs i) (xs i)).re + c i * ((B - B') (xs i) (xs i)).re := by
    intro i; rw [LinearMap.sub_apply, LinearMap.sub_apply, Complex.sub_re]; ring
  have h0' : ∀ i, 0 ≤ c i * (B' (xs i) (xs i)).re := fun i => mul_nonneg (hc i).le (h1.2.1 _)
  have h0'' : ∀ i, 0 ≤ c i * ((B - B') (xs i) (xs i)).re := fun i => mul_nonneg (hc i).le (h2.2.1 _)
  have hb' : ∀ n, ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re ≤ 1 := fun n => by
    have := hcapB n
    simp only [hsplit, Finset.sum_add_distrib] at this
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) => h0'' i]
  have hb'' : ∀ n, ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re ≤ 1 := fun n => by
    have := hcapB n
    simp only [hsplit, Finset.sum_add_distrib] at this
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) => h0' i]
  have hs' := summable_of_sum_range_le h0' hb'
  have hs'' := summable_of_sum_range_le h0'' hb''
  have hP : ∑' i, c i * (B' (xs i) (xs i)).re + ∑' i, c i * ((B - B') (xs i) (xs i)).re ≤ 1 := by
    rw [← hs'.tsum_add hs'']
    refine (hs'.add hs'').tsum_le_of_sum_range_le fun n => ?_
    have := hcapB n
    simp only [hsplit] at this
    exact this
  have hle' : ∀ n, ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re
      ≤ ∑' i, c i * (B' (xs i) (xs i)).re := fun n => hs'.sum_le_tsum _ (fun i _ => h0' i)
  have hle'' : ∀ n, ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re
      ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re := fun n => hs''.sum_le_tsum _ (fun i _ => h0'' i)
  have hi' : ∀ i, c i * (B' (xs i) (xs i)).re ≤ ∑' i, c i * (B' (xs i) (xs i)).re :=
    fun i => hs'.le_tsum i (fun j _ => h0' j)
  have hi'' : ∀ i, c i * ((B - B') (xs i) (xs i)).re ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re :=
    fun i => hs''.le_tsum i (fun j _ => h0'' j)
  have hnn' : 0 ≤ ∑' i, c i * (B' (xs i) (xs i)).re := tsum_nonneg h0'
  have hnn'' : 0 ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re := tsum_nonneg h0''
  generalize ∑' i, c i * (B' (xs i) (xs i)).re = p' at hP hle' hi' hnn'
  generalize ∑' i, c i * ((B - B') (xs i) (xs i)).re = p'' at hP hle'' hi'' hnn''
  have zero_of : ∀ B₁ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, InvF ρ B₁ → (∀ i, c i * (B₁ (xs i) (xs i)).re ≤ 0) →
      ∀ x y, B₁ x y = 0 := by
    intro B₁ hB₁ hle x y
    refine eq_zero_of_re B₁ hB₁.1 hB₁.2.1 xs hsp (fun i => ?_) x y
    have h0 := mul_nonneg (hc i).le (hB₁.2.1 (xs i))
    have := le_antisymm (hle i) h0
    exact (mul_eq_zero.mp this).resolve_left (hc i).ne'
  rcases hnn'.lt_or_eq with hp' | hp'
  swap
  · refine ⟨0, fun x y => ?_⟩
    rw [zero_of B' h1 (fun i => (hi' i).trans hp'.ge) x y, zero_mul]
  rcases hnn''.lt_or_eq with hp'' | hp''
  swap
  · refine ⟨1, fun x y => ?_⟩
    have := zero_of (B - B') h2 (fun i => (hi'' i).trans hp''.ge) x y
    rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_eq_zero] at this
    rw [this, one_mul]
  have hPpos : 0 < p' + p'' := by linarith
  have hne' := hp'.ne'
  have hne'' := hp''.ne'
  have hPne := hPpos.ne'
  have hr' : (0 : ℝ) ≤ (p' + p'') / p' := div_nonneg hPpos.le hp'.le
  have hr'' : (0 : ℝ) ≤ (p' + p'') / p'' := div_nonneg hPpos.le hp''.le
  have hF1 : ev ((((p' + p'') / p' : ℝ) : ℂ) • B') ∈ capSet ρ c xs := by
    refine ev_mem ρ c xs (h1.smul hr') fun n => ?_
    show ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p' : ℝ) : ℂ) • B') (xs i) (xs i)).re ≤ 1
    have e : ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p' : ℝ) : ℂ) • B') (xs i) (xs i)).re
        = (p' + p'') / p' * ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      ring
    rw [e]
    calc (p' + p'') / p' * ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re
        ≤ (p' + p'') / p' * p' := mul_le_mul_of_nonneg_left (hle' n) hr'
      _ = p' + p'' := by field_simp
      _ ≤ 1 := hP
  have hF2 : ev ((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) ∈ capSet ρ c xs := by
    refine ev_mem ρ c xs (h2.smul hr'') fun n => ?_
    show ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) (xs i) (xs i)).re ≤ 1
    have e : ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) (xs i) (xs i)).re
        = (p' + p'') / p'' * ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      ring
    rw [e]
    calc (p' + p'') / p'' * ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re
        ≤ (p' + p'') / p'' * p'' := mul_le_mul_of_nonneg_left (hle'' n) hr''
      _ = p' + p'' := by field_simp
      _ ≤ 1 := hP
  have k1r : p' / (p' + p'') * ((p' + p'') / p') = 1 := by field_simp
  have k2r : p'' / (p' + p'') * ((p' + p'') / p'') = 1 := by field_simp
  have k1 : ((p' / (p' + p'') : ℝ) : ℂ) * (((p' + p'') / p' : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, k1r, Complex.ofReal_one]
  have k2 : ((p'' / (p' + p'') : ℝ) : ℂ) * (((p' + p'') / p'' : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, k2r, Complex.ofReal_one]
  have hseg : ev B ∈ openSegment ℝ (ev ((((p' + p'') / p' : ℝ) : ℂ) • B'))
      (ev ((((p' + p'') / p'' : ℝ) : ℂ) • (B - B'))) := by
    refine ⟨p' / (p' + p''), p'' / (p' + p''), div_pos hp' hPpos, div_pos hp'' hPpos, by field_simp, ?_⟩
    funext x y
    rw [comb_apply]
    simp only [ev, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
    linear_combination (B' x y) * k1 + (B x y - B' x y) * k2
  have hx := hBx _ hF1 _ hF2 hseg
  refine ⟨((p' / (p' + p'') : ℝ) : ℂ), fun x y => ?_⟩
  have e := congrFun (congrFun hx.1 x) y
  simp only [ev, LinearMap.smul_apply, smul_eq_mul] at e
  rw [← e]
  linear_combination (-(B' x y)) * k1

end cap

theorem extreme_exists_core {G : Type*} [Group G] (ρ : Representation ℂ G M)
    (hspan : ∃ s : Set M, s.Countable ∧ Submodule.span ℂ s = ⊤)
    (B₀ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (h₀ : InvF ρ B₀) (f : M) (hf : B₀ f f ≠ 0) :
    ∃ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (InvF ρ B ∧ ∀ B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, InvF ρ B' → InvF ρ (B - B') →
      ∃ c : ℂ, ∀ x y, B' x y = c * B x y) ∧ B f f ≠ 0 := by
  obtain ⟨s, hsc, hss⟩ := hspan
  obtain ⟨xs, hxs⟩ := (hsc.insert 0).exists_eq_range (Set.insert_nonempty 0 s)
  have hsp : Submodule.span ℂ (Set.range xs) = ⊤ := by rw [← hxs, Submodule.span_insert_zero, hss]
  obtain ⟨c, hc_def⟩ : ∃ c : ℕ → ℝ, c = fun i => (1 / 2 : ℝ) ^ i / (1 + (B₀ (xs i) (xs i)).re) := ⟨_, rfl⟩
  have hc : ∀ i, 0 < c i := fun i => by
    simp only [hc_def]
    exact div_pos (by positivity) (by linarith [h₀.2.1 (xs i)])
  have hhalf : InvF ρ (((1 / 2 : ℝ) : ℂ) • B₀) := h₀.smul (by norm_num)
  have hmem₀ : ev (((1 / 2 : ℝ) : ℂ) • B₀) ∈ capSet ρ c xs := by
    refine ev_mem ρ c xs hhalf fun n => ?_
    show ∑ i ∈ Finset.range n, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re ≤ 1
    have hterm : ∀ i, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re ≤ (1 / 2) * (1 / 2 : ℝ) ^ i := by
      intro i
      have hr := h₀.2.1 (xs i)
      have hp : (0 : ℝ) < (1 / 2) ^ i := by positivity
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, hc_def]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ∑ i ∈ Finset.range n, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re
        ≤ ∑ i ∈ Finset.range n, (1 / 2) * (1 / 2 : ℝ) ^ i := Finset.sum_le_sum fun i _ => hterm i
      _ = (1 / 2) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
      _ ≤ 1 := by linarith [sum_geometric_two_le n]
  obtain ⟨F, hFe, hFf⟩ : ∃ F ∈ (capSet ρ c xs).extremePoints ℝ, F f f ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have hZ : IsClosed {F : M → M → ℂ | F f f = 0} := isClosed_eq (continuous_eval f f) continuous_const
    have hZc : Convex ℝ {F : M → M → ℂ | F f f = 0} := by
      intro F hF G hG a b _ _ _
      have hF' : F f f = 0 := hF
      have hG' : G f f = 0 := hG
      show (a • F + b • G) f f = 0
      rw [comb_apply, hF', hG', mul_zero, mul_zero, add_zero]
    have hsub : capSet ρ c xs ⊆ {F | F f f = 0} := by
      rw [← closure_convexHull_extremePoints (isCompact_capSet ρ c xs hsp hc) (convex_capSet ρ c xs)]
      exact closure_minimal (convexHull_min (fun F hF => hcon F hF) hZc) hZ
    have h : ((1 / 2 : ℝ) : ℂ) * B₀ f f = 0 := hsub hmem₀
    apply hf
    simpa using h
  have hFm := (mem_extremePoints.mp hFe).1
  exact ⟨mkForm F hFm.1.1.1.1, ⟨invF_mkForm ρ c xs hFm, fun B' h1 h2 => ray ρ c xs hsp hc (mkForm F hFm.1.1.1.1) hFe B' h1 h2⟩, hFf⟩

end DiscreteGroups.sglob.LConvKM
end
end

section
namespace DiscreteGroups.sglob.LConv

theorem extremeExists : ExtremeExists := by
  intro G M _ _ _ ρ hspan B₀ hB₀ f hf
  obtain ⟨B, ⟨hB, hext⟩, hBf⟩ := DiscreteGroups.sglob.LConvKM.extreme_exists_core ρ hspan B₀ hB₀ f hf
  exact ⟨B, ⟨hB, hext⟩, hBf⟩

end DiscreteGroups.sglob.LConv
end

section
noncomputable section

open scoped InnerProductSpace
open UniformSpace

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def IsPsd (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop := (∀ x y, starRingEnd ℂ (B x y) = B y x) ∧ ∀ x, 0 ≤ (B x x).re

def Pre (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (_ : IsPsd B) : Type := M

variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)

instance : AddCommGroup (Pre B hB) := inferInstanceAs (AddCommGroup M)
instance : Module ℂ (Pre B hB) := inferInstanceAs (Module ℂ M)

instance core : PreInnerProductSpace.Core ℂ (Pre B hB) where
  inner x y := B x y
  conj_inner_symm x y := hB.1 y x
  re_inner_nonneg x := hB.2 x
  add_left x y z := LinearMap.map_add₂ B x y z
  smul_left x y r := (LinearMap.map_smulₛₗ₂ B r x y).trans (smul_eq_mul _ _)

instance : SeminormedAddCommGroup (Pre B hB) := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
instance : InnerProductSpace ℂ (Pre B hB) := InnerProductSpace.ofCore (core B hB)

abbrev Hs := Completion (Pre B hB)

def iota : M →ₗ[ℂ] Hs B hB := (Completion.toComplL : Pre B hB →L[ℂ] Hs B hB).toLinearMap

theorem iota_apply (x : M) : iota B hB x = ((show Pre B hB from x : Pre B hB) : Hs B hB) := rfl

theorem inner_iota (x y : M) : ⟪iota B hB x, iota B hB y⟫_ℂ = B x y := by
  rw [iota_apply, iota_apply, Completion.inner_coe]; rfl

theorem re_B (x : M) : (B x x).re = ‖iota B hB x‖ ^ 2 := by
  have h := @inner_self_eq_norm_sq ℂ _ _ _ _ (iota B hB x)
  rw [inner_iota] at h
  simpa using h

theorem ind {p : Hs B hB → Prop} (hp : IsClosed {y | p y}) (h : ∀ x : M, p (iota B hB x)) (y : Hs B hB) :
    p y :=
  Completion.induction_on y hp fun a => h a

theorem ext_iota {T S : Hs B hB →L[ℂ] Hs B hB} (h : ∀ x, T (iota B hB x) = S (iota B hB x)) : T = S :=
  ContinuousLinearMap.ext fun y => ind B hB (p := fun y => T y = S y) (isClosed_eq T.continuous S.continuous) h y

variable {G : Type} [Group G] (ρ : Representation ℂ G M)

theorem rho_mul (g h : G) (x : M) : ρ (g * h) x = ρ g (ρ h x) := by rw [map_mul]; rfl
theorem rho_one (x : M) : ρ 1 x = x := by rw [map_one]; rfl
theorem rho_inv (g : G) (x : M) : ρ g⁻¹ (ρ g x) = x := by rw [← rho_mul, inv_mul_cancel, rho_one]

variable (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

def rhoP (g : G) : Pre B hB →ₗ[ℂ] Pre B hB := ρ g

include hinv in
theorem norm_rhoP (g : G) (x : Pre B hB) : ‖rhoP B hB ρ g x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) x]
  rw [show ⟪rhoP B hB ρ g x, rhoP B hB ρ g x⟫_ℂ = ⟪x, x⟫_ℂ from hinv g x x]

def piF (g : G) : Hs B hB →L[ℂ] Hs B hB :=
  (LinearMap.mkContinuous (rhoP B hB ρ g) 1 fun x => by rw [one_mul, norm_rhoP B hB ρ hinv]).completion

theorem piF_iota (g : G) (x : M) : piF B hB ρ hinv g (iota B hB x) = iota B hB (ρ g x) := by
  rw [iota_apply, piF, ContinuousLinearMap.completion_apply_coe]; rfl

def pi : G →* (Hs B hB →L[ℂ] Hs B hB) where
  toFun := piF B hB ρ hinv
  map_one' := ext_iota B hB fun x => by rw [piF_iota, rho_one]; rfl
  map_mul' g h := ext_iota B hB fun x => by
    rw [ContinuousLinearMap.mul_apply, piF_iota, piF_iota, piF_iota, rho_mul]

theorem pi_iota (g : G) (x : M) : pi B hB ρ hinv g (iota B hB x) = iota B hB (ρ g x) := piF_iota B hB ρ hinv g x

theorem norm_pi (g : G) (y : Hs B hB) : ‖pi B hB ρ hinv g y‖ = ‖y‖ :=
  ind B hB (p := fun y => ‖pi B hB ρ hinv g y‖ = ‖y‖)
    (isClosed_eq (continuous_norm.comp (pi B hB ρ hinv g).continuous) continuous_norm)
    (fun x => by rw [pi_iota, iota_apply, iota_apply, Completion.norm_coe, Completion.norm_coe]; exact norm_rhoP B hB ρ hinv g x) y

theorem pi_inner (g : G) (u v : Hs B hB) : ⟪pi B hB ρ hinv g u, pi B hB ρ hinv g v⟫_ℂ = ⟪u, v⟫_ℂ :=
  let V : Hs B hB →ₗᵢ[ℂ] Hs B hB := { toLinearMap := (pi B hB ρ hinv g : Hs B hB →ₗ[ℂ] Hs B hB), norm_map' := norm_pi B hB ρ hinv g }
  V.inner_map_map u v

theorem inner_left (g : G) (v w : Hs B hB) : ⟪pi B hB ρ hinv g v, w⟫_ℂ = ⟪v, pi B hB ρ hinv g⁻¹ w⟫_ℂ := by
  rw [← pi_inner B hB ρ hinv g v, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

theorem star_pi (g : G) : star (pi B hB ρ hinv g) = pi B hB ρ hinv g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  rw [inner_left B hB ρ hinv g⁻¹, inv_inv]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
end
end

section
noncomputable section

open scoped InnerProductSpace
open UniformSpace

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

theorem comm_apply {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {S T : E →L[ℂ] E}
    (h : S * T = T * S) (v : E) : S (T v) = T (S v) := by
  have := congrArg (fun A : E →L[ℂ] E => A v) h
  exact this

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)

def formOf (S : Hs B hB →L[ℂ] Hs B hB) : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ⟪iota B hB x, S (iota B hB y)⟫_ℂ)
    (fun x₁ x₂ y => by simp [map_add, inner_add_left])
    (fun c x y => by simp [map_smul, inner_smul_left])
    (fun x y₁ y₂ => by simp [map_add, inner_add_right])
    (fun c x y => by simp [map_smul, inner_smul_right])

theorem formOf_apply (S : Hs B hB →L[ℂ] Hs B hB) (x y : M) :
    formOf B hB S x y = ⟪iota B hB x, S (iota B hB y)⟫_ℂ := rfl

variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

theorem scalar_sa (hext : IsExtremeForm ρ B) (S : Hs B hB →L[ℂ] Hs B hB) (hS : IsSelfAdjoint S)
    (hc : ∀ g, S * pi B hB ρ hinv g = pi B hB ρ hinv g * S) : ∃ c : ℂ, S = c • 1 := by
  set a : ℝ := (2 * (‖S‖ + 1))⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have hsym : ∀ u v, ⟪S u, v⟫_ℂ = ⟪u, S v⟫_ℂ := fun u v => by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hS.star_eq]
  have hherm : ∀ x y, starRingEnd ℂ (formOf B hB S x y) = formOf B hB S y x := fun x y => by
    rw [formOf_apply, formOf_apply, inner_conj_symm, hsym]
  have hinvQ : ∀ g x y, formOf B hB S (ρ g x) (ρ g y) = formOf B hB S x y := fun g x y => by
    rw [formOf_apply, formOf_apply, ← pi_iota B hB ρ hinv, ← pi_iota B hB ρ hinv, comm_apply (hc g), pi_inner]
  have hbd : ∀ x, |(formOf B hB S x x).re| ≤ ‖S‖ * ‖iota B hB x‖ ^ 2 := fun x => by
    rw [formOf_apply]
    calc _ ≤ ‖⟪iota B hB x, S (iota B hB x)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖iota B hB x‖ * ‖S (iota B hB x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖iota B hB x‖ * (‖S‖ * ‖iota B hB x‖) := by gcongr; exact S.le_opNorm _
      _ = _ := by ring
  have key : ∀ x, |a * (formOf B hB S x x).re| ≤ (B x x).re / 2 := fun x => by
    rw [re_B B hB, abs_mul, abs_of_pos ha]
    calc a * |(formOf B hB S x x).re| ≤ a * ((‖S‖ + 1) * ‖iota B hB x‖ ^ 2) := by
          gcongr; exact (hbd x).trans (by gcongr; linarith)
      _ = _ := by rw [ha_def]; field_simp
  have h1 : IsInvForm ρ (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  have h2 : IsInvForm ρ (B - (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S)) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_sub, map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  obtain ⟨c, hc'⟩ := hext.2 _ h1 h2
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hQ : ∀ x y, formOf B hB S x y = ((a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))) * B x y := fun x y => by
    have h := hc' x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ ha']
    linear_combination h
  set d := (a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))
  have hQ' : ∀ x y : M, ⟪iota B hB x, S (iota B hB y)⟫_ℂ = d * ⟪iota B hB x, iota B hB y⟫_ℂ := fun x y => by
    rw [inner_iota, ← formOf_apply]; exact hQ x y
  have hall : ∀ u v : Hs B hB, ⟪u, S v⟫_ℂ = d * ⟪u, v⟫_ℂ := by
    intro u v
    refine Completion.induction_on₂ u v ?_ fun p q => ?_
    · exact isClosed_eq (continuous_fst.inner (S.continuous.comp continuous_snd))
        (continuous_const.mul (continuous_fst.inner continuous_snd))
    · exact hQ' p q
  refine ⟨d, ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_⟩
  rw [hall, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]

theorem commutant (hext : IsExtremeForm ρ B) (T : Hs B hB →L[ℂ] Hs B hB)
    (hT : ∀ g, T * pi B hB ρ hinv g = pi B hB ρ hinv g * T) : ∃ c : ℂ, T = c • 1 := by
  have hT' : ∀ g, star T * pi B hB ρ hinv g = pi B hB ρ hinv g * star T := fun g => by
    have h := congrArg star (hT g⁻¹)
    simp only [star_mul, star_pi, inv_inv] at h
    exact h.symm
  have hre : ∀ g, (realPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * realPart T := fun g => by
    simp only [realPart_apply_coe, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hT, hT']
  have him : ∀ g, (imaginaryPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * imaginaryPart T := fun g => by
    simp only [imaginaryPart_apply_coe, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hT, hT']
  obtain ⟨c₁, h₁⟩ := scalar_sa B hB ρ hinv hext _ (realPart T).prop hre
  obtain ⟨c₂, h₂⟩ := scalar_sa B hB ρ hinv hext _ (imaginaryPart T).prop him
  refine ⟨c₁ + Complex.I * c₂, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [h₁, h₂, smul_smul, add_smul]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
end
end

section
noncomputable section

open scoped InnerProductSpace
open UniformSpace GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)
variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

def fixSub (K : Subgroup G) : Submodule ℂ M where
  carrier := {a | ∀ κ ∈ K, ρ κ a = a}
  add_mem' {a b} ha hb κ hκ := by rw [map_add, ha κ hκ, hb κ hκ]
  zero_mem' κ _ := map_zero _
  smul_mem' c a ha κ hκ := by rw [map_smul, ha κ hκ]

include hinv in
theorem avg_exists [TopologicalSpace G] [IsTopologicalGroup G] (hsm : IsSmooth ρ) (Z : Submodule ℂ M)
    (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z) (K : Subgroup G) (hKc : IsCompact (K : Set G)) (x : M)
    (hx : ∀ κ ∈ K, ρ κ x = x) (z : M) (hz : z ∈ Z) :
    ∃ a ∈ Z, (∀ κ ∈ K, ρ κ a = a) ∧
      dist (iota B hB x) (iota B hB a) ≤ dist (iota B hB x) (iota B hB z) := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hf : Continuous fun g : G => ρ g z := by
    refine continuous_discrete_rng.2 fun b => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨(fun h => g⁻¹ * h) ⁻¹' {h | ρ h z = z}, fun h hh => ?_,
      (continuous_mul_left g⁻¹).isOpen_preimage _ (hsm z), ?_⟩
    · simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] at hh hg ⊢
      rw [← hg, show h = g * (g⁻¹ * h) by group, rho_mul, hh]
    · simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel, rho_one]
  have hfin : ((fun g : G => ρ g z) '' (K : Set G)).Finite := (hKc.image hf).finite_of_discrete
  set O := hfin.toFinset with hO
  have hmem : ∀ m, m ∈ O ↔ ∃ k ∈ K, ρ k z = m := fun m => by
    rw [hO, Set.Finite.mem_toFinset]; rfl
  have hzO : z ∈ O := (hmem z).2 ⟨1, K.one_mem, rho_one ρ z⟩
  have hcard : (O.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨z, hzO⟩)
  have hcardC : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨z, hzO⟩)
  refine ⟨(O.card : ℂ)⁻¹ • ∑ m ∈ O, m, Z.smul_mem _ (Z.sum_mem fun m hm => ?_), fun κ hκ => ?_, ?_⟩
  · obtain ⟨k, _, rfl⟩ := (hmem m).1 hm
    exact hZ k z hz
  · rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (fun m => ρ κ m) (fun m => ρ κ⁻¹ m) (fun m hm => ?_) (fun m hm => ?_)
      (fun m _ => rho_inv ρ κ m) (fun m _ => ?_) (fun _ _ => rfl)
    · obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
      exact (hmem _).2 ⟨κ * k, K.mul_mem hκ hk, rho_mul ρ κ k z⟩
    · obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
      exact (hmem _).2 ⟨κ⁻¹ * k, K.mul_mem (K.inv_mem hκ) hk, rho_mul ρ κ⁻¹ k z⟩
    · simp
  · have hdist : ∀ m ∈ O, ‖iota B hB x - iota B hB m‖ = ‖iota B hB x - iota B hB z‖ := by
      intro m hm
      obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
      have e : iota B hB x - iota B hB (ρ k z) = pi B hB ρ hinv k (iota B hB x - iota B hB z) := by
        rw [map_sub, pi_iota, pi_iota, hx k hk]
      rw [e, norm_pi]
    have hsum : iota B hB x - iota B hB ((O.card : ℂ)⁻¹ • ∑ m ∈ O, m) =
        (O.card : ℂ)⁻¹ • ∑ m ∈ O, (iota B hB x - iota B hB m) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, map_smul, map_sum,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcardC, one_smul]
    rw [dist_eq_norm, dist_eq_norm, hsum, norm_smul]
    calc ‖((O.card : ℂ))⁻¹‖ * ‖∑ m ∈ O, (iota B hB x - iota B hB m)‖
        ≤ ‖((O.card : ℂ))⁻¹‖ * ∑ m ∈ O, ‖iota B hB x - iota B hB m‖ := by gcongr; exact norm_sum_le _ _
      _ = ‖((O.card : ℂ))⁻¹‖ * (O.card * ‖iota B hB x - iota B hB z‖) := by
          rw [Finset.sum_congr rfl hdist, Finset.sum_const, nsmul_eq_mul]
      _ = ‖iota B hB x - iota B hB z‖ := by
          rw [norm_inv, Complex.norm_natCast, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
end
end

section
noncomputable section

open scoped InnerProductSpace
open UniformSpace GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)
variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

include hinv in
theorem closure_top (hext : IsExtremeForm ρ B) (Z : Submodule ℂ M) (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z)
    (z₀ : M) (hz₀ : z₀ ∈ Z) (hne : B z₀ z₀ ≠ 0) (y : Hs B hB) :
    y ∈ (Z.map (iota B hB)).topologicalClosure := by
  set W := (Z.map (iota B hB)).topologicalClosure with hW
  have : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hWinv : ∀ g, ∀ w ∈ W, pi B hB ρ hinv g w ∈ W := by
    intro g w hw
    rw [← SetLike.mem_coe, hW, Submodule.topologicalClosure_coe] at hw ⊢
    refine map_mem_closure (pi B hB ρ hinv g).continuous hw fun v hv => ?_
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv
    exact Submodule.mem_map.2 ⟨ρ g z, hZ g z hz, (pi_iota B hB ρ hinv g z).symm⟩
  have hP : ∀ g, W.starProjection * pi B hB ρ hinv g = pi B hB ρ hinv g * W.starProjection := by
    intro g
    refine ContinuousLinearMap.ext fun v => ?_
    show W.starProjection (pi B hB ρ hinv g v) = pi B hB ρ hinv g (W.starProjection v)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hWinv g _ (W.starProjection_apply_mem v)
    · intro w hw
      rw [← map_sub, inner_left]
      exact W.starProjection_inner_eq_zero v _ (hWinv _ _ hw)
  obtain ⟨c, hc⟩ := commutant B hB ρ hinv hext _ hP
  have hι0 : iota B hB z₀ ≠ 0 := fun h => hne (by rw [← inner_iota B hB, h, inner_zero_left])
  have hmem : iota B hB z₀ ∈ W := Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hz₀)
  have h1 : W.starProjection (iota B hB z₀) = iota B hB z₀ := Submodule.starProjection_eq_self_iff.2 hmem
  rw [hc] at h1
  have hc1 : c = 1 := by
    have e : (c - 1) • iota B hB z₀ = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]; simpa using h1
    rcases smul_eq_zero.1 e with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hι0
  apply Submodule.starProjection_eq_self_iff.1
  rw [hc, hc1, one_smul]; rfl

end DiscreteGroups.sglob.LConv.IrreduciblePresentation

namespace DiscreteGroups.sglob.LConv

open IrreduciblePresentation in
theorem extremeIrred : ExtremeIrred := by
  intro G M _ _ _ _ _ ρ hsm hK hAdm B hext Z hZ
  by_cases h0 : ∀ z ∈ Z, B z z = 0
  · exact Or.inl h0
  right
  simp only [not_forall, exists_prop] at h0
  obtain ⟨z₀, hz₀, hne⟩ := h0
  have hB : IsPsd B := ⟨hext.1.1, hext.1.2.1⟩
  have hinv := hext.1.2.2
  intro x
  obtain ⟨K, hKo, hKc, hxK⟩ := hK x
  obtain ⟨s, hs⟩ := hAdm K hKo hKc (Hs B hB) (pi B hB ρ hinv) (norm_pi B hB ρ hinv)
    (commutant B hB ρ hinv hext)
  set L : Submodule ℂ (Hs B hB) := (Z ⊓ fixSub ρ K).map (iota B hB) with hL
  have hle : L ≤ Submodule.span ℂ (s : Set (Hs B hB)) := by
    intro v hv
    obtain ⟨a, ⟨_, haK⟩, rfl⟩ := Submodule.mem_map.1 hv
    exact hs _ fun κ hκ => by rw [pi_iota, haK κ hκ]
  have : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hle
  have hcl : IsClosed (L : Set (Hs B hB)) := L.closed_of_finiteDimensional
  have hxL : iota B hB x ∈ L := by
    rw [← SetLike.mem_coe, ← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hxW := closure_top B hB ρ hinv hext Z hZ z₀ hz₀ hne (iota B hB x)
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hxW
    obtain ⟨_, hb, hd⟩ := hxW ε hε
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hb
    obtain ⟨a, haZ, haK, hda⟩ := avg_exists B hB ρ hinv hsm Z hZ K hKc x hxK z hz
    exact ⟨iota B hB a, Submodule.mem_map_of_mem ⟨haZ, haK⟩, lt_of_le_of_lt hda hd⟩
  obtain ⟨a, ⟨haZ, _⟩, ha⟩ := Submodule.mem_map.1 hxL
  refine ⟨a, haZ, ?_⟩
  rw [← inner_iota B hB, map_sub, ha, sub_self, inner_zero_left]

end DiscreteGroups.sglob.LConv
end
end

section
namespace DiscreteGroups.sglob.LConv

theorem localConverseGL : GlobalTheory.Published.LocalConverseGL :=
  localConverseGL_of_leaves cuspGen kirBump bigCell extremeExists extremeIrred sepOfExtreme commBound unifOfComm
    altIdentity finiteOfAlt unitOfUnif glue


end DiscreteGroups.sglob.LConv
end
