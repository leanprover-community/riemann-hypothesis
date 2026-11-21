import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightFunctionalCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedModuleNontrivialStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIsoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairSplitTorus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedKFiniteRestriction

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qdet_apply_eq_prod_of_gelfVal : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ), GlRel E → (∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) → ∀ (Y : ℂ) (v : V), qdet E (Y + ((n : ℂ) - 1) / 2) v = (∏ s, (Y + χ s)) • v := by
  first | exact @GlobalTheory.CapelliNewton.capelli_of_gelfand | exact GlobalTheory.CapelliNewton.capelli_of_gelfand | (intros; apply GlobalTheory.CapelliNewton.capelli_of_gelfand <;> assumption)
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory

noncomputable def jointNullChain {V : Type} [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V)
    (S : Submodule ℂ V) : ℕ → Submodule ℂ V
  | 0 => S
  | m + 1 => jointNullChain T S m ⊓ LinearMap.ker (T m)

theorem exists_common_null_of_commute_locallyNilpotent :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V) (S : Submodule ℂ V),
      FiniteDimensional ℂ S → S ≠ ⊥ → (∀ k, ∀ v ∈ S, T k v ∈ S) →
      (∀ k l, Commute (T k) (T l)) → (∀ k, ∀ v ∈ S, ∃ N : ℕ, (T k ^ N) v = 0) →
      ∃ v ∈ S, v ≠ 0 ∧ ∀ k, T k v = 0 := by
  intro V _ _ T S hfin hne hstab hcomm hnil
  set Z := jointNullChain T S with hZ
  have hsucc : ∀ m, Z (m + 1) = Z m ⊓ LinearMap.ker (T m) := fun m => rfl
  have hanti : Antitone Z := antitone_nat_of_succ_le (fun m => by rw [hsucc]; exact inf_le_left)
  have hleS : ∀ m, Z m ≤ S := fun m => hanti (Nat.zero_le m)
  have hst : ∀ m l, ∀ v ∈ Z m, T l v ∈ Z m := by
    intro m
    induction m with
    | zero => exact fun l v hv => hstab l v hv
    | succ m ih =>
      intro l v hv
      rw [hsucc] at hv ⊢
      refine ⟨ih l v hv.1, ?_⟩
      have h0 : T m v = 0 := hv.2
      show T m (T l v) = 0
      have := LinearMap.congr_fun (hcomm m l).eq v
      simp only [Module.End.mul_apply] at this
      rw [this, h0, map_zero]
  have hstpow : ∀ m l i, ∀ v ∈ Z m, (T l ^ i) v ∈ Z m := by
    intro m l i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ i ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact hst m l _ (ih v hv)
  have hkill : ∀ m, ∀ k < m, ∀ v ∈ Z m, T k v = 0 := by
    intro m
    induction m with
    | zero => intro k hk; omega
    | succ m ih =>
      intro k hk v hv
      rw [hsucc] at hv
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact ih k hk v hv.1
      · subst hk; exact hv.2
  have hnebot : ∀ m, Z m ≠ ⊥ := by
    intro m
    induction m with
    | zero => exact hne
    | succ m ih =>
      obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp ih
      have hex : ∃ N : ℕ, (T m ^ N) w = 0 := hnil m w (hleS m hw)
      classical
      set N0 := Nat.find hex with hN0
      have hN0spec : (T m ^ N0) w = 0 := Nat.find_spec hex
      have hN0pos : N0 ≠ 0 := by
        intro h
        rw [h, pow_zero, Module.End.one_apply] at hN0spec
        exact hw0 hN0spec
      obtain ⟨i, hi⟩ : ∃ i, N0 = i + 1 := ⟨N0 - 1, by omega⟩
      have hne0 : (T m ^ i) w ≠ 0 := Nat.find_min hex (by omega)
      rw [Submodule.ne_bot_iff]
      refine ⟨(T m ^ i) w, ?_, hne0⟩
      rw [hsucc]
      refine ⟨hstpow m m i w hw, ?_⟩
      show T m ((T m ^ i) w) = 0
      rw [← Module.End.mul_apply, ← pow_succ', ← hi, hN0spec]
  have hfinZ : ∀ m, FiniteDimensional ℂ (Z m) := fun m => Submodule.finiteDimensional_of_le (hleS m)
  let f : ℕ → ℕ := fun m => Module.finrank ℂ (Z m)
  have hexc : ∃ c, ∃ m, f m = c := ⟨_, 0, rfl⟩
  classical
  obtain ⟨M, hM⟩ := Nat.find_spec hexc
  have hmin : ∀ m, Nat.find hexc ≤ f m := fun m => Nat.find_min' hexc ⟨m, rfl⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp (hnebot M)
  refine ⟨w, hleS M hw, hw0, fun k => ?_⟩
  rcases lt_or_ge k M with hk | hk
  · exact hkill M k hk w hw
  · have hle : Z (k + 1) ≤ Z M := hanti (by omega)
    have heq : Z (k + 1) = Z M := by
      haveI := hfinZ M
      apply Submodule.eq_of_le_of_finrank_eq hle
      have h1 := hmin (k + 1)
      have h2 : f (k + 1) ≤ f M := Submodule.finrank_mono hle
      have h3 : f M = Nat.find hexc := hM
      show f (k + 1) = f M
      omega
    exact hkill (k + 1) k (Nat.lt_succ_self k) w (heq ▸ hw)

end GlobalTheory
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.common_kernel_commuting_nilpotent : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V) (S : Submodule ℂ V), FiniteDimensional ℂ S → S ≠ ⊥ → (∀ k, ∀ v ∈ S, T k v ∈ S) → (∀ k l, Commute (T k) (T l)) → (∀ k, ∀ v ∈ S, ∃ N : ℕ, (T k ^ N) v = 0) → ∃ v ∈ S, v ≠ 0 ∧ ∀ k, T k v = 0 := by
  atlas_forward_decl GlobalTheory.exists_common_null_of_commute_locallyNilpotent
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.KFinStable

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def restr (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (T : Module.End ℂ (kFinVec ε ρ))
    (S : Submodule ℂ H) (hle : S ≤ kFinVec ε ρ) : S →ₗ[ℂ] H :=
  (kFinVec ε ρ).subtype ∘ₗ T ∘ₗ Submodule.inclusion hle

theorem range_restr (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (T : Module.End ℂ (kFinVec ε ρ))
    (hT : ∀ κ ∈ Kset ε, ∀ (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((T w : kFinVec ε ρ) : H) = ρ κ (T v : H))
    (Λ : Fin n → ℝ) (S : Submodule ℂ H) (hS : IsKTypeOf ε ρ Λ S) (hle : S ≤ kFinVec ε ρ) :
    LinearMap.range (restr ε ρ T S hle) = ⊥ ∨ IsKTypeOf ε ρ Λ (LinearMap.range (restr ε ρ T S hle)) := by
  obtain ⟨hfd, hK, hirr, ⟨v0, hv0S, hv0, hv0w⟩, hdom⟩ := hS
  set φ := restr ε ρ T S hle with hφ
  have hcomm : ∀ g (hg : g ∈ Kset ε) (x : S), φ ⟨ρ g x, hK g hg x x.2⟩ = ρ g (φ x) := by
    intro g hg x
    exact hT g hg ⟨x, hle x.2⟩ ⟨ρ g x, hle (hK g hg x x.2)⟩ rfl

  set Kr : Submodule ℂ H := (LinearMap.ker φ).map S.subtype with hKr
  have hKrS : Kr ≤ S := Submodule.map_subtype_le _ _
  have hKrK : IsKStableOn ε ρ Kr := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    refine Submodule.mem_map.2 ⟨⟨ρ g y, hK g hg y y.2⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker] at hy ⊢
    rw [hcomm g hg y, hy, map_zero]
  rcases hirr Kr hKrS hKrK with h0 | h1
  · right
    have hinj : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      have : (y : H) ∈ Kr := Submodule.mem_map.2 ⟨y, hy, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    refine ⟨LinearMap.finiteDimensional_range φ, ?_, ?_, ?_, ?_⟩
    · rintro g hg _ ⟨x, rfl⟩
      exact ⟨⟨ρ g x, hK g hg x x.2⟩, hcomm g hg x⟩
    · intro S'' hS''le hS''K
      set P : Submodule ℂ H := (S''.comap φ).map S.subtype with hP
      have hPS : P ≤ S := Submodule.map_subtype_le _ _
      have hPK : IsKStableOn ε ρ P := by
        intro g hg x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
        refine Submodule.mem_map.2 ⟨⟨ρ g y, hK g hg y y.2⟩, ?_, rfl⟩
        rw [Submodule.mem_comap] at hy ⊢
        rw [hcomm g hg y]
        exact hS''K g hg _ hy
      rcases hirr P hPS hPK with hP0 | hP1
      · left
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨z, rfl⟩ := hS''le hy
        have : (z : H) ∈ P := Submodule.mem_map.2 ⟨z, hy, rfl⟩
        rw [hP0, Submodule.mem_bot] at this
        have hz : z = 0 := Subtype.ext this
        rw [hz, map_zero]; exact Submodule.zero_mem _
      · right
        refine le_antisymm hS''le ?_
        rintro _ ⟨z, rfl⟩
        have : (z : H) ∈ P := by rw [hP1]; exact z.2
        obtain ⟨z', hz', hzz⟩ := Submodule.mem_map.1 this
        have : z' = z := Subtype.ext hzz
        rw [← this]; exact hz'
    · refine ⟨φ ⟨v0, hv0S⟩, ⟨_, rfl⟩, ?_, ?_⟩
      · intro h
        have := hinj (h.trans (map_zero φ).symm)
        exact hv0 (congrArg Subtype.val this)
      · intro θ hθ
        rw [← hcomm _ hθ, ← map_smul]
        congr 1
        exact Subtype.ext (hv0w θ hθ)
    · rintro μ _ ⟨x, rfl⟩ hy hw
      have hx : (x : H) ≠ 0 := by
        intro h
        apply hy
        rw [show x = 0 from Subtype.ext h, map_zero]
      refine hdom μ x x.2 hx ?_
      intro θ hθ
      have := hw θ hθ
      rw [← hcomm _ hθ, ← map_smul] at this
      exact congrArg Subtype.val (hinj this)
  · left
    rw [LinearMap.range_eq_bot]
    ext y
    have : (y : H) ∈ Kr := by rw [h1]; exact y.2
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 this
    have : z = y := Subtype.ext hzy
    rw [← this]
    simpa using hz

end GlobalTheory.KFinStable

noncomputable section

namespace GlobalTheory.KFinStable

variable {n : ℕ}

def kSub (ε : Fin n → Bool) : Subgroup (Matrix.unitaryGroup (Fin n) ℂ) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * g}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    show (a : Matrix (Fin n) (Fin n) ℂ) * b * Jm ε = Jm ε * (a * b)
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  one_mem' := by
    show ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * _
    simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    show star (a : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * star (a : Matrix (Fin n) (Fin n) ℂ)
    have h := congrArg star ha
    simp only [star_mul, Matrix.star_eq_conjTranspose, Jm_conjTranspose] at h
    simpa [Matrix.star_eq_conjTranspose] using h.symm

theorem mem_Kset (ε : Fin n → Bool) (g : kSub ε) : ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨(g : Matrix.unitaryGroup (Fin n) ℂ).2, g.2⟩

theorem mem_UJset (ε : Fin n → Bool) (g : kSub ε) :
    ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  show inUJ ε _
  have hu : star ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *
      ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (g : Matrix.unitaryGroup (Fin n) ℂ).2
  unfold inUJ
  rw [Matrix.mul_assoc, ← g.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu, Matrix.one_mul]

instance unitaryGroup_compactSpace' (m : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin m) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := ((Matrix.unitaryGroup (Fin m) ℂ : Submonoid _) :
      Set (Matrix (Fin m) (Fin m) ℂ))) hK isClosed_unitary ?_
  intro U hU
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU i j)

instance matrix_secondCountable' (m : ℕ) : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))

instance unitaryGroup_secondCountable' (m : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin m) ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance kSub_secondCountable (ε : Fin n → Bool) : SecondCountableTopology (kSub ε) :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance kSub_compactSpace (ε : Fin n → Bool) : CompactSpace (kSub ε) := by
  apply isCompact_iff_compactSpace.mp
  apply IsClosed.isCompact
  have : IsClosed {g : Matrix.unitaryGroup (Fin n) ℂ |
      (g : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * g} :=
    isClosed_eq ((continuous_subtype_val).mul continuous_const)
      (continuous_const.mul continuous_subtype_val)
  exact this

end GlobalTheory.KFinStable

noncomputable section

namespace GlobalTheory.KFinStable

def kRep {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) :
    kSub ε →* (H →L[ℂ] H) where
  toFun g := ρ ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  map_one' := h.1
  map_mul' a b := h.2 _ (mem_UJset ε a) _ (mem_UJset ε b)

theorem exists_finDim_stable : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ T : ℕ → Module.End ℂ (kFinVec ε ρ), (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((T k w : kFinVec ε ρ) : H) = ρ κ (T k v : H)) → ∃ S : Submodule ℂ (kFinVec ε ρ), FiniteDimensional ℂ S ∧ S ≠ ⊥ ∧ ∀ k, ∀ w ∈ S, T k w ∈ S := by
  intro n ε H _ _ _ _ ρ hA T hT
  obtain ⟨hrep, hcont, hnorm, hadm⟩ := hA

  obtain ⟨S₀, hS₀, hS₀fd, hS₀K⟩ := GlobalTheory.T.compact_unitary_finite_invariant_subspace (kSub ε) H (kRep ε ρ hrep)
    (fun k x => hnorm _ (mem_Kset ε k) x)
    (fun x => (hcont x).comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
      (fun k => mem_UJset ε k))
  have hS₀K' : IsKStableOn ε ρ S₀ := fun g hg v hv => hS₀K ⟨⟨g, hg.1⟩, hg.2⟩ v hv

  have hex : ∃ d, ∃ S : Submodule ℂ H, S ≠ ⊥ ∧ FiniteDimensional ℂ S ∧ IsKStableOn ε ρ S ∧
      Module.finrank ℂ S = d := ⟨_, S₀, hS₀, hS₀fd, hS₀K', rfl⟩
  classical
  obtain ⟨S₁, hS₁, hS₁fd, hS₁K, hS₁d⟩ := Nat.find_spec hex
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S₁ → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S₁ := by
    intro S' hle hK'
    by_cases h0 : S' = ⊥
    · exact Or.inl h0
    right
    by_contra hne
    have hlt : S' < S₁ := lt_of_le_of_ne hle hne
    haveI := Submodule.finiteDimensional_of_le hle
    have := Submodule.finrank_lt_finrank_of_lt hlt
    exact Nat.find_min hex (hS₁d ▸ this) ⟨S', h0, inferInstance, hK', rfl⟩
  obtain ⟨Λ, hΛ⟩ := (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H ρ hrep hcont hnorm).1 S₁ hS₁fd hS₁ hS₁K hirr

  set Sg : Submodule ℂ H := sSup {S' | S' ≤ ⊤ ∧ IsKTypeOf ε ρ Λ S'} with hSg
  haveI hSgfd : FiniteDimensional ℂ Sg := hadm Λ
  have hkt_le : ∀ S', IsKTypeOf ε ρ Λ S' → S' ≤ kFinVec ε ρ := fun S' h v hv => ⟨S', h.1, hv, h.2.1⟩
  have hSgle : Sg ≤ kFinVec ε ρ := sSup_le fun S' h => hkt_le S' h.2
  have hle_Sg : ∀ S', IsKTypeOf ε ρ Λ S' → S' ≤ Sg := fun S' h => le_sSup ⟨le_top, h⟩
  refine ⟨Sg.comap (kFinVec ε ρ).subtype, ?_, ?_, ?_⟩
  · exact LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSgle).symm
  · obtain ⟨v0, hv0, hv0ne, -⟩ := hΛ.2.2.2.1
    intro hbot
    have hmem : (⟨v0, hkt_le S₁ hΛ hv0⟩ : kFinVec ε ρ) ∈ Sg.comap (kFinVec ε ρ).subtype :=
      hle_Sg S₁ hΛ hv0
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv0ne (congrArg Subtype.val hmem)
  · intro k
    set N : Submodule ℂ H :=
      (Sg.comap ((kFinVec ε ρ).subtype ∘ₗ T k)).map (kFinVec ε ρ).subtype with hN
    have hSgN : Sg ≤ N := by
      refine sSup_le fun S' hS' => ?_
      intro x hx
      have hxk := hkt_le S' hS'.2 hx
      refine Submodule.mem_map.2 ⟨⟨x, hxk⟩, ?_, rfl⟩
      rw [Submodule.mem_comap]
      have hr : restr ε ρ (T k) S' (hkt_le S' hS'.2) ⟨x, hx⟩ ∈ Sg := by
        rcases range_restr ε ρ (T k) (fun κ hκ v w h => hT κ hκ k v w h) Λ S' hS'.2 (hkt_le S' hS'.2) with h0 | h1
        · have : restr ε ρ (T k) S' (hkt_le S' hS'.2) ⟨x, hx⟩ ∈
              LinearMap.range (restr ε ρ (T k) S' (hkt_le S' hS'.2)) := ⟨_, rfl⟩
          rw [h0, Submodule.mem_bot] at this
          rw [this]; exact Sg.zero_mem
        · exact hle_Sg _ h1 ⟨_, rfl⟩
      exact hr
    intro w hw
    rw [Submodule.mem_comap] at hw ⊢
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSgN hw)
    have : y = w := Subtype.ext hyw
    rw [← this]
    exact hy

end GlobalTheory.KFinStable
end
end
end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dimensional_invariant_subspace : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ T : ℕ → Module.End ℂ (kFinVec ε ρ), (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((T k w : kFinVec ε ρ) : H) = ρ κ (T k v : H)) → ∃ S : Submodule ℂ (kFinVec ε ρ), FiniteDimensional ℂ S ∧ S ≠ ⊥ ∧ ∀ k, ∀ w ∈ S, T k w ∈ S := by
  first | exact @GlobalTheory.KFinStable.exists_finDim_stable | exact GlobalTheory.KFinStable.exists_finDim_stable | (intros; apply GlobalTheory.KFinStable.exists_finDim_stable <;> assumption)
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.IsotropicPartner

open scoped ComplexOrder

def hf {n : ℕ} (d : Fin n → ℂ) (x y : Fin n → ℂ) : ℂ := ∑ i, star (x i) * d i * y i

lemma hf_symm {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, star (d i) = d i) (x y : Fin n → ℂ) :
    hf d y x = star (hf d x y) := by
  simp only [hf, star_sum, star_mul', star_star, hd]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma hf_sub {n : ℕ} (d : Fin n → ℂ) (x y u w : Fin n → ℂ) (a b : ℂ) :
    hf d x (fun i => y i - a * u i - b * w i) = hf d x y - a * hf d x u - b * hf d x w := by
  simp only [hf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_adapted_basis (n : ℕ) (ε : Fin n → Bool) (e : Fin n → ℂ) (he : e ≠ 0)
    (hiso : star e ⬝ᵥ (Jm ε *ᵥ e) = 0) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P ∧ p ≠ q ∧
      P *ᵥ Pi.single p 1 = e ∧ P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ e) ∧
      ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
        (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
  set d : Fin n → ℂ := fun a => if ε a then 1 else -1 with hd_def
  have hJ : Jm ε = diagonal d := rfl
  have hd : ∀ i, star (d i) = d i := by intro i; simp only [d]; split_ifs <;> simp
  have hd2 : ∀ i, d i * d i = 1 := by intro i; simp only [d]; split_ifs <;> norm_num
  set s : ℂ := ∑ i, star (e i) * e i with hs_def
  have hs : s ≠ 0 := by
    have := (dotProduct_star_self_eq_zero (v := e)).not.mpr he
    exact fun h0 => this h0
  set c : ℂ := s⁻¹ with hc_def
  set e' : Fin n → ℂ := fun i => c * (d i * e i) with he'_def
  have hee : hf d e e = 0 := by
    simpa [hJ, hf, dotProduct, mulVec_diagonal, mul_assoc] using hiso
  have hee' : hf d e e' = 1 := by
    have : hf d e e' = c * s := by
      simp only [hf, e', s, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by linear_combination (c * star (e i) * e i) * hd2 i
    rw [this, hc_def, inv_mul_cancel₀ hs]
  have he'e' : hf d e' e' = 0 := by
    have : hf d e' e' = star c * c * hf d e e := by
      simp only [hf, e', Finset.mul_sum, star_mul', hd]
      exact Finset.sum_congr rfl fun i _ => by
        linear_combination (star c * c * star (e i) * d i * e i) * hd2 i
    rw [this, hee, mul_zero]
  have he'e : hf d e' e = 1 := by rw [hf_symm d hd, hee', star_one]
  obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
    by_contra h; push_neg at h; exact he (funext h)
  set f : Fin n → ℂ := fun i => e' i - (e' p / e p) * e i with hf_def
  obtain ⟨q, hq⟩ : ∃ q, f q ≠ 0 := by
    by_contra h; push_neg at h
    have : hf d e e' = (e' p / e p) * hf d e e := by
      simp only [hf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := h i; simp only [f] at this
      linear_combination (star (e i) * d i) * this
    rw [hee', hee, mul_zero] at this; exact one_ne_zero this
  have hpq : p ≠ q := by
    rintro rfl; apply hq; simp only [f]; field_simp; ring
  let pr : (Fin n → ℂ) → (Fin n → ℂ) := fun y i => y i - hf d e' y * e i - hf d e y * e' i
  have hpre : ∀ y, hf d e (pr y) = 0 := by
    intro y; simp only [pr]; rw [hf_sub, hee, hee']; ring
  have hpre' : ∀ y, hf d e' (pr y) = 0 := by
    intro y; simp only [pr]; rw [hf_sub, he'e, he'e']; ring
  have hpre_l : ∀ y, hf d (pr y) e = 0 := by intro y; rw [hf_symm d hd, hpre, star_zero]
  have hpre'_l : ∀ y, hf d (pr y) e' = 0 := by intro y; rw [hf_symm d hd, hpre', star_zero]
  let col : Fin n → Fin n → ℂ := fun j => if j = p then e else if j = q then e' else pr (Pi.single j 1)
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => col j i
  have hPcol : ∀ j, P *ᵥ Pi.single j 1 = col j := by
    intro j; ext i; simp [P, mulVec_single_one]
  have hgram : ∀ a b, (Pᴴ * Jm ε * P) a b = hf d (col a) (col b) := by
    intro a b
    rw [hJ, Matrix.mul_apply]; simp only [Matrix.mul_diagonal]
    simp [hf, P, Matrix.conjTranspose_apply]
  have hcolp : col p = e := by simp [col]
  have hcolq : col q = e' := by simp [col, hpq.symm]
  have hcolr : ∀ r, r ≠ p → r ≠ q → col r = pr (Pi.single r 1) := by
    intro r h1 h2; simp [col, h1, h2]
  have hGram : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      hf d (col a) (col b) = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
    intro a b hab
    rcases eq_or_ne a p with rfl | hap
    · rcases eq_or_ne b a with rfl | hba
      · simp [hcolp, hee, hpq]
      rcases eq_or_ne b q with rfl | hbq
      · simp [hcolp, hcolq, hee']
      · simp [hcolp, hcolr b hba hbq, hpre, hba, hbq]
    rcases eq_or_ne a q with rfl | haq
    · rcases eq_or_ne b p with rfl | hbp
      · simp [hcolp, hcolq, he'e]
      rcases eq_or_ne b a with rfl | hbq
      · simp [hcolq, he'e', hap]
      · simp [hcolq, hcolr b hbp hbq, hpre', hbp, hbq]
    · rcases hab with h | h | rfl | rfl
      · exact absurd h hap
      · exact absurd h haq
      · simp [hcolp, hcolr a hap haq, hpre_l, hap, haq]
      · simp [hcolq, hcolr a hap haq, hpre'_l, hap, haq]
  have key : ∀ x v, hf d x (P *ᵥ v) = ∑ j, v j * hf d x (col j) := by
    intro x v
    simp only [hf, mulVec, dotProduct, P, of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hecol : ∀ j, hf d e (col j) = if j = q then 1 else 0 := by
    intro j
    rcases eq_or_ne j p with rfl | hjp
    · simp [hcolp, hee, hpq]
    rcases eq_or_ne j q with rfl | hjq
    · simp [hcolq, hee']
    · simp [hcolr j hjp hjq, hpre, hjq]
  have he'col : ∀ j, hf d e' (col j) = if j = p then 1 else 0 := by
    intro j
    rcases eq_or_ne j p with rfl | hjp
    · simp [hcolp, he'e]
    rcases eq_or_ne j q with rfl | hjq
    · simp [hcolq, he'e', hjp]
    · simp [hcolr j hjp hjq, hpre', hjp]
  have hsingle : ∀ x j, hf d x (Pi.single j 1) = star (x j) * d j := by
    intro x j; simp [hf, Pi.single_apply]
  have h0 : ∀ x, hf d x 0 = 0 := by intro x; simp [hf]
  have hker : ∀ v, P *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hvq : v q = 0 := by
      have := key e v
      rw [hv, h0] at this
      simp only [hecol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    have hvp : v p = 0 := by
      have := key e' v
      rw [hv, h0] at this
      simp only [he'col, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    have hPv : P *ᵥ v = pr v := by
      ext i
      have hterm : ∀ j, col j i * v j = pr (Pi.single j 1) i * v j := by
        intro j
        rcases eq_or_ne j p with rfl | hjp
        · simp [hvp]
        rcases eq_or_ne j q with rfl | hjq
        · simp [hvq]
        rw [hcolr j hjp hjq]
      simp only [mulVec, dotProduct, P, of_apply]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      simp only [pr, hsingle]
      have h1 : ∑ j, (Pi.single j (1:ℂ) : Fin n → ℂ) i * v j = v i := by simp [Pi.single_apply]
      simp only [sub_mul, Finset.sum_sub_distrib, h1]
      rw [sub_sub, sub_sub]
      congr 1
      simp only [hf, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hPv] at hv
    have hvi : ∀ i, v i = hf d e' v * e i + hf d e v * e' i := by
      intro i; have := congrFun hv i; simp only [pr, Pi.zero_apply] at this
      linear_combination this
    have hp0 : hf d e' v * e p + hf d e v * e' p = 0 := by rw [← hvi p, hvp]
    have hq0 : hf d e' v * e q + hf d e v * e' q = 0 := by rw [← hvi q, hvq]
    have hβ : hf d e v = 0 := by
      have : hf d e v * f q = 0 := by
        simp only [f]; field_simp; linear_combination e p * hq0 - e q * hp0
      exact (mul_eq_zero.mp this).resolve_right hq
    have hα : hf d e' v = 0 := by
      rw [hβ, zero_mul, add_zero] at hp0; exact (mul_eq_zero.mp hp0).resolve_right hp
    ext i; rw [hvi, hα, hβ]; simp
  have hunit : IsUnit P := by
    refine (Matrix.mulVec_injective_iff_isUnit).mp fun v w h => ?_
    have := hker (v - w) (by rw [Matrix.mulVec_sub, h, sub_self])
    exact sub_eq_zero.mp this
  refine ⟨P, p, q, c, hunit, hpq, by rw [hPcol, hcolp], ?_, fun a b hab => by rw [hgram]; exact hGram a b hab⟩
  rw [hPcol, hcolq]; ext i; simp [e', hJ, mulVec_diagonal]

end GlobalTheory.IsotropicPartner
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_change_of_basis : ∀ (n : ℕ) (ε : Fin n → Bool) (e : Fin n → ℂ), e ≠ 0 → star e ⬝ᵥ (Jm ε *ᵥ e) = 0 → ∃ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P ∧ p ≠ q ∧ P *ᵥ Pi.single p 1 = e ∧ P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ e) ∧ ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
  atlas_forward_decl GlobalTheory.IsotropicPartner.exists_adapted_basis
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.UnipRadUnit

variable {n : ℕ}

def RadCond (ε : Fin n → Bool) (e : Fin n → ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Y *ᵥ e = 0 ∧ (∀ y, star e ⬝ᵥ (Jm ε *ᵥ y) = 0 → ∃ c : ℂ, Y *ᵥ y = c • e) ∧
    ∀ y, star e ⬝ᵥ (Jm ε *ᵥ (Y *ᵥ y)) = 0

theorem RadCond.add {ε : Fin n → Bool} {e : Fin n → ℂ} {Y Y' : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (h' : RadCond ε e Y') : RadCond ε e (Y + Y') := by
  refine ⟨by rw [add_mulVec, h.1, h'.1, add_zero], fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨c, hc⟩ := h.2.1 y hy
    obtain ⟨c', hc'⟩ := h'.2.1 y hy
    exact ⟨c + c', by rw [add_mulVec, hc, hc', add_smul]⟩
  · rw [add_mulVec, mulVec_add, dotProduct_add, h.2.2, h'.2.2, add_zero]

theorem RadCond.smul {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (s : ℂ) : RadCond ε e (s • Y) := by
  refine ⟨by rw [Matrix.smul_mulVec, h.1, smul_zero], fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨c, hc⟩ := h.2.1 y hy
    exact ⟨s * c, by rw [Matrix.smul_mulVec, hc, smul_smul]⟩
  · rw [Matrix.smul_mulVec, mulVec_smul, dotProduct_smul, h.2.2, smul_zero]

theorem RadCond.neg {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) : RadCond ε e (-Y) := by
  simpa using h.smul (-1)

theorem RadCond.sub {ε : Fin n → Bool} {e : Fin n → ℂ} {Y Y' : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (h' : RadCond ε e Y') : RadCond ε e (Y - Y') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem RadCond.pow_three {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) : Y ^ 3 = 0 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  obtain ⟨c, hc⟩ := h.2.1 (Y *ᵥ Pi.single i 1) (h.2.2 _)
  rw [zero_mulVec, pow_succ, pow_two, ← mulVec_mulVec, ← mulVec_mulVec, hc, mulVec_smul, h.1, smul_zero]

theorem RadCond.exp_mulVec {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (y : Fin n → ℂ) (hy : star e ⬝ᵥ (Jm ε *ᵥ y) = 0) :
    NormedSpace.exp Y *ᵥ y = y + Y *ᵥ y := by
  have h3 := h.pow_three
  have hexp : NormedSpace.exp Y = ∑ k ∈ Finset.range 3, ((k.factorial : ℂ)⁻¹) • Y ^ k := by
    rw [NormedSpace.exp_eq_tsum ℂ]
    refine tsum_eq_sum fun k hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    rw [← Nat.add_sub_cancel' hk, pow_add, h3, zero_mul, smul_zero]
  obtain ⟨c, hc⟩ := h.2.1 y hy
  have h2 : Y *ᵥ (Y *ᵥ y) = 0 := by rw [hc, mulVec_smul, h.1, smul_zero]
  rw [hexp]
  simp [Finset.sum_range_succ, add_mulVec, Matrix.smul_mulVec, pow_two, ← mulVec_mulVec, h2]

theorem expG_mem_flagN {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : 0 < a) (hW : IsIsoFlag ε j W) (hj : j ⟨0, h⟩ = 1)
    {e : Fin n → ℂ} (he : e ∈ W ⟨1, Nat.succ_lt_succ h⟩) (he0 : e ≠ 0)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ lieSet ε) (hR : RadCond ε e Y) (t : ℝ) :
    expG ε Y t ∈ flagN ε W := by
  obtain ⟨hW0, hmono, hrank, hiso⟩ := hW
  have hrank1 : Module.finrank ℂ (W ⟨1, Nat.succ_lt_succ h⟩) = 1 := by
    have h1 := hrank ⟨0, h⟩
    have hc : (⟨0, h⟩ : Fin a).castSucc = 0 := Fin.ext rfl
    rw [hc, hW0, finrank_bot, hj, zero_add] at h1
    exact h1
  have hspan : ∀ y ∈ W ⟨1, Nat.succ_lt_succ h⟩, ∃ d : ℂ, y = d • e := by
    intro y hy
    have he0' : (⟨e, he⟩ : W ⟨1, Nat.succ_lt_succ h⟩) ≠ 0 := fun h0 => he0 (congrArg Subtype.val h0)
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp hrank1 ⟨y, hy⟩
    exact ⟨d, (congrArg Subtype.val hd).symm⟩
  have hlast : W ⟨1, Nat.succ_lt_succ h⟩ ≤ W (Fin.last a) := hmono (Fin.le_last _)
  have hperp : ∀ y ∈ W (Fin.last a), star e ⬝ᵥ (Jm ε *ᵥ y) = 0 := fun y hy => hiso e (hlast he) y hy
  have hRZ := hR.smul (t : ℂ)
  have hexp : uMat (expG ε Y t) = NormedSpace.exp ((t : ℂ) • Y) := toM_expG ε Y t hY
  have key : ∀ y, star e ⬝ᵥ (Jm ε *ᵥ y) = 0 → ∃ c : ℂ, uMat (expG ε Y t) *ᵥ y - y = c • e := by
    intro y hy
    rw [hexp, hRZ.exp_mulVec y hy, add_sub_cancel_left]
    exact hRZ.2.1 y hy
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · have hy' := hperp y (hmono (Fin.le_last _) hy)
    rcases Nat.eq_zero_or_pos i.val with hi | hi
    · have hi' : i.succ = ⟨1, Nat.succ_lt_succ h⟩ := Fin.ext (by simp [hi])
      rw [hi'] at hy
      obtain ⟨d, rfl⟩ := hspan y hy
      rw [hexp, hRZ.exp_mulVec _ hy', add_sub_cancel_left, mulVec_smul, hRZ.1, smul_zero]
      exact zero_mem _
    · obtain ⟨c, hc⟩ := key y hy'
      rw [hc]
      have hle : (⟨1, Nat.succ_lt_succ h⟩ : Fin (a + 1)) ≤ i.castSucc := by
        rw [Fin.le_def]; simp; omega
      exact hmono hle (Submodule.smul_mem _ c he)
  · obtain ⟨c, hc⟩ := key y (hy e (hlast he))
    rw [hc]
    exact hlast (Submodule.smul_mem _ c he)

def theta (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Jm ε * Zᴴ * Jm ε)

theorem Jm_Jm_mul (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem re_mem (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (2⁻¹ : ℂ) • (Z + theta ε Z) ∈ lieSet ε := by
  show ((2⁻¹ : ℂ) • (Z + theta ε Z))ᴴ * Jm ε + Jm ε * ((2⁻¹ : ℂ) • (Z + theta ε Z)) = 0
  simp only [theta, conjTranspose_smul, conjTranspose_add, conjTranspose_neg, conjTranspose_mul,
    Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Jm_Jm_mul]
  simp

theorem im_mem (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Complex.I / 2) • (theta ε Z - Z) ∈ lieSet ε := by
  show ((Complex.I / 2) • (theta ε Z - Z))ᴴ * Jm ε + Jm ε * ((Complex.I / 2) • (theta ε Z - Z)) = 0
  simp only [theta, conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, conjTranspose_mul,
    Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Jm_Jm_mul]
  simp
  module

theorem decomp {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : 0 < a) (hW : IsIsoFlag ε j W) (hj : j ⟨0, h⟩ = 1)
    {e : Fin n → ℂ} (he : e ∈ W ⟨1, Nat.succ_lt_succ h⟩) (he0 : e ≠ 0)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : RadCond ε e Z) (hθ : RadCond ε e (theta ε Z)) :
    ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧
      (∀ t, expG ε X' t ∈ flagN ε W) ∧ Z = X + Complex.I • X' := by
  refine ⟨(2⁻¹ : ℂ) • (Z + theta ε Z), (Complex.I / 2) • (theta ε Z - Z), re_mem ε Z, im_mem ε Z,
    expG_mem_flagN h hW hj he he0 (re_mem ε Z) ((hZ.add hθ).smul _),
    expG_mem_flagN h hW hj he he0 (im_mem ε Z) ((hθ.sub hZ).smul _), ?_⟩
  rw [smul_smul, show Complex.I * (Complex.I / 2) = -2⁻¹ by rw [← mul_div_assoc, Complex.I_mul_I]; ring]
  module

theorem vecMulVec_mulVec' (x φ y : Fin n → ℂ) : vecMulVec x φ *ᵥ y = (φ ⬝ᵥ y) • x := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

theorem theta_vecMulVec (ε : Fin n → Bool) (x φ : Fin n → ℂ) :
    theta ε (vecMulVec x φ) = -vecMulVec (Jm ε *ᵥ star φ) (star x ᵥ* Jm ε) := by
  rw [theta, conjTranspose_vecMulVec, mul_vecMulVec, vecMulVec_mul]

theorem radCond_col {ε : Fin n → Bool} {e : Fin n → ℂ} (hfe : star e ⬝ᵥ (Jm ε *ᵥ e) = 0)
    (φ : Fin n → ℂ) (hφ : φ ⬝ᵥ e = 0) : RadCond ε e (vecMulVec e φ) := by
  refine ⟨by rw [vecMulVec_mulVec', hφ, zero_smul], fun y _ => ⟨φ ⬝ᵥ y, vecMulVec_mulVec' _ _ _⟩,
    fun y => ?_⟩
  rw [vecMulVec_mulVec', mulVec_smul, dotProduct_smul, hfe, smul_zero]

theorem radCond_row {ε : Fin n → Bool} {e : Fin n → ℂ} (hfe : star e ⬝ᵥ (Jm ε *ᵥ e) = 0)
    (x : Fin n → ℂ) (hx : star e ⬝ᵥ (Jm ε *ᵥ x) = 0) :
    RadCond ε e (vecMulVec x (star e ᵥ* Jm ε)) := by
  refine ⟨by rw [vecMulVec_mulVec', ← dotProduct_mulVec, hfe, zero_smul], fun y hy => ⟨0, ?_⟩, fun y => ?_⟩
  · rw [vecMulVec_mulVec', ← dotProduct_mulVec, hy, zero_smul, zero_smul]
  · rw [vecMulVec_mulVec', mulVec_smul, dotProduct_smul, hx, smul_zero]

theorem single_eq_vecMulVec (p b : Fin n) :
    Matrix.single p b (1 : ℂ) = vecMulVec (Pi.single p 1) (Pi.single b 1) := by
  ext i k
  rcases eq_or_ne p i with rfl | hi
  · rcases eq_or_ne b k with rfl | hk
    · simp [vecMulVec_apply, Matrix.single_apply]
    · simp [vecMulVec_apply, Matrix.single_apply, hk, hk.symm]
  · simp [vecMulVec_apply, Matrix.single_apply, hi, hi.symm]

theorem matrixUnits_mem_radical : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a) (h : 0 < a), IsIsoFlag ε j W → j ⟨0, h⟩ = 1 → ∀ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P → p ≠ q → P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩ → P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) → (∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) → (∀ b, b ≠ p → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single p b 1 * P⁻¹ = X + Complex.I • X') ∧ ∀ b, b ≠ q → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single b q 1 * P⁻¹ = X + Complex.I • X' := by
  intro n ε a j W h hW hj P p q c hP hpq hp hq hG
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  set e := P *ᵥ Pi.single p 1 with he_def
  have hPe : P⁻¹ *ᵥ e = Pi.single p 1 := by rw [he_def, mulVec_mulVec, hPP, one_mulVec]
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := congrFun hPe p
    rw [h0, mulVec_zero] at h1
    simp at h1
  have hGp : ∀ k, (Pᴴ * Jm ε * P) p k = if k = q then 1 else 0 := by
    intro k
    rw [hG p k (Or.inl rfl)]
    by_cases hk : k = q <;> simp [hk, hpq]
  have hf : ∀ y, star e ⬝ᵥ (Jm ε *ᵥ y) = (P⁻¹ *ᵥ y) q := by
    intro y
    have hy : y = P *ᵥ (P⁻¹ *ᵥ y) := by rw [mulVec_mulVec, hPP', one_mulVec]
    conv_lhs => rw [hy]
    rw [he_def, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
    generalize P⁻¹ *ᵥ y = v
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hGp]
  have hfe : star e ⬝ᵥ (Jm ε *ᵥ e) = 0 := by
    rw [hf, hPe]; simp [hpq.symm]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have hZ : P * Matrix.single p b 1 * P⁻¹ = vecMulVec e (Pi.single b 1 ᵥ* P⁻¹) := by
      rw [single_eq_vecMulVec, mul_vecMulVec, vecMulVec_mul]
    have hre : (Pi.single b 1 ᵥ* P⁻¹) ⬝ᵥ e = 0 := by
      rw [← dotProduct_mulVec, hPe]; simp [hb]
    have h1 := radCond_col hfe _ hre
    have h2 : RadCond ε e (theta ε (vecMulVec e (Pi.single b 1 ᵥ* P⁻¹))) := by
      rw [theta_vecMulVec]
      refine (radCond_row hfe _ ?_).neg
      rw [mulVec_mulVec, Jm_mul_self, one_mulVec, star_dotProduct, star_star, hre, star_zero]
    rw [hZ]
    exact decomp h hW hj hp he0 h1 h2
  · have hZ : P * Matrix.single b q 1 * P⁻¹ = vecMulVec (P *ᵥ Pi.single b 1) (Pi.single q 1 ᵥ* P⁻¹) := by
      rw [single_eq_vecMulVec, mul_vecMulVec, vecMulVec_mul]
    have hs : Pi.single q 1 ᵥ* P⁻¹ = star e ᵥ* Jm ε := by
      funext k
      have h1 := hf (Pi.single k 1)
      rw [dotProduct_mulVec] at h1
      simpa [Matrix.mulVec, Matrix.vecMul, dotProduct, Pi.single_apply] using h1.symm
    have hv : star e ⬝ᵥ (Jm ε *ᵥ (P *ᵥ Pi.single b 1)) = 0 := by
      rw [hf, mulVec_mulVec, hPP, one_mulVec]; simp [hb]
    have h1 := radCond_row hfe _ hv
    have h2 : RadCond ε e (theta ε (vecMulVec (P *ᵥ Pi.single b 1) (star e ᵥ* Jm ε))) := by
      rw [theta_vecMulVec, star_vecMul, Jm_conjTranspose, star_star, mulVec_mulVec, Jm_mul_self, one_mulVec]
      refine (radCond_col hfe _ ?_).neg
      rw [← dotProduct_mulVec, star_dotProduct, star_mulVec, Jm_conjTranspose, ← dotProduct_mulVec, hv,
        star_zero]
    rw [hZ, hs]
    exact decomp h hW hj hp he0 h1 h2

end GlobalTheory.UnipRadUnit
end
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_in_first_flag_space : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a) (h : 0 < a), IsIsoFlag ε j W → j ⟨0, h⟩ = 1 → ∀ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P → p ≠ q → P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩ → P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) → (∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) → (∀ b, b ≠ p → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single p b 1 * P⁻¹ = X + Complex.I • X') ∧ ∀ b, b ≠ q → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single b q 1 * P⁻¹ = X + Complex.I • X' := by
  atlas_forward_decl GlobalTheory.UnipRadUnit.matrixUnits_mem_radical
end

section
section
open scoped InnerProductSpace

namespace GlobalTheory

open Module.End in

theorem exists_common_eigenvector_inner_ne_zero_of_commute_isometry
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (U : Submodule ℂ V)
    (hfin : FiniteDimensional ℂ U) {ι : Type} (A : ι → V →L[ℂ] V) (x₀ : V)
    (hx₀ : x₀ ∈ U) (hne : x₀ ≠ 0) (hU : ∀ i, ∀ x ∈ U, A i x ∈ U)
    (hiso : ∀ i x, ‖A i x‖ = ‖x‖) (hcomm : ∀ i l x, A i (A l x) = A l (A i x)) :
    ∃ v ∈ U, ⟪v, x₀⟫_ℂ ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i v = c • v := by
  classical
  let B : ι → Module.End ℂ U := fun i => (A i).toLinearMap.restrict (hU i)
  have hBapp : ∀ i (x : U), ((B i x : U) : V) = A i x := fun i x => rfl
  have hinner : ∀ i (x y : U), ⟪B i x, B i y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro i x y
    let L : U →ₗᵢ[ℂ] U := { toLinearMap := B i, norm_map' := fun x => hiso i x }
    exact L.inner_map_map x y
  let D : ι → Module.End ℂ U := fun i => LinearMap.adjoint (B i)
  have hDB : ∀ i, D i * B i = 1 := by
    intro i
    apply LinearMap.ext; intro x
    apply ext_inner_left ℂ; intro y
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_right, hinner]
    rfl
  have hBD : ∀ i, B i * D i = 1 := fun i => mul_eq_one_comm.mp (hDB i)
  let u : ι → (Module.End ℂ U)ˣ := fun i => ⟨B i, D i, hBD i, hDB i⟩
  have hBB : ∀ i l, Commute (B i) (B l) := by
    intro i l
    apply LinearMap.ext; intro x
    apply Subtype.ext
    exact hcomm i l x
  have hDBc : ∀ i l, Commute (D i) (B l) := fun i l =>
    Commute.units_inv_left (u := u i) (hBB i l)
  have hDD : ∀ i l, Commute (D i) (D l) := fun i l =>
    Commute.units_inv_left (u := u i) (hDBc l i).symm
  let T : ι ⊕ ι → Module.End ℂ U :=
    Sum.elim (fun i => B i + D i) (fun i => Complex.I • (B i - D i))
  have hTB : ∀ a k, Commute (T a) (B k) := by
    rintro (i|i) k
    · exact (hBB i k).add_left (hDBc i k)
    · exact ((hBB i k).sub_left (hDBc i k)).smul_left _
  have hTD : ∀ a k, Commute (T a) (D k) := by
    rintro (i|i) k
    · exact (hDBc k i).symm.add_left (hDD i k)
    · exact ((hDBc k i).symm.sub_left (hDD i k)).smul_left _
  have hTT : ∀ a b, Commute (T a) (T b) := by
    intro a b
    rcases b with i|i
    · exact (hTB a i).add_right (hTD a i)
    · exact ((hTB a i).sub_right (hTD a i)).smul_right _
  have hTsym : ∀ a, (T a).IsSymmetric := by
    rintro (i|i) x y
    · simp only [T, D, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right,
        LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
      ring
    · simp only [T, D, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left,
        inner_smul_right, inner_sub_left, inner_sub_right,
        LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, Complex.conj_I]
      ring
  have hsup := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTsym (fun a b _ => hTT a b)
  have key : ∃ χ : ι ⊕ ι → ℂ, ∃ w ∈ ⨅ a, eigenspace (T a) (χ a), ⟪(w : V), x₀⟫_ℂ ≠ 0 := by
    by_contra h
    push_neg at h
    let x : U := ⟨x₀, hx₀⟩
    have hle : (⨆ χ : ι ⊕ ι → ℂ, ⨅ a, eigenspace (T a) (χ a)) ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      refine iSup_le fun χ w hw => ?_
      rw [LinearMap.mem_ker, innerₛₗ_apply_apply, Submodule.coe_inner, ← inner_conj_symm, h χ w hw]
      simp
    rw [hsup] at hle
    have hx : x ∈ LinearMap.ker (innerₛₗ ℂ x) := hle Submodule.mem_top
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at hx
    exact hne (congrArg Subtype.val hx)
  obtain ⟨χ, w, hw, hwx⟩ := key
  refine ⟨w, w.2, hwx, fun i => ⟨(χ (Sum.inl i) - Complex.I * χ (Sum.inr i)) / 2, ?_⟩⟩
  rw [Submodule.mem_iInf] at hw
  have h1 : B i w + D i w = χ (Sum.inl i) • w := by
    have := hw (Sum.inl i)
    rw [mem_eigenspace_iff] at this
    simpa [T] using this
  have h2 : Complex.I • (B i w - D i w) = χ (Sum.inr i) • w := by
    have := hw (Sum.inr i)
    rw [mem_eigenspace_iff] at this
    simpa [T] using this
  have h3 : B i w = ((χ (Sum.inl i) - Complex.I * χ (Sum.inr i)) / 2) • w := by
    have h2' : (B i w - D i w) = (-Complex.I * χ (Sum.inr i)) • w := by
      have := congrArg (fun z : U => (-Complex.I) • z) h2
      simp only [smul_smul] at this
      rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul] at this
      exact this
    linear_combination (norm := module) (1/2 : ℂ) • h1 + (1/2 : ℂ) • h2'
  have := congrArg Subtype.val h3
  exact this

end GlobalTheory
end

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_isometries_common_eigenvector : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (U : Submodule ℂ V), FiniteDimensional ℂ U → ∀ {ι : Type} (A : ι → V →L[ℂ] V) (x₀ : V), x₀ ∈ U → x₀ ≠ 0 → (∀ i, ∀ x ∈ U, A i x ∈ U) → (∀ i x, ‖A i x‖ = ‖x‖) → (∀ i l x, A i (A l x) = A l (A i x)) → ∃ v ∈ U, ⟪v, x₀⟫_ℂ ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i v = c • v := by
  atlas_forward_decl GlobalTheory.exists_common_eigenvector_inner_ne_zero_of_commute_isometry
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.IndFunctional

theorem exists_factor {A H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup H] [Module ℂ H]
    (ι : A →ₗ[ℂ] H) (L : A →ₗ[ℂ] ℂ) (hL : ∀ a, ι a = 0 → L a = 0) :
    ∃ ℓ : H →ₗ[ℂ] ℂ, ∀ a, ℓ (ι a) = L a := by
  have hle : LinearMap.ker ι ≤ LinearMap.ker L := fun a ha => hL a ha
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend
    (((LinearMap.ker ι).liftQ L hle).comp ι.quotKerEquivRange.symm.toLinearMap)
  refine ⟨ℓ, fun a => ?_⟩
  have := LinearMap.congr_fun hℓ ⟨ι a, LinearMap.mem_range_self ι a⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image] at this
  rw [this]
  rfl

theorem apply_one_eq_zero {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (f : I.fns) (hf : I.ι f = 0) :
    f.1 1 = 0 := by
  have hc : Continuous f.1 := (mem_indFun_top.1 f.2).1
  have hck : Continuous fun k : KG ε => ‖f.1 k‖ ^ 2 := (hc.comp continuous_subtype_val).norm.pow 2
  have hint : Integrable (fun k : KG ε => ‖f.1 k‖ ^ 2) (muK ε) :=
    hck.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : ∫ k : KG ε, ‖f.1 k‖ ^ 2 ∂muK ε = 0 := by
    rw [← I.model.norm_sq f, hf, norm_zero]; norm_num
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) hint).1 h0
  have heq : (fun k : KG ε => ‖f.1 k‖ ^ 2) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hck continuous_const).1 hae
  have := congrFun heq ⟨1, (KG ε).one_mem⟩
  simpa using this

theorem functional : GlobalTheory.Published.Langlands.Induced → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ H₀ T : Matrix (Fin n) (Fin n) ℂ, H₀ ∈ lieSet ε → T ∈ lieSet ε → (∀ x : ℝ, IsSplit ε I.W (Pi.single ⟨0, h⟩ x) (expG ε H₀ x)) → (∀ θ : ℝ, expG ε T θ ∈ KG ε ⊓ I.M ∧ ∀ m ∈ I.M, expG ε T θ * m = m * expG ε T θ) → ∀ Y : Submodule ℂ I.H, Y ≤ kFinVec ε I.ρ → Y ≠ ⊥ → IsKStableOn ε I.ρ Y → ∃ (ℓ : I.H →ₗ[ℂ] ℂ) (γ : ℂ), (∃ y ∈ Y, ℓ y ≠ 0) ∧ (∀ X ∈ lieSet ε, (∀ t, expG ε X t ∈ flagN ε I.W) → ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ X w) = 0) ∧ (∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ H₀ w) = (I.s ⟨0, h⟩ + n - 1) * ℓ w) ∧ ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ T w) = γ * ℓ w := by
  intro hInd n ε I h hj H₀ T hH₀ hT hsp hTθ Y hYk hY0 hYs
  obtain ⟨-, -, -, hkf, hder, -⟩ := hInd n ε I
  obtain ⟨hσ, -⟩ := I.temp.2.2
  have huM1 : uMat (1 : UJ ε) = 1 := rfl
  have hσ1 : I.σ 1 = 1 := hσ.1.1
  have hσmul : ∀ a ∈ I.M, ∀ b ∈ I.M, I.σ (uMat (a * b)) = (I.σ (uMat a)).comp (I.σ (uMat b)) :=
    fun a ha b hb => hσ.1.2 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hσiso : ∀ m ∈ I.M, ∀ x, ‖I.σ (uMat m) x‖ = ‖x‖ := fun m hm x => hσ.2.1 _ ⟨m, hm, rfl⟩ x
  have hinner : ∀ m ∈ I.M, ∀ a b, ⟪I.σ (uMat m) a, I.σ (uMat m) b⟫_ℂ = ⟪a, b⟫_ℂ := fun m hm a b =>
    (⟨(I.σ (uMat m)).toLinearMap, hσiso m hm⟩ : I.V →ₗᵢ[ℂ] I.V).inner_map_map a b
  have hN1 : (1 : UJ ε) ∈ flagN ε I.W := ⟨fun i y _ => by simp [huM1], fun y _ => by simp [huM1]⟩
  have law : ∀ f : I.fns, ∀ u ∈ flagN ε I.W, ∀ m ∈ I.M, ∀ x t, IsSplit ε I.W x t →
      f.1 (u * m * t) = Complex.exp (pairing I.j (I.s + rho n I.j) x) • I.σ (uMat m) (f.1 1) := by
    intro f u hu m hm x t ht
    simpa using (mem_indFun_top.1 f.2).2 u hu m hm x t ht 1
  have law0 : ∀ f : I.fns, ∀ u ∈ flagN ε I.W, ∀ m ∈ I.M, f.1 (u * m) = I.σ (uMat m) (f.1 1) := by
    intro f u hu m hm
    simpa [pairing] using law f u hu m hm 0 1 isSplit_one
  have kf : ∀ w ∈ kFinVec ε I.ρ, ∃ f : I.fns, IsKFinFun f.1 ∧ I.ι f = w := fun w hw => (hkf w).1 hw
  have dat1 : ∀ X ∈ lieSet ε, ∀ w ∈ kFinVec ε I.ρ, ∃ f f' : I.fns, I.ι f = w ∧ I.ι f' = dRep I.ρ X w ∧
      HasDerivAt (fun t : ℝ => f.1 (expG ε X t)) (f'.1 1) 0 := by
    intro X hX w hw
    obtain ⟨f, hfk, rfl⟩ := kf w hw
    obtain ⟨f', hd, he⟩ := hder f hfk X hX
    exact ⟨f, f', rfl, he.symm, by simpa using hd 1⟩

  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  obtain ⟨f, hfk, rfl⟩ := kf y (hYk hyY)
  have hf0 : f.1 ≠ 0 := fun e => hy0 (by rw [show f = 0 from Subtype.ext e, map_zero])
  obtain ⟨k₀, hk₀, hfk₀⟩ := (GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum f.1 f.2 hfk).2.2 hf0
  let f₁ : I.fns := ⟨fun g => f.1 (g * k₀), indFun_mul_right f.2 trivial⟩
  have hf₁k : IsKFinFun f₁.1 := by
    have hle : Submodule.span ℂ {φ : UJ ε → I.V | ∃ k ∈ KG ε, φ = fun g => f₁.1 (g * k)} ≤
        Submodule.span ℂ {φ : UJ ε → I.V | ∃ k ∈ KG ε, φ = fun g => f.1 (g * k)} := by
      refine Submodule.span_mono ?_
      rintro φ ⟨k, hk, rfl⟩
      exact ⟨k * k₀, mul_mem hk hk₀, by funext g; simp [f₁, mul_assoc]⟩
    haveI : FiniteDimensional ℂ (Submodule.span ℂ {φ : UJ ε → I.V | ∃ k ∈ KG ε, φ = fun g => f.1 (g * k)}) := hfk
    exact Submodule.finiteDimensional_of_le hle
  have hy₁ : I.ρ (uMat k₀) (I.ι f) = I.ι f₁ := I.model.transl k₀ trivial f f₁ fun g => rfl
  have hy₁Y : I.ι f₁ ∈ Y := hy₁ ▸ hYs (uMat k₀) hk₀ _ hyY
  have hx₀ : f₁.1 1 ≠ 0 := by simpa [f₁] using hfk₀
  obtain ⟨U, hUfd, hx₀U, hUst⟩ := (GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum f₁.1 f₁.2 hf₁k).2.1

  have hum : ∀ θ, (expG ε T θ)⁻¹ ∈ KG ε ⊓ I.M := fun θ => inv_mem (hTθ θ).1
  obtain ⟨v, -, hvx, hv⟩ := GlobalTheory.T.commuting_isometries_common_eigenvector U hUfd (fun θ => I.σ (uMat (expG ε T θ)⁻¹)) (f₁.1 1) hx₀U hx₀
    (fun θ x hx => hUst _ (hum θ) x hx) (fun θ x => hσiso _ (hum θ).2 x) (fun θ θ' x => by
      rw [← ContinuousLinearMap.comp_apply, ← hσmul _ (hum θ).2 _ (hum θ').2, ← ContinuousLinearMap.comp_apply,
        ← hσmul _ (hum θ').2 _ (hum θ).2, (Commute.inv_left ((hTθ θ).2 _ (hum θ').2)).eq])
  choose c hc using hv
  have key : ∀ θ x, ⟪v, I.σ (uMat (expG ε T θ)) x⟫_ℂ = starRingEnd ℂ (c θ) * ⟪v, x⟫_ℂ := by
    intro θ x
    have h1 : I.σ (uMat (expG ε T θ)⁻¹) (I.σ (uMat (expG ε T θ)) x) = x := by
      rw [← ContinuousLinearMap.comp_apply, ← hσmul _ (hum θ).2 _ (hTθ θ).1.2, inv_mul_cancel, huM1, hσ1]
      rfl
    rw [← hinner _ (hum θ).2, h1, hc θ, inner_smul_left]

  obtain ⟨ℓ, hℓ⟩ := exists_factor I.ι ((innerSL ℂ v).toLinearMap ∘ₗ (LinearMap.proj 1) ∘ₗ I.fns.subtype)
    (fun a ha => by simp [apply_one_eq_zero I a ha])
  have hℓ' : ∀ a : I.fns, ℓ (I.ι a) = ⟪v, a.1 1⟫_ℂ := fun a => by rw [hℓ]; rfl
  have hinD : ∀ {F : ℝ → I.V} {F' : I.V}, HasDerivAt F F' 0 → HasDerivAt (fun t => ⟪v, F t⟫_ℂ) ⟪v, F'⟫_ℂ 0 :=
    fun hF => (((innerSL ℂ v).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hF
  have lawT : ∀ (g : I.fns) θ, ⟪v, g.1 (expG ε T θ)⟫_ℂ = starRingEnd ℂ (c θ) * ⟪v, g.1 1⟫_ℂ := by
    intro g θ
    have := law0 g 1 hN1 _ (hTθ θ).1.2
    rw [one_mul] at this
    rw [this, key]

  obtain ⟨f₁', hd₁, -⟩ := hder f₁ hf₁k T hT
  set γ := ⟪v, f₁'.1 1⟫_ℂ / ⟪v, f₁.1 1⟫_ℂ
  have hg : HasDerivAt (fun θ : ℝ => starRingEnd ℂ (c θ)) γ 0 := by
    have := (hinD (by simpa using hd₁ 1)).div_const ⟪v, f₁.1 1⟫_ℂ
    have e : (fun θ : ℝ => starRingEnd ℂ (c θ)) = fun θ => ⟪v, f₁.1 (expG ε T θ)⟫_ℂ / ⟪v, f₁.1 1⟫_ℂ := by
      funext θ
      rw [lawT, mul_div_assoc, div_self hvx, mul_one]
    rw [e]
    exact this
  refine ⟨ℓ, γ, ⟨I.ι f₁, hy₁Y, by rw [hℓ']; exact hvx⟩, ?_, ?_, ?_⟩
  · intro X hX hXN w hw
    obtain ⟨g, g', rfl, he, hd⟩ := dat1 X hX w hw
    rw [← he, hℓ']
    have hconst : (fun t : ℝ => g.1 (expG ε X t)) = fun _ => g.1 1 := funext fun t => by
      simpa [huM1, hσ1] using law0 g _ (hXN t) 1 (one_mem _)
    rw [hconst] at hd
    rw [hd.unique (hasDerivAt_const _ _), inner_zero_right]
  · intro w hw
    obtain ⟨g, g', rfl, he, hd⟩ := dat1 H₀ hH₀ w hw
    rw [← he, hℓ', hℓ']
    have hIio : Finset.Iio (⟨0, h⟩ : Fin I.a) = ∅ := by
      ext l; simp [Fin.lt_iff_val_lt_val]
    have hpair : ∀ t : ℝ, pairing I.j (I.s + rho n I.j) (Pi.single ⟨0, h⟩ t) = (I.s ⟨0, h⟩ + n - 1) * t := by
      intro t
      rw [pairing, Finset.sum_eq_single ⟨0, h⟩]
      · simp [hj, rho, hIio]
        left; ring
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    have hfun : (fun t : ℝ => g.1 (expG ε H₀ t)) = fun t : ℝ => Complex.exp ((I.s ⟨0, h⟩ + n - 1) * t) • g.1 1 :=
      funext fun t => by
        have := law g 1 hN1 1 (one_mem _) _ _ (hsp t)
        rw [one_mul, one_mul, hpair, huM1, hσ1] at this
        simpa using this
    rw [hfun] at hd
    have hd' : HasDerivAt (fun t : ℝ => Complex.exp ((I.s ⟨0, h⟩ + n - 1) * t) • g.1 1)
        ((I.s ⟨0, h⟩ + n - 1) • g.1 1) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (I.s ⟨0, h⟩ + n - 1)).cexp).smul_const (g.1 1)
      simpa using this
    rw [hd.unique hd', inner_smul_right]
  · intro w hw
    obtain ⟨g, g', rfl, he, hd⟩ := dat1 T hT w hw
    rw [← he, hℓ', hℓ']
    have h2 := hinD hd
    have h3 : HasDerivAt (fun θ : ℝ => ⟪v, g.1 (expG ε T θ)⟫_ℂ) (γ * ⟪v, g.1 1⟫_ℂ) 0 := by
      have e : (fun θ : ℝ => ⟪v, g.1 (expG ε T θ)⟫_ℂ) = fun θ => starRingEnd ℂ (c θ) * ⟪v, g.1 1⟫_ℂ := by
        funext θ
        rw [lawT]
      rw [e]
      exact hg.mul_const ⟪v, g.1 1⟫_ℂ
    exact h2.unique h3

end GlobalTheory.IndFunctional
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_stable_subspace_exponent_functional : GlobalTheory.Published.Langlands.Induced → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ H₀ T : Matrix (Fin n) (Fin n) ℂ, H₀ ∈ lieSet ε → T ∈ lieSet ε → (∀ x : ℝ, IsSplit ε I.W (Pi.single ⟨0, h⟩ x) (expG ε H₀ x)) → (∀ θ : ℝ, expG ε T θ ∈ KG ε ⊓ I.M ∧ ∀ m ∈ I.M, expG ε T θ * m = m * expG ε T θ) → ∀ Y : Submodule ℂ I.H, Y ≤ kFinVec ε I.ρ → Y ≠ ⊥ → IsKStableOn ε I.ρ Y → ∃ (ℓ : I.H →ₗ[ℂ] ℂ) (γ : ℂ), (∃ y ∈ Y, ℓ y ≠ 0) ∧ (∀ X ∈ lieSet ε, (∀ t, expG ε X t ∈ flagN ε I.W) → ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ X w) = 0) ∧ (∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ H₀ w) = (I.s ⟨0, h⟩ + n - 1) * ℓ w) ∧ ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ T w) = γ * ℓ w := by
  atlas_forward_decl GlobalTheory.IndFunctional.functional
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.IndCap

theorem epow_eq_pow' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (m : ℕ) (a b : Fin n) :
    epow E m a b = (Matrix.of E ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp [epow, pow_succ, Matrix.mul_apply, ih]

theorem etr_succ_eq_gelfA' {B : Type} [Ring B] [Algebra ℂ B] {n : ℕ} (E : Fin n → Fin n → B) (k : ℕ) :
    etr E (k + 1) = GlobalTheory.SmoothForms.gelfA E k := by
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]; simp [etr, epow_eq_pow']

theorem commute_epow' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (z : B)
    (hz : ∀ a b, Commute z (E a b)) (m : ℕ) (a b : Fin n) : Commute z (epow E m a b) := by
  induction m generalizing a b with
  | zero => simp only [epow]; split_ifs <;> simp
  | succ m ih => simp only [epow]; exact Commute.sum_right _ _ _ fun c _ => (ih a c).mul_right (hz c b)

theorem commute_etr' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (z : B)
    (hz : ∀ a b, Commute z (E a b)) (m : ℕ) : Commute z (etr E m) :=
  Commute.sum_right _ _ _ fun a _ => commute_epow' E z hz m a a

theorem lift_etr' {n : ℕ} {B : Type} [Ring B] [Algebra ℂ B] (φ : Fin n × Fin n → B) (m : ℕ) :
    FreeAlgebra.lift ℂ φ (etr (Egl n) m) = etr (fun a b => φ (a, b)) m := by
  have key : ∀ a b, FreeAlgebra.lift ℂ φ (epow (Egl n) m a b) = epow (fun a b => φ (a, b)) m a b := by
    induction m with
    | zero => intro a b; simp only [epow]; split_ifs <;> simp
    | succ m ih => intro a b; simp [epow, map_sum, map_mul, ih, Egl]
  simp [etr, map_sum, key]

section Restr
variable {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (V : Submodule ℂ M)
  (E : Fin n → Fin n → Module.End ℂ M) (hE : ∀ a b, ∀ v ∈ V, E a b v ∈ V)

theorem epow_restrict' (m : ℕ) (a b : Fin n) (v : V) :
    ((epow (fun a b => (E a b).restrict (hE a b)) m a b v : V) : M) = epow E m a b v := by
  induction m generalizing a b v with
  | zero => simp only [epow]; split_ifs <;> simp
  | succ m ih =>
    simp only [epow, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, ih]
    rfl

theorem glRel_restrict' (h : GlRel E) : GlRel (fun a b => (E a b).restrict (hE a b)) := by
  intro a b c d
  ext v
  have := congrArg (fun F => F (v : M)) (h a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, LinearMap.restrict_apply]
  rw [this]
  split_ifs <;> simp
end Restr

theorem infChar_sub_eq_of_line : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ χ : Fin n → ℂ, (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ i j, i ≠ j ∧ χ i - χ j = I.s ⟨0, h⟩ := by
  intro hLC n ε I h hj χ hnil
  obtain ⟨hInd, -⟩ := hLC
  obtain ⟨hadm, -, hgk, -⟩ := hInd n ε I
  obtain ⟨A, hA1, hA2, hA3, hA4, -⟩ := GlobalTheory.T.gl_relations_on_k_finite_vectors n ε I.H I.ρ hadm hgk
  set E0 : Fin n → Fin n → Module.End ℂ (kFinVec ε I.ρ) := fun a b => A (Matrix.single a b 1) with hE0
  have hGl0 : GlRel E0 := by simpa using (hA2 1 isUnit_one).1
  set T : ℕ → Module.End ℂ (kFinVec ε I.ρ) := fun k => etr E0 (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1)) with hT
  have hcommE : ∀ k a b, Commute (etr E0 (k + 1)) (E0 a b) := fun k a b => by
    rw [etr_succ_eq_gelfA']; exact (GlobalTheory.SmoothForms.commute_gelfA _ n E0 hGl0 k a b).symm
  have hcommTE : ∀ k a b, Commute (T k) (E0 a b) := fun k a b =>
    (hcommE k a b).sub_left (Algebra.commute_algebraMap_left _ _)
  have hTcomm : ∀ k l, Commute (T k) (T l) := fun k l =>
    ((commute_etr' E0 _ (hcommTE k) (l + 1))).sub_right (Algebra.commute_algebraMap_right _ _)
  have hnilT : ∀ k (v : kFinVec ε I.ρ), ∃ N : ℕ, (T k ^ N) v = 0 := fun k v => by
    obtain ⟨N, hN⟩ := hnil k v v.2
    refine ⟨N, ?_⟩
    rw [hA3] at hN
    have e : FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1))
        ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) = T k ^ N := by
      rw [map_pow, map_sub, AlgHom.commutes, lift_etr']
    rw [e] at hN
    exact Subtype.ext (by simpa using hN)
  have hTK : ∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε I.ρ), (w : I.H) = I.ρ κ v →
      ((T k w : kFinVec ε I.ρ) : I.H) = I.ρ κ (T k v : I.H) := fun κ hκ k v w hw => by
    have := hA4 κ hκ (k + 1) v w hw
    simp only [hT, LinearMap.sub_apply, Submodule.coe_sub, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, Submodule.coe_smul, this, hw, map_sub, map_smul]
  haveI : Nontrivial I.H := GlobalTheory.T.induced_module_nontrivial n ε I
  obtain ⟨S, hSfd, hS0, hST⟩ := GlobalTheory.T.finite_dimensional_invariant_subspace n ε I.H I.ρ hadm T hTK
  obtain ⟨v₀, -, hv₀, hv₀T⟩ := GlobalTheory.T.common_kernel_commuting_nilpotent _ T S hSfd hS0 hST hTcomm (fun k v _ => hnilT k v)
  set Y : Submodule ℂ (kFinVec ε I.ρ) := ⨅ k : ℕ, LinearMap.ker (T k) with hY
  have memY : ∀ w, w ∈ Y ↔ ∀ k, T k w = 0 := fun w => by simp [hY, Submodule.mem_iInf]
  have hYE : ∀ a b, ∀ w ∈ Y, E0 a b w ∈ Y := fun a b w hw => (memY _).2 fun k => by
    rw [← Module.End.mul_apply, (hcommTE k a b).eq, Module.End.mul_apply, (memY w).1 hw k, map_zero]
  have hYA : ∀ Z : Matrix (Fin n) (Fin n) ℂ, ∀ w ∈ Y, A Z w ∈ Y := fun Z w hw => by
    rw [Matrix.matrix_eq_sum_single Z]
    simp only [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    rw [show Matrix.single a b (Z a b) = Z a b • Matrix.single a b 1 by simp [Matrix.smul_single], map_smul,
      LinearMap.smul_apply]
    exact Y.smul_mem _ (hYE a b w hw)

  have hv₀Y : v₀ ∈ Y := (memY v₀).2 hv₀T
  set Y' : Submodule ℂ I.H := Y.map (kFinVec ε I.ρ).subtype with hY'
  have hY'le : Y' ≤ kFinVec ε I.ρ := Submodule.map_subtype_le _ _
  have hY'0 : Y' ≠ ⊥ := by
    intro e
    have : ((v₀ : kFinVec ε I.ρ) : I.H) ∈ Y' := Submodule.mem_map_of_mem hv₀Y
    rw [e, Submodule.mem_bot] at this
    exact hv₀ (Subtype.ext this)
  have hY'K : IsKStableOn ε I.ρ Y' := by
    rintro g hg _ ⟨w, hw, rfl⟩
    have hm : I.ρ g (w : I.H) ∈ kFinVec ε I.ρ := isKStableOn_kFinVec ε I.ρ g hg _ w.2
    refine ⟨⟨_, hm⟩, (memY _).2 fun k => Subtype.ext ?_, rfl⟩
    rw [hTK g hg k w ⟨_, hm⟩ rfl, (memY w).1 hw k]
    simp

  have hW1 : Module.finrank ℂ (I.W ⟨1, Nat.succ_lt_succ h⟩) = 1 := by
    have := I.flag.2.2.1 ⟨0, h⟩
    have hz : Module.finrank ℂ (I.W (⟨0, h⟩ : Fin I.a).castSucc) = 0 := Submodule.finrank_eq_zero.2 I.flag.1
    rw [hz, hj] at this
    exact this.trans (zero_add 1)
  obtain ⟨e, he1, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.1 hW1.ge)
  have hiso : star e ⬝ᵥ (Jm ε *ᵥ e) = 0 := by
    have hl : e ∈ I.W (Fin.last I.a) := I.flag.2.1 (Fin.le_last _) he1
    exact I.flag.2.2.2 e hl e hl
  obtain ⟨P, p, q, c, hPu, hpq, hPe, hPe', hG⟩ := GlobalTheory.T.hyperbolic_pair_change_of_basis n ε e he0 hiso
  have hPe1 : P *ᵥ Pi.single p 1 ∈ I.W ⟨1, Nat.succ_lt_succ h⟩ := hPe ▸ he1
  have hPe'' : P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) := by rw [hPe]; exact hPe'
  obtain ⟨hOffp, hOffq⟩ := GlobalTheory.T.hyperbolic_pair_in_first_flag_space n ε I.a I.j I.W h I.flag hj P p q c hPu hpq hPe1 hPe'' hG
  obtain ⟨hH₀, hsplit, hTc, hTcc⟩ := GlobalTheory.T.hyperbolic_pair_split_torus n ε I.a I.j I.W h I.flag hj P p q c hPu hpq hPe1 hPe'' hG
  set H₀ := P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹ with hH₀def
  set Tc := P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹ with hTcdef
  obtain ⟨ℓ, γ, ⟨y, hyY, hy⟩, hℓN, hℓH, hℓT⟩ := GlobalTheory.T.k_stable_subspace_exponent_functional hInd n ε I h hj H₀ Tc hH₀ hTc hsplit hTcc Y' hY'le hY'0 hY'K

  set E' : Fin n → Fin n → Module.End ℂ Y := fun a b => (A (P * Matrix.single a b 1 * P⁻¹)).restrict
    (fun w hw => hYA _ w hw) with hE'
  have hGl' : GlRel E' := glRel_restrict' Y _ _ (hA2 P hPu).1
  have hetr' : ∀ (k : ℕ) (v : Y), etr E' (k + 1) v = gelfVal χ (k + 1) • v := fun k v => by
    apply Subtype.ext
    have e1 : ((etr E' (k + 1) v : Y) : kFinVec ε I.ρ) = etr (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) (k + 1) v := by
      simp only [etr, LinearMap.sum_apply, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun a _ => epow_restrict' Y _ _ (k + 1) a a v
    rw [e1, (hA2 P hPu).2]
    have := (memY v).1 v.2 k
    simp only [hT, LinearMap.sub_apply, sub_eq_zero, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply] at this
    rw [this]; rfl
  have hqdet := GlobalTheory.T.qdet_apply_eq_prod_of_gelfVal Y n E' χ hGl' hetr'
  set ℓ' : Y →ₗ[ℂ] ℂ := ℓ ∘ₗ (kFinVec ε I.ρ).subtype ∘ₗ Y.subtype with hℓ'
  have hℓ'0 : ℓ' ≠ 0 := by
    obtain ⟨w, hw, rfl⟩ := hyY
    intro e0
    exact hy (by simpa [hℓ'] using LinearMap.congr_fun e0 ⟨w, hw⟩)

  have hE'v : ∀ a b (v : Y), ℓ' (E' a b v) =
      ℓ ((A (P * Matrix.single a b 1 * P⁻¹) (v : kFinVec ε I.ρ) : kFinVec ε I.ρ) : I.H) := fun a b v => rfl
  have hℓ'v : ∀ v : Y, ℓ' v = ℓ ((v : kFinVec ε I.ρ) : I.H) := fun v => rfl
  have hsplitA : ∀ (X X' : Matrix (Fin n) (Fin n) ℂ) (u v : ℂ) (w : Y), X ∈ lieSet ε → X' ∈ lieSet ε →
      ℓ ((A (u • X + v • X') (w : kFinVec ε I.ρ) : kFinVec ε I.ρ) : I.H) =
        u * ℓ (dRep I.ρ X ((w : kFinVec ε I.ρ) : I.H)) + v * ℓ (dRep I.ρ X' ((w : kFinVec ε I.ρ) : I.H)) := by
    intro X X' u v w hX hX'
    rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, map_add, map_smul, map_smul, hA1 X hX, hA1 X' hX',
      smul_eq_mul, smul_eq_mul]
  have hoffp : ∀ b, b ≠ p → ∀ v : Y, ℓ' (E' p b v) = 0 := fun b hb v => by
    obtain ⟨X, X', hX, hX', hXN, hX'N, he⟩ := hOffp b hb
    rw [hE'v, he, show X + Complex.I • X' = (1 : ℂ) • X + Complex.I • X' by rw [one_smul], hsplitA X X' _ _ v hX hX',
      hℓN X hX hXN _ (v : kFinVec ε I.ρ).2, hℓN X' hX' hX'N _ (v : kFinVec ε I.ρ).2]
    simp
  have hoffq : ∀ b, b ≠ q → ∀ v : Y, ℓ' (E' b q v) = 0 := fun b hb v => by
    obtain ⟨X, X', hX, hX', hXN, hX'N, he⟩ := hOffq b hb
    rw [hE'v, he, show X + Complex.I • X' = (1 : ℂ) • X + Complex.I • X' by rw [one_smul], hsplitA X X' _ _ v hX hX',
      hℓN X hX hXN _ (v : kFinVec ε I.ρ).2, hℓN X' hX' hX'N _ (v : kFinVec ε I.ρ).2]
    simp
  have hdiag : ∀ (u v : ℂ) (r : Fin n), (∀ i, diagonal (Pi.single r (1 : ℂ)) i i =
      u * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) i + v * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) i) →
      P * Matrix.single r r 1 * P⁻¹ = u • H₀ + v • Tc := by
    intro u v r hr
    have e : Matrix.single r r (1 : ℂ) = u • diagonal (Pi.single p 1 - Pi.single q 1) +
        v • diagonal (Pi.single p Complex.I + Pi.single q Complex.I) := by
      ext i k
      by_cases hik : i = k
      · subst hik
        have := hr i
        simp only [diagonal_apply_eq] at this
        simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul]
        rw [← this, Matrix.single_apply, Pi.single_apply]
        by_cases h' : r = i <;> simp [h', eq_comm]
      · have hn : ¬ (r = i ∧ r = k) := fun hh => hik (hh.1 ▸ hh.2)
        simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply_ne _ hik, smul_zero, add_zero]
        rw [Matrix.single_apply, if_neg hn]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
  have hDp : P * Matrix.single p p 1 * P⁻¹ = (1 / 2 : ℂ) • H₀ + (-(Complex.I / 2)) • Tc := hdiag _ _ p fun i => by
    by_cases hi : i = p
    · subst hi; simp [Pi.single_apply, hpq.symm]; ring_nf; rw [Complex.I_sq]; ring
    · by_cases hi' : i = q
      · subst hi'; simp [Pi.single_apply, hi]; ring_nf; rw [Complex.I_sq]; ring
      · simp [Pi.single_apply, hi, hi']
  have hDq : P * Matrix.single q q 1 * P⁻¹ = (-(1 / 2) : ℂ) • H₀ + (-(Complex.I / 2)) • Tc := hdiag _ _ q fun i => by
    by_cases hi : i = p
    · subst hi; simp [Pi.single_apply, hpq]; ring_nf; rw [Complex.I_sq]; ring
    · by_cases hi' : i = q
      · subst hi'; simp [Pi.single_apply, hi]; ring_nf; rw [Complex.I_sq]; ring
      · simp [Pi.single_apply, hi, hi']
  set α : ℂ := (1 / 2 : ℂ) * (I.s ⟨0, h⟩ + n - 1) + (-(Complex.I / 2)) * γ with hα
  set β : ℂ := (-(1 / 2) : ℂ) * (I.s ⟨0, h⟩ + n - 1) + (-(Complex.I / 2)) * γ with hβ
  have hdp : ∀ v : Y, ℓ' (E' p p v) = α * ℓ' v := fun v => by
    rw [hE'v, hDp, hsplitA _ _ _ _ v hH₀ hTc, hℓH _ (v : kFinVec ε I.ρ).2, hℓT _ (v : kFinVec ε I.ρ).2, hℓ'v, hα]
    ring
  have hdq : ∀ v : Y, ℓ' (E' q q v) = β * ℓ' v := fun v => by
    rw [hE'v, hDq, hsplitA _ _ _ _ v hH₀ hTc, hℓH _ (v : kFinVec ε I.ρ).2, hℓT _ (v : kFinVec ε I.ρ).2, hℓ'v, hβ]
    ring
  obtain ⟨i, k, hik, hi, hk⟩ := GlobalTheory.T.highest_weight_functional_character Y n E' χ hGl' hqdet p q hpq ℓ' α β hℓ'0 hoffp hoffq hdp hdq
  exact ⟨i, k, hik, by rw [hi, hk, hα, hβ]; ring⟩

end GlobalTheory.IndCap

end
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_difference : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ χ : Fin n → ℂ, (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ i j, i ≠ j ∧ χ i - χ j = I.s ⟨0, h⟩ := by
  atlas_forward_decl GlobalTheory.IndCap.infChar_sub_eq_of_line
end
