import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.LowLES
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer

open _root_.Neutral.B1

noncomputable section

def quotAddCongr {R R' A A' : Type} [Ring R] [Ring R'] [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R' A']
    (P : Submodule R A) (P' : Submodule R' A') (e : A ≃+ A') (h : ∀ x, x ∈ P ↔ e x ∈ P') : (A ⧸ P) ≃+ (A' ⧸ P') :=
  QuotientAddGroup.congr P.toAddSubgroup P'.toAddSubgroup e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).1 hx
    · intro hy
      exact ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩)

section Scalars

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (rho : Representation R G M) (rho' : Representation ℤ G M) (h : ∀ g m, rho g m = rho' g m)

def oneCocyclesScalarEquiv : Z1 rho ≃+ Z1 rho' where
  toFun f := ⟨f.1, f.2.1, fun g k => by rw [← h]; exact f.2.2 g k⟩
  invFun f := ⟨f.1, f.2.1, fun g k => by rw [h]; exact f.2.2 g k⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def twoCocyclesScalarEquiv : Z2 rho ≃+ Z2 rho' where
  toFun f := ⟨f.1, f.2.1, fun g k l => by rw [← h]; exact f.2.2 g k l⟩
  invFun f := ⟨f.1, f.2.1, fun g k l => by rw [h]; exact f.2.2 g k l⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def h1ScalarEquiv : H1 rho ≃+ H1 rho' :=
  quotAddCongr _ _ (oneCocyclesScalarEquiv rho rho' h) fun f => by
    show f.1 ∈ Bd1 rho ↔ f.1 ∈ Bd1 rho'
    simp only [mem_contCoboundaries1, h]

def h2ScalarEquiv : H2 rho ≃+ H2 rho' :=
  quotAddCongr _ _ (twoCocyclesScalarEquiv rho rho' h) fun f => by
    show f.1 ∈ Bd2 rho ↔ f.1 ∈ Bd2 rho'
    have hd : ∀ c : G → M, d1 rho c = d1 rho' c := fun c => by
      funext x
      show rho x.1 (c x.2) - c (x.1 * x.2) + c x.1 = rho' x.1 (c x.2) - c (x.1 * x.2) + c x.1
      rw [h]
    simp only [mem_contCoboundaries2, hd]

end Scalars

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

theorem kbarRep_apply (σ : GK p K) (x : (PadicAlgCl p)ˣ) :
    kbarRep p K σ (Additive.ofMul x : KbarMult p) =
      (Additive.ofMul (Units.map (σ : PadicAlgCl p →* PadicAlgCl p) x) : KbarMult p) := rfl

theorem contAction_kbarRep : ReciprocityTheory.Gal.ContAction (kbarRep p K) := by
  show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2
  rw [continuous_prod_of_discrete_right]
  intro x
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun σ₀ => ?_)
  have hx := stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p)
    ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)
  refine ⟨_, hx.preimage (continuous_const_mul σ₀⁻¹), ?_, ?_⟩
  · simp
  · intro σ hσ
    have h1 : (σ₀⁻¹ * σ) ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = (Additive.toMul x : (PadicAlgCl p)ˣ) := hσ
    have h2 : σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = σ₀ (Additive.toMul x : (PadicAlgCl p)ˣ) := by
      have := congrArg σ₀ h1
      simpa [AlgEquiv.mul_apply] using this
    exact Units.ext h2

def kT : ReciprocityTheory.Coh.TRep ℤ (GK p K) where
  V := KbarMult p
  rho := kbarRep p K
  cont := contAction_kbarRep p K

def muRep : Representation ℤ (GK p K) (ZMod n) where
  toFun g := (charRep (cycK p K n) g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun x => by
    show charRep (cycK p K n) 1 x = x
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun x => by
    show charRep (cycK p K n) (g * h) x = charRep (cycK p K n) g (charRep (cycK p K n) h x)
    rw [map_mul]; rfl

theorem muRep_apply (g : GK p K) (x : ZMod n) : muRep p K n g x = ((cycK p K n g : (ZMod n)ˣ) : ZMod n) * x := rfl

variable {p n}

def muMap (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) : ZMod n →ₗ[ℤ] KbarMult p :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun k => (Additive.ofMul (ζ ^ k.val) : KbarMult p)
      map_zero' := by simp; rfl
      map_add' := fun a b => by
        show ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val
        rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add] }

theorem muMap_apply (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (k : ZMod n) :
    muMap ζ hζ k = (Additive.ofMul (ζ ^ k.val) : KbarMult p) := rfl

theorem muMap_equiv (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (g : GK p K) (k : ZMod n) :
    muMap ζ hζ (muRep p K n g k) = kbarRep p K g (muMap ζ hζ k) := by
  rw [muMap_apply, muMap_apply, kbarRep_apply, muRep_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  have h1 : ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, Units.val_one]
  have h2 := cycN_spec (K := K) g _ h1
  show _ = g ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p)
  rw [h2, ← Units.val_pow_eq_pow_val, ZMod.val_mul, ← pow_eq_pow_mod _ hζ, ← pow_mul, mul_comm]

theorem muMap_injective {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : Function.Injective (muMap ζ hζ.pow_eq_one) := by
  intro a b hab
  exact ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab)

variable (p n) in

def powMap : KbarMult p →ₗ[ℤ] KbarMult p := (n : ℤ) • LinearMap.id

theorem powMap_apply (x : (PadicAlgCl p)ˣ) :
    powMap p n (Additive.ofMul x : KbarMult p) = (Additive.ofMul (x ^ n) : KbarMult p) := by
  show (n : ℤ) • (Additive.ofMul x : Additive (PadicAlgCl p)ˣ) = _
  rw [natCast_zsmul]; rfl

theorem powMap_surjective : Function.Surjective (powMap p n) := by
  intro y
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p) (NeZero.pos n)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hz
    exact (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero hz.symm
  refine ⟨(Additive.ofMul (Units.mk0 z hz0) : KbarMult p), ?_⟩
  rw [powMap_apply]
  exact congrArg Additive.ofMul (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hz))

theorem exact_muMap_powMap {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Function.Exact (muMap ζ hζ.pow_eq_one) (powMap p n) := by
  intro y
  constructor
  · intro hy
    have h1 : (Additive.toMul y : (PadicAlgCl p)ˣ) ^ n = 1 := by
      have := powMap_apply (p := p) (n := n) (Additive.toMul y)
      exact (this.symm.trans hy : _)
    have h2 : ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨i, hi, hi'⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one h2
    have hi'' : ζ ^ i = (Additive.toMul y : (PadicAlgCl p)ˣ) := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hi')
    refine ⟨(i : ZMod n), ?_⟩
    rw [muMap_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hi'']; rfl
  · rintro ⟨k, rfl⟩
    rw [muMap_apply, powMap_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]; rfl

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

namespace Kummer

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

theorem exists_primitive_unit : ∃ ζ : (PadicAlgCl p)ˣ, IsPrimitiveRoot ζ n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) n
  exact ⟨_, hζ.isUnit_unit (NeZero.ne n)⟩

theorem isEmbedding_muMap {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Topology.IsEmbedding (muMap ζ hζ.pow_eq_one) :=
  (Continuous.isClosedEmbedding continuous_of_discreteTopology (muMap_injective hζ)).isEmbedding

theorem contAction_muRep : ReciprocityTheory.Gal.ContAction (muRep p K n) := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit p n
  show Continuous fun q : GK p K × ZMod n => muRep p K n q.1 q.2
  rw [(isEmbedding_muMap p n hζ).continuous_iff]
  have h : (muMap ζ hζ.pow_eq_one ∘ fun q : GK p K × ZMod n => muRep p K n q.1 q.2) =
      fun q => kbarRep p K q.1 (muMap ζ hζ.pow_eq_one q.2) := funext fun q => muMap_equiv K ζ _ q.1 q.2
  rw [h]
  exact (contAction_kbarRep p K).comp (f := fun q : GK p K × ZMod n => (q.1, muMap ζ hζ.pow_eq_one q.2))
    (continuous_fst.prodMk (continuous_of_discreteTopology.comp continuous_snd))

def muT : TRep ℤ (GK p K) where
  V := ZMod n
  rho := muRep p K n
  cont := contAction_muRep p K n

variable {p n} in

def iP {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : Pair (muT p K n) (kT p K) :=
  Pair.ofMap (M := muT p K n) (M' := kT p K) (muMap ζ hζ.pow_eq_one)
    (continuous_of_discreteTopology : Continuous (muMap ζ hζ.pow_eq_one : ZMod n → KbarMult p))
    (muMap_equiv K ζ _)

def pP : Pair (kT p K) (kT p K) :=
  Pair.ofMap (M := kT p K) (M' := kT p K) (powMap p n)
    (continuous_of_discreteTopology : Continuous (powMap p n : KbarMult p → KbarMult p))
    fun g m => (map_zsmul (kbarRep p K g) (n : ℤ) m).symm

variable {p n} in
theorem adm {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : admitted (iP K hζ) (pP p K n) :=
  ⟨rfl, rfl, isEmbedding_muMap p n hζ, exact_muMap_powMap hζ,
    ⟨Function.surjInv (powMap_surjective (p := p) (n := n)),
      (continuous_of_discreteTopology : Continuous (Function.surjInv (powMap_surjective (p := p) (n := n)))),
      Function.surjInv_eq _⟩⟩

def unitsToInvariants' : Additive Kˣ →+ ReciprocityTheory.Gal.H0 (kT p K).rho where
  toFun a := ⟨(Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul) : KbarMult p),
    fun σ => Units.ext (σ.commutes _)⟩
  map_zero' := Subtype.ext (by simp; rfl)
  map_add' a b := Subtype.ext (by simp; rfl)

theorem units_to_invariants_prime_injective : Function.Injective (unitsToInvariants' p K) := by
  intro a b hab
  have h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul =
      Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul := congrArg Subtype.val hab
  exact Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1

theorem units_to_invariants_prime_surjective : Function.Surjective (unitsToInvariants' p K) := by
  rintro ⟨x, hx⟩
  have : IsGalois K (PadicAlgCl p) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have h1 : ∀ σ : GK p K, σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = (Additive.toMul x : (PadicAlgCl p)ˣ) :=
    fun σ => congrArg (fun y : KbarMult p => ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)) (hx σ)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero ha.symm
  exact ⟨Additive.ofMul (Units.mk0 a ha0), Subtype.ext (Units.ext ha)⟩

theorem power_map_h0_unitsToInvariants (b : Kˣ) :
    (pP p K n).h0 (unitsToInvariants' p K (Additive.ofMul b)) = unitsToInvariants' p K (Additive.ofMul (b ^ n)) := by
  refine Subtype.ext ?_
  show powMap p n (Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b) : KbarMult p) = _
  rw [powMap_apply, ← map_pow]
  rfl

end

end Kummer

open Kummer

theorem h1_roots_of_unity_equiv_of_h1_subsingleton (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]
    (h90 : Subsingleton (H1 (kbarRep p K))) :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit p n
  obtain ⟨δ₀, δ₁, -, -, -, -, e2, e3, -⟩ :=
    low_degree_long_exact_sequence ℤ (GK p K) (muT p K n) (kT p K) (kT p K) (iP K hζ) (pP p K n) (adm K hζ)
  have h90' : Subsingleton (ReciprocityTheory.Gal.H1 (kT p K).rho) := h90
  have hs : Function.Surjective δ₀ := fun y => (e3 y).1 (Subsingleton.elim _ _)
  let ψ : Kˣ →* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    AddMonoidHom.toMultiplicativeRight (δ₀.toAddMonoidHom.comp (unitsToInvariants' p K))
  have hψ : ∀ a : Kˣ, ψ a = Multiplicative.ofAdd (δ₀ (unitsToInvariants' p K (Additive.ofMul a))) := fun a => rfl
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hs y.toAdd
    obtain ⟨a, rfl⟩ := units_to_invariants_prime_surjective p K x
    exact ⟨a.toMul, hx⟩
  have hker : ψ.ker = (powMonoidHom n : Kˣ →* Kˣ).range := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro ha
      have ha' : δ₀ (unitsToInvariants' p K (Additive.ofMul a)) = 0 := ha
      obtain ⟨y, hy⟩ := (e2 _).1 ha'
      obtain ⟨b, rfl⟩ := units_to_invariants_prime_surjective p K y
      refine ⟨b.toMul, ?_⟩
      have := (power_map_h0_unitsToInvariants p K n b.toMul).symm.trans hy
      exact units_to_invariants_prime_injective p K this
    · rintro ⟨b, rfl⟩
      show δ₀ (unitsToInvariants' p K (Additive.ofMul (b ^ n))) = 0
      exact (e2 _).2 ⟨_, power_map_h0_unitsToInvariants p K n b⟩
  have E1 : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  exact ⟨(h1ScalarEquiv (charRep (cycK p K n)) (muRep p K n) fun _ _ => rfl).trans (MulEquiv.toAdditiveLeft E1).symm⟩

theorem h1_roots_of_unity_equiv_units_quot_pow (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n] :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) :=
  h1_roots_of_unity_equiv_of_h1_subsingleton p K n (h1_kbarRep_subsingleton p K)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
