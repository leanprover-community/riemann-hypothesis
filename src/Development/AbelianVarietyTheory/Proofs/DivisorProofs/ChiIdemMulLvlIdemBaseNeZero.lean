import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCoeffChiIdemMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerEqOneOfCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerateWhittakerDimParabolicInductionCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockEmbeddingFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePower
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacter
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersOfAbelianByPrimePower
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AsAlgebraHomSurjectiveOfFinrankIntertwiningMapEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceCompLeftFunLeft

section
noncomputable section

namespace GlobalTheory.GenericProduct

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne NumberField Module

def OneGenericVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 →
    ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
      (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1

section Twist

variable {K P V : Type} [Field K] [Group P] [AddCommGroup V] [Module K V]

def twistInv (τ : Representation K P V) (c : P →* Kˣ) : Representation K P V where
  toFun h := (((c h)⁻¹ : Kˣ) : K) • τ h
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]

theorem twistInv_apply (τ : Representation K P V) (c : P →* Kˣ) (h : P) :
    twistInv τ c h = (((c h)⁻¹ : Kˣ) : K) • τ h := rfl

theorem sum_trace_mul_inv [Fintype P] [CharZero K] [FiniteDimensional K V] (τ : Representation K P V) (c : P →* Kˣ) :
    ∑ h : P, LinearMap.trace K V (τ h) * (((c h)⁻¹ : Kˣ) : K) =
      (Nat.card P : K) * (finrank K (twistInv τ c).invariants : K) := by
  have hc : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI : Invertible (Nat.card P : K) := invertibleOfNonzero hc
  letI : Invertible (Fintype.card P : K) := invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact hc)
  have h := Representation.card_inv_mul_sum_char_eq_finrank (twistInv τ c)
  rw [← h, mul_inv_cancel_left₀ hc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.character, twistInv_apply, map_smul, smul_eq_mul, mul_comm]

end Twist

theorem sum_unip_eq {F : Type} [Field F] {r : ℕ} [Fintype (unip F r)] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) :
    ∑ h : unip F r, LinearMap.trace ℂ V (τ h) * (((addCharHom ψ (supHom F r) h)⁻¹ : ℂˣ) : ℂ) =
      (Nat.card (unip F r) : ℂ) * (whDim ψ τ : ℂ) := by
  have h := sum_trace_mul_inv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))
  have e : (twistInv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))).invariants =
      eig τ (unip F r : Set (GL (Fin r) F)) fun g => ψ (edgeSum supEdge g) := by
    ext v
    simp only [Representation.mem_invariants, eig, Submodule.mem_iInf, LinearMap.mem_ker, twistInv_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have key : ∀ g : unip F r, ((((addCharHom ψ (supHom F r) g)⁻¹ : ℂˣ) : ℂ) • (τ.comp (unip F r).subtype g) v = v ↔
        τ g v = ψ (edgeSum supEdge (g : GL (Fin r) F)) • v) := by
      intro g
      have hv : ψ (edgeSum supEdge (g : GL (Fin r) F)) = ((addCharHom ψ (supHom F r) g : ℂˣ) : ℂ) := rfl
      rw [hv, Units.val_inv_eq_inv_val, inv_smul_eq_iff₀ (Units.ne_zero _)]
      rfl
    exact ⟨fun H g hg => (key ⟨g, hg⟩).1 (H ⟨g, hg⟩), fun H g => (key g).2 (H g.1 g.2)⟩
  rw [e] at h
  exact h

def piEquiv {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H) ≃ ∀ i, H i where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ _)⟩
  invFun y := ⟨fun i => (y i).1, fun i _ => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

attribute [local instance] resField finite_res

theorem genericMultOne (hL : OneGenericVector) : GenericMultOne := by
  classical
  intro E _ _ Pg r K _ _ s ψ hψ χ hχ
  obtain ⟨b, V, i1, i2, i3, σ, hσ, hs⟩ := hχ
  letI : Fintype (P0 Pg r ψ).H := Fintype.ofFinite _
  letI : ∀ PP : ↥Pg, Fintype (unip (kP PP.1) r) := fun PP => Fintype.ofFinite _
  apply s.injective
  let ψ' : ∀ PP : ↥Pg, AddChar (kP PP.1) ℂ := fun PP => s.toMonoidHom.compAddChar (ψ PP.1)
  have hψ' : ∀ PP : ↥Pg, ψ' PP ≠ 1 := by
    intro PP h
    refine hψ PP.1 PP.2 ?_
    ext x
    apply s.injective
    have := DFunLike.congr_fun h x
    simpa [ψ'] using this
  let e : (P0 Pg r ψ).H ≃ ∀ PP : ↥Pg, unip (kP PP.1) r := piEquiv fun PP : ↥Pg => unip (kP PP.1) r
  let f : ∀ PP : ↥Pg, unip (kP PP.1) r → ℂ := fun PP h =>
    LinearMap.trace ℂ _ (parInd (F := kP PP.1) (b PP) (σ PP) h) *
      (((addCharHom (ψ' PP) (supHom (kP PP.1) r) h)⁻¹ : ℂˣ) : ℂ)
  have hf : ∀ PP : ↥Pg, ∑ h, f PP h = (Nat.card (unip (kP PP.1) r) : ℂ) := by
    intro PP
    letI : Fintype (kP PP.1) := Fintype.ofFinite _
    haveI := finite_parInd (b PP) (σ PP)
    have h1 := sum_unip_eq (ψ' PP) (parInd (F := kP PP.1) (b PP) (σ PP))
    rw [hL (kP PP.1) (ψ' PP) (hψ' PP) r (V PP) (b PP) (σ PP) (hσ PP), Nat.cast_one, mul_one] at h1
    exact h1
  have hterm : ∀ h : (P0 Pg r ψ).H, s (χ (h : G0 Pg r) * ((((P0 Pg r ψ).chi h)⁻¹ : Kˣ) : K)) = ∏ PP, f PP (e h PP) := by
    intro h
    have hchi : (P0 Pg r ψ).chi h = ∏ PP : ↥Pg, addCharHom (ψ PP.1) (supHom (kP PP.1) r) (e h PP) := by
      exact MonoidHom.finset_prod_apply (fun PP : ↥Pg => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp
        (LevelP.prj (fun PP : ↥Pg => unip (kP PP.1) r) PP)) Finset.univ h
    rw [map_mul, hs, hchi, Units.val_inv_eq_inv_val, map_inv₀, Units.coe_prod, map_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [f, Units.val_inv_eq_inv_val]
    rfl
  rw [map_sum, Finset.sum_congr rfl fun h _ => hterm h, map_natCast, Nat.card_congr e, Nat.card_pi, Nat.cast_prod,
    ← Finset.prod_congr rfl fun PP _ => hf PP, Fintype.prod_sum]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GlobalTheory.GenericProduct
end
end

section
section
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

theorem degenerateWhittakerDim_zero_eq_whittakerDim {F : Type} [Field F] {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) : whCut ψ τ 0 = whDim ψ τ := by
  have h : ∀ g : GL (Fin r) F, edgeSum (cutEdge 0) g = edgeSum supEdge g := by
    intro g
    unfold edgeSum
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      if_congr (by simp [cutEdge, supEdge]) rfl rfl
  unfold whCut whDim
  rw [show (fun g : GL (Fin r) F => ψ (edgeSum (cutEdge 0) g)) = fun g => ψ (edgeSum supEdge g) from
    funext fun g => by rw [h]]

theorem numBlockSetsOfTotalSize_zero_eq_one {r : ℕ} (b : Fin r → ℕ) : splitDoublingNBlock b 0 = 1 := by
  unfold splitDoublingNBlock
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext J
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (h1 hx)
    have : i ∈ Finset.univ.filter fun i => b i ∈ J := by simp [hx]
    rw [h2] at this
    simp at this
  · rintro rfl
    simp

theorem whDim_parInd_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1 := by
  intro F _ _ ψ hψ r V _ _ _ b σ hσ
  rw [← degenerateWhittakerDim_zero_eq_whittakerDim, GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal F ψ hψ r V b σ hσ 0 (Or.inr rfl), numBlockSetsOfTotalSize_zero_eq_one,
    GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal F ψ hψ r V b σ hσ]

end GlobalTheory.FinGL
end

open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1 := by
  atlas_forward_decl GlobalTheory.FinGL.whDim_parInd_eq_one
end

section
namespace GlobalTheory.GenericProduct

theorem oneGenericVector : OneGenericVector := GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one

theorem genericMultOne_holds : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne := genericMultOne oneGenericVector

theorem oneWhittakerVector_holds : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector :=
  GlobalTheory.CuspidalIdempotentCharacters.genericMultOne_iff.1 genericMultOne_holds

end GlobalTheory.GenericProduct
end

section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealOneVector

theorem isCuspIndProdChar_of_isProdCuspChar {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (s : K →+* ℂ)
    (Pg : Finset (Pl E)) (r : ℕ) (χ : G0 Pg r → K) (h : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar s Pg r χ) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar Pg r s χ := by
  obtain ⟨θ, hθ, hχ⟩ := h
  refine ⟨θ, fun PP => ?_, hχ⟩
  obtain ⟨d, b, σ, hσ, hx⟩ := hθ PP
  exact ⟨b, Fin d → ℂ, inferInstance, inferInstance, inferInstance, σ, hσ, hx⟩

theorem typeSum_base_eq_card : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → (∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g)) → ∀ [Fintype F.P0], ∀ χ ∈ A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hlev hind _ χ hχ
  have h := GlobalTheory.OneForm.oneVector_of_whittaker R F GlobalTheory.GenericProduct.oneWhittakerVector_holds hlev
    (fun χ hχ => isCuspIndProdChar_of_isProdCuspChar _ _ _ _ (hind χ hχ)) χ hχ
  rw [← Nat.card_eq_fintype_card, ← h, GlobalTheory.OneForm.typeSum]
  congr 1
  exact congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _)

end GlobalTheory.RealOneVector
end
end

section
noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues Formalism.MainNotions.PrimeDegreeVariant

section Conclusion

variable {K G : Type} [Field K] [Group G]

def ConclFinset (emb : K →+* ℂ) (Y : Set (G → ℂ)) : Prop :=
  ∃ Xg : Finset (G → K), (∀ ch, ch ∈ Y ↔ ∃ c ∈ Xg, ∀ t, ch t = emb (c t)) ∧ (∀ c ∈ Xg, IsAbsIrrChar c) ∧
    ∃ T : GoodSet K G, ∀ c, c ∈ Xg ↔ ∃ s : T.S, ∀ t, c t = LinearMap.trace K (T.W s) (T.tau s t)

def ConclRange (σ : K →+* ℂ) (Y : Set (G → ℂ)) : Prop :=
  (∀ Θ ∈ Y, ∃ ΘK : G → K, (∀ t, σ (ΘK t) = Θ t) ∧ IsAbsIrrChar ΘK) ∧
    ∃ T : GoodSet K G, (Set.range fun (s : T.S) (t : G) => σ (LinearMap.trace K (T.W s) (T.tau s t))) = Y

theorem ConclRange.mono {σ : K →+* ℂ} {Y Y' : Set (G → ℂ)} (h : ConclRange σ Y) (hY : Y' ⊆ Y) : ConclRange σ Y' := by
  classical
  obtain ⟨h1, T, rfl⟩ := h
  let T' : GoodSet K G :=
    { S := {s : T.S // (fun t => σ (LinearMap.trace K (T.W s) (T.tau s t))) ∈ Y'}
      W := fun s => T.W s.1
      tau := fun s => T.tau s.1
      irr := fun s => T.irr s.1
      inj := fun s s' e => Subtype.ext (T.inj e) }
  refine ⟨fun Θ hΘ => h1 Θ (hY hΘ), T', Set.ext fun Θ => ⟨?_, fun hΘ => ?_⟩⟩
  · rintro ⟨s, rfl⟩
    exact s.2
  · obtain ⟨s, rfl⟩ := hY hΘ
    exact ⟨⟨s, hΘ⟩, rfl⟩

end Conclusion

section OnePrime

variable {g : ℕ} [Fact g.Prime] {P : Type} {r m : ℕ}

def FullGood (ω : P → Fbar g →*₀ ℂ) (η : P → Fin m → (ZMod g)ˣ → ℂ) (τ : P → GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (f : P → (ZMod g)[X]) (c : P → Fin m → (ZMod g)ˣ), (∀ v j, IsTameLabel (ω v) (η v j) (c v j)) ∧
    IsGood r g f (fun v (js : Fin m × Bool) => if js.2 then c v js.1 else (c v js.1)⁻¹) ∧
    ∀ v, IndefiniteRowSideFullHecke.CuspValueComparison.IsTypeChar (ω v) (f v) (τ v)

def TorusGood (ι : P → (Fbar g)ˣ →* ℂˣ) (η : P → Fin m × Bool → (ZMod g)ˣ → ℂ)
    (τ : P → GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (f : P → (ZMod g)[X]) (c : P → Fin m × Bool → (ZMod g)ˣ), (∀ v j, IsCharLabel (ι v) (η v j) (c v j)) ∧
    IsGood r g f c ∧ ∀ v, IndefiniteRowSideFullHecke.TameCharacterTorusValues.IsTypeChar (ι v) (f v) (τ v)

theorem FullGood.change {ω ω' : P → Fbar g →*₀ ℂ} (hω : ∀ v, Function.Injective (ω v))
    (hω' : ∀ v, Function.Injective (ω' v)) {η : P → Fin m → (ZMod g)ˣ → ℂ} {τ : P → GL (Fin r) (ZMod g) → ℂ}
    (h : FullGood ω' η τ) : FullGood ω η τ := by
  obtain ⟨f, c, h1, h2, h3⟩ := h
  choose β hβ using fun v => exists_beta (hω v) (hω' v)
  choose f' hf' using fun v => exists_tr (β v) _ (f v) (h2.1 v).1 rfl
  choose c' hc' using fun v j => exists_unit_of_pow (y := β v (algebraMap (ZMod g) (Fbar g) (c v j)))
    (by rw [← map_pow, unit_pow, map_one])
  refine ⟨f', c', fun v j z => ?_, isGood_tr β hf' (fun v js => ?_) h2,
    fun v => isTypeChar_tr (hβ v) (h2.1 v).2.2 (hf' v) (h3 v)⟩
  · rw [h1 v j z, hβ v 1 one_pos _ _ (unit_pow _) (unit_pow _), hc']
  · split_ifs
    · exact hc' v js.1
    · rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, map_inv₀, hc']

theorem FullGood.reindex {P' : Type} (e : P' ≃ P) {ω : P → Fbar g →*₀ ℂ} {η : P → Fin m → (ZMod g)ˣ → ℂ}
    {τ : P → GL (Fin r) (ZMod g) → ℂ} (h : FullGood ω η τ) :
    FullGood (fun v => ω (e v)) (fun v => η (e v)) (fun v => τ (e v)) := by
  obtain ⟨f, c, h0, ⟨h1, h2, h3, h4, h5, v, h6⟩, h7⟩ := h
  refine ⟨fun v => f (e v), fun v => c (e v), fun v => h0 _, ⟨fun v => h1 _, fun v => h2 _,
    fun l hl hb v => h3 l hl hb _, fun l hl hb v => h4 l hl hb _, fun a ha hb => ?_, e.symm v, by simpa using h6⟩,
    fun v => h7 _⟩
  obtain ⟨v, hv⟩ := h5 a ha hb
  exact ⟨e.symm v, by simpa using hv⟩

theorem TorusGood.full (H : CuspidalCharacterFormula) {ι : P → (Fbar g)ˣ →* ℂˣ} {ω : P → Fbar g →*₀ ℂ}
    (hι : ∀ v, Function.Injective (ι v))
    (hω : ∀ v, Function.Injective (ω v)) {η : P → Fin m → (ZMod g)ˣ → ℂ} {η' : P → Fin m × Bool → (ZMod g)ˣ → ℂ}
    (ht : ∀ v j, η' v (j, true) = η v j) (hf : ∀ v j, η' v (j, false) = fun z => (η v j z)⁻¹)
    {τ : P → GL (Fin r) (ZMod g) → ℂ} (h : TorusGood ι η' τ) : FullGood ω η τ := by
  choose ω' hω' he using fun v => exists_ext (hι v)
  obtain ⟨f, c, h1, h2, h3⟩ := h
  have a1 : ∀ v j, IsTameLabel (ω' v) (η v j) (c v (j, true)) := fun v j => ht v j ▸ (label_iff (he v) _ _).1 (h1 v _)
  refine FullGood.change hω hω' ⟨f, fun v j => c v (j, true), a1, ?_,
    fun v => typeChar_full_of_torus H (hω' v) (he v) (h3 v)⟩
  convert h2 using 3 with v js
  obtain ⟨j, _ | _⟩ := js
  · exact label_unique (hω' v) (label_inv (a1 v j)) (hf v j ▸ (label_iff (he v) _ _).1 (h1 v _))
  · rfl

end OnePrime

section Global

variable {E : Type} [Field E] [NumberField E] [StarRing E] {gp : Fin 2 → ℕ} [∀ i, Fact (gp i).Prime]
  {pb : Fin 2 → 𝓞 E} {K : Type} [Field K]

def placeEquiv (hT : IsTypeDatum gp pb) (i : Fin 2) : PlacesOver pb i ≃ ↥(primesOf (pb i)) where
  toFun v := ⟨v.1.1, mem_primesOf.2 ⟨pb_ne_zero hT i, v.2⟩⟩
  invFun v := ⟨toBoth hT i v, (mem_primesOf.1 v.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def eta (hT : IsTypeDatum gp pb) (m : ℕ) (σ : K →+* ℂ) (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ) (i : Fin 2)
    (v : ↥(primesOf (pb i))) (j : Fin m) (z : (ZMod (gp i))ˣ) : ℂ :=
  σ (χ (j.val + 1) v.1 (Units.map ((resIso hT i v : ZMod (gp i) →+* kP v.1) : ZMod (gp i) →* kP v.1) z) : Kˣ)

end Global

end GlobalTheory.GoodCharsCompare
end
end

section
noncomputable section

namespace GlobalTheory.GoodFamily

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.BI GlobalTheory.GoodCharsCompare Formalism.MainNotions.PrimeDegreeVariant
open scoped MonoidAlgebra

section Characters

theorem irreducible_of_surjective {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [Nontrivial V]
    (ρ : Representation k G V) (h : Function.Surjective ρ.asAlgebraHom) : ρ.IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · refine Or.inr (Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun w _ => ?_))
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv0
    obtain ⟨a, ha⟩ := h (LinearMap.smulRight φ w)
    have hw : ρ.asAlgebraHom a v = w := by rw [ha]; simp [hφ]
    rw [← hw]
    clear hw ha
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, LinearMap.add_apply]; exact S.toSubmodule.add_mem hx hy
    | single t c =>
      rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
      exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule t hv)

theorem irreducible_extend (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] {G : Type} [Group G]
    [Finite G] {n : ℕ} (ρ : Representation K G (Fin n → K))
    (h : Module.finrank K (Representation.IntertwiningMap ρ ρ) = 1) : (extendScalarsRep K L ρ).IsIrreducible := by
  have h1 := pair_character_eq_finrank K L G _ _ ρ ρ
  have h2 := pair_character_eq_finrank L L G _ _ (extendScalarsRep K L ρ) (extendScalarsRep K L ρ)
  simp only [character_extendScalarsRep, Algebra.algebraMap_self, RingHom.id_apply] at h2
  rw [h1, h] at h2
  obtain ⟨h3, h4⟩ := GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one L G _ (extendScalarsRep K L ρ)
    (by exact_mod_cast h2.symm)
  exact irreducible_of_surjective _ h4

theorem norm_one_prod {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] {χ : ∀ i, G i → ℂ}
    (h : ∀ i, IsChar ℂ ℂ (χ i) ∧ pair (χ i) (χ i) = 1) :
    IsChar ℂ ℂ (fun t : ∀ i, G i => ∏ i, χ i (t i)) ∧
      pair (fun t : ∀ i, G i => ∏ i, χ i (t i)) (fun t => ∏ i, χ i (t i)) = 1 := by
  classical
  constructor
  · have : ∀ s : Finset ι, IsChar ℂ ℂ (fun t : ∀ i, G i => ∏ i ∈ s, χ i (t i)) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using isChar_one ℂ ℂ (∀ i, G i)
      | insert a s ha ih =>
        obtain ⟨n, ρ, hρ⟩ := (h a).1
        have h1 : IsChar ℂ ℂ (fun t : ∀ i, G i => χ a (t a)) := ⟨n, ρ.comp (Pi.evalMonoidHom G a), fun t => hρ (t a)⟩
        have := isChar_mul_complex h1 ih
        convert this using 1
        funext t
        rw [Finset.prod_insert ha]; rfl
    exact this _
  · letI : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
    have h2 : ∏ i, pair (χ i) (χ i) = 1 := Finset.prod_eq_one fun i _ => (h i).2
    rw [← h2]
    simp only [pair, finsum_eq_sum_of_fintype, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [Nat.card_pi, Nat.cast_prod, Fintype.prod_sum]
    simp only [Finset.prod_mul_distrib, Pi.inv_apply]

end Characters

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

variable {g : ℕ} [Fact g.Prime] {r : ℕ}

end Local

section Global

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

end Global

end GlobalTheory.GoodFamily
end
end

section
noncomputable section

namespace GlobalTheory.GoodTypeGeneric

section Groups

open GlobalTheory.BI Formalism.L2.DIV

theorem sum_character_eq_zero_iff {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∑ g, ρ.character g = 0 ↔ ∀ v, (∀ g, ρ g v = v) → v = 0 := by
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI := invertibleOfNonzero hc
  have h := ρ.card_inv_mul_sum_char_eq_finrank
  have e : ∑ g, ρ.character g = 0 ↔ ρ.invariants = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← Nat.cast_eq_zero (R := ℂ), ← h]
    simp [hc]
  rw [e, Submodule.eq_bot_iff]
  simp only [Representation.mem_invariants]

theorem character_coind_eq_ind {G V : Type} [Group G] [Finite G] (H : Subgroup G) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (σ : Representation ℂ H V) (g : G) :
    (Representation.coind H.subtype σ).character g = ind H σ.character g := by
  classical
  letI := Fintype.ofFinite G
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h := GlobalTheory.BadShare.trace_coind_mul_card H.subtype σ g
  unfold ind
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, eq_inv_mul_iff_mul_eq₀ hc, mul_comm]
  refine h.trans ?_
  rw [Finset.sum_comm, ← Equiv.sum_comp (Equiv.inv G)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have key : ∀ γ : H, H.subtype γ * (Equiv.inv G x * g) = Equiv.inv G x ↔ ((γ⁻¹ : H) : G) = x⁻¹ * g * x := by
    intro γ
    simp only [Subgroup.coe_subtype, Equiv.inv_apply, Subgroup.coe_inv]
    constructor
    · intro h
      have : (γ : G) = x⁻¹ * (x⁻¹ * g)⁻¹ := by rw [eq_mul_inv_iff_mul_eq, h]
      rw [this]; group
    · intro h
      have : (γ : G) = (x⁻¹ * g * x)⁻¹ := by rw [← h, inv_inv]
      rw [this]; group
  simp only [key]
  unfold ext0
  split_ifs with hx
  · rw [Finset.sum_eq_single (⟨_, hx⟩ : H)⁻¹]
    · rw [inv_inv, if_pos rfl]; rfl
    · intro γ _ hγ
      rw [if_neg]
      intro e
      exact hγ (inv_eq_iff_eq_inv.1 (Subtype.ext e))
    · simp
  · exact Finset.sum_eq_zero fun γ _ => if_neg fun e : ((γ⁻¹ : H) : G) = x⁻¹ * g * x => hx (e ▸ (γ⁻¹).2)

theorem isChar_prod {ι : Type} [Fintype ι] {G : Type} [Group G] {χ : ι → G → ℂ}
    (h : ∀ i, IsChar ℂ ℂ (χ i)) : IsChar ℂ ℂ (fun t => ∏ i, χ i t) := by
  classical
  have : ∀ s : Finset ι, IsChar ℂ ℂ (fun t => ∏ i ∈ s, χ i t) := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using isChar_one ℂ ℂ G
    | insert a s ha ih =>
      have := isChar_mul_complex (h a) ih
      convert this using 1
      funext t
      rw [Finset.prod_insert ha]; rfl
  exact this _

theorem isIrrChar_of_isAbsIrrChar {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ) {χ : G → K}
    (h : IsAbsIrrChar χ) : IsIrrChar ℂ ℂ fun g => emb (χ g) := by
  obtain ⟨n, ρ, hi, hρ⟩ := h
  letI : Algebra K ℂ := emb.toAlgebra
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let φ : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) ℂ := φ.toRingHom.toAlgebra
  have h1 := pair_self_of_isIrrChar_algClosed (AlgebraicClosure K) G _ ⟨n, ρ, hi, fun _ => rfl⟩
  rw [pair_character_eq_finrank] at h1
  refine ⟨n, extendScalarsRep _ ℂ ρ, GlobalTheory.GoodFamily.irreducible_extend _ ℂ ρ (by exact_mod_cast h1), fun g => ?_⟩
  rw [character_extendScalarsRep, hρ]
  exact (φ.commutes (χ g)).symm

theorem exists_eq_of_idemOf {K G ι : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Y : Finset ι) (t : ι → G → ℂ) (ht : ∀ i ∈ Y, IsChar ℂ ℂ (t i))
    (h : ∀ g, emb ((idemOf X).coeff g) = ∑ i ∈ Y, t i 1 / (Nat.card G : ℂ) * t i g⁻¹) {χ : G → K} (hχ : χ ∈ X) :
    ∃ i ∈ Y, ∀ g, emb (χ g) = t i g := by
  classical
  have h0 := congrArg emb (GlobalTheory.IdemChar.sum_coeff_idemOf_mul K G X hX χ hχ)
  have hirr := isIrrChar_of_isAbsIrrChar emb (hX χ hχ)
  have hne := GlobalTheory.FinGL.LeviChar.irrChar_one_ne_zero hirr
  obtain ⟨n, ρ, hi, hρ⟩ := hirr
  beta_reduce at hρ
  choose! m τ hτ using ht
  have e1 : ∀ (k : ℕ) (σ : Representation ℂ G (Fin k → ℂ)), algebraMap ℂ ℂ (σ.character 1) = k := by
    intro k σ; simp
  have h1 : (n : ℂ) = ∑ i ∈ Y, (m i : ℂ) * (Module.finrank ℂ ((τ i).IntertwiningMap ρ) : ℂ) := by
    rw [← e1 n ρ, ← hρ, ← h0, map_sum]
    simp only [map_mul, h, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← pair_character_eq_finrank ℂ ℂ, ← e1 _ (τ i), ← hτ i hi, pair, finsum_eq_sum_of_fintype, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hρ, ← hτ i hi]
    ring
  have h2 : n = ∑ i ∈ Y, m i * Module.finrank ℂ ((τ i).IntertwiningMap ρ) := by exact_mod_cast h1
  have hn : n ≠ 0 := by
    intro e
    apply hne
    rw [hρ, e1, e, Nat.cast_zero]
  obtain ⟨i, hiY, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (fun e => hn (h2.trans e))
  have hle : m i * Module.finrank ℂ ((τ i).IntertwiningMap ρ) ≤ n :=
    (Finset.single_le_sum (f := fun i => m i * Module.finrank ℂ ((τ i).IntertwiningMap ρ))
      (fun _ _ => Nat.zero_le _) hiY).trans h2.ge
  have hpos := Nat.pos_of_ne_zero (right_ne_zero_of_mul hi0)
  have hle' : m i ≤ n := le_trans (Nat.le_mul_of_pos_right _ hpos) hle
  haveI := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨f, hf⟩ := exists_ne (0 : (τ i).IntertwiningMap ρ)
  have hs : Function.Surjective f := (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  have hge : n ≤ m i := by
    simpa using LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hs
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) (by simp; omega)).2 hs
  refine ⟨i, hiY, fun g => ?_⟩
  rw [hρ, hτ i hiY, Representation.char_iso (f.ofBijective ⟨hinj, hs⟩)]

theorem chiIdem_mul_lvlIdem_ne_zero {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (P : Subgroup G) [Fintype P]
    (ψ : P →* Kˣ) {χ : G → K} (h1 : χ 1 ≠ 0) (h : ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) ≠ 0) :
    chiIdem χ * lvlIdem P ψ ≠ 0 := by
  classical
  intro h0
  have h2 := congrArg (fun a : MonoidAlgebra K G => a.coeff 1) h0
  have hG : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hP : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  simp only [lvlIdem, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply', MonoidAlgebra.coeff_mul_single_apply,
    coeff_chiIdem, one_mul, inv_inv, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h2
  apply h
  have h3 : χ 1 / (Fintype.card G : K) * (Nat.card P : K)⁻¹ ≠ 0 := mul_ne_zero (div_ne_zero h1 hG) (inv_ne_zero hP)
  apply mul_left_cancel₀ h3
  rw [mul_zero, ← h2, Finset.mul_sum]
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun x _ => ?_
  rw [map_inv]
  ring

end Groups

section Datum

open GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.FiniteGL GlobalTheory.Parabolic GlobalTheory.FinGL.LeviChar

variable {F : Type} [Field F] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

def blocksHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) :
    blockTri (κ := F) b →* ∀ a, GL (Fin (d a)) F :=
  Pi.monoidHom fun a => (leviBlock b (fun i => e ⟨a, i⟩)
    (fun _ _ hij => sigma_mk_injective (β := fun a => Fin (d a)) (e.injective hij)) (fun i j hij => by
      obtain ⟨⟨c, l⟩, rfl⟩ := e.surjective j
      obtain rfl : a = c := (he _ _).1 hij
      exact ⟨l, rfl⟩)).comp (leviProj b)

omit [Fintype ι] [DecidableEq ι] in
theorem blocksHom_apply (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (p : blockTri (κ := F) b) (a : ι) (i j : Fin (d a)) :
    (blocksHom b e he p a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩) :=
  if_pos ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl)

theorem blocksHom_diagHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (x : ∀ a, GL (Fin (d a)) F) : blocksHom b e he (diagHom b e he x) = x := by
  funext a
  apply Units.ext
  ext i j
  rw [blocksHom_apply, diagHom_apply, Matrix.blockDiagonal'_apply_eq]

theorem exists_isCuspDatum [Finite F] {b : Fin r → ℕ} (hb : Monotone b) (e : (Σ a, Fin (d a)) ≃ Fin r)
    (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) (χ : ∀ a, GL (Fin (d a)) F → ℂ) (hχ : ∀ a, IsIrrChar ℂ ℂ (χ a))
    (hc : ∀ a, ∀ c : Fin (d a) → ℕ, (∃ i j, c i ≠ c j) → ∑ᶠ u : unipRadical F c, χ a u = 0) :
    ∃ (n : ℕ) (σ : Representation ℂ (blockTri (κ := F) b) (Fin n → ℂ)), IsCuspDatum b σ ∧
      ∀ p, σ.character p = ∏ a, χ a (blocksHom b e he p a) := by
  classical
  obtain ⟨⟨n, ρ, hρ⟩, h1⟩ := GlobalTheory.GoodFamily.norm_one_prod (χ := χ) fun a =>
    ⟨let ⟨n, ρ, _, h⟩ := hχ a; ⟨n, ρ, h⟩, pair_self_of_isIrrChar_algClosed ℂ _ _ (hχ a)⟩
  rw [funext hρ, pair_character_eq_finrank] at h1
  obtain ⟨h3, h4⟩ := GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one ℂ _ _ ρ (by exact_mod_cast h1)
  refine ⟨n, ρ.comp (blocksHom b e he), ⟨hb, Transport.isIrreducible_comp ρ _
    (fun x => ⟨_, blocksHom_diagHom b e he x⟩) (GlobalTheory.GoodFamily.irreducible_of_surjective ρ h4), fun p hp => ?_, ?_⟩,
    fun p => (hρ _).symm⟩
  · have : blocksHom b e he p = 1 := by
      funext a
      apply Units.ext
      ext i j
      rw [blocksHom_apply, hp _ _ ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl)]
      simp [Matrix.one_apply]
    rw [MonoidHom.comp_apply, this, map_one]
  · rintro S ⟨i, j, hij, hi, hj⟩ y hy
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨a', j⟩, rfl⟩ := e.surjective j
    obtain rfl : a = a' := (he _ _).1 hij
    let c : Fin (d a) → ℕ := fun l => if e ⟨a, l⟩ ∈ S then 0 else 1
    letI : Fintype (unipRadical F c) := Fintype.ofFinite _
    let τ : Representation ℂ (unipRadical F c) (Fin n → ℂ) :=
      ρ.comp ((MonoidHom.mulSingle (fun a => GL (Fin (d a)) F) a).comp (unipRadical F c).subtype)
    refine (sum_character_eq_zero_iff τ).1 ?_ y fun u => ?_
    · have h5 := hc a c ⟨i, j, by simp [c, hi, hj]⟩
      rw [finsum_eq_sum_of_fintype] at h5
      have hv : ∀ u : unipRadical F c, τ.character u = χ a u * ∏ c' ∈ Finset.univ.erase a, χ c' 1 := by
        intro u
        refine (hρ (Pi.mulSingle a (u : GL (Fin (d a)) F))).symm.trans ?_
        beta_reduce
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Pi.mulSingle_eq_same]
        congr 1
        refine Finset.prod_congr rfl fun c' hc' => ?_
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hc')]
      simp only [hv]
      rw [← Finset.sum_mul, h5, zero_mul]
    · have h6 := hy (diagHom b e he (Pi.mulSingle a (u : GL (Fin (d a)) F))) ?_
      · rw [MonoidHom.comp_apply, blocksHom_diagHom] at h6
        exact h6
      · intro k l hkl
        obtain ⟨⟨a₁, k⟩, rfl⟩ := e.surjective k
        obtain ⟨⟨a₂, l⟩, rfl⟩ := e.surjective l
        rw [diagHom_apply] at hkl
        by_cases h12 : a₁ = a₂
        · subst h12
          rw [Matrix.blockDiagonal'_apply_eq] at hkl
          have h1 : (1 : Matrix (Fin r) (Fin r) F) (e ⟨a₁, k⟩) (e ⟨a₁, l⟩) = (1 : Matrix _ _ F) k l := by
            simp [Matrix.one_apply]
          rw [h1] at hkl
          by_cases ha : a₁ = a
          · subst ha
            rw [Pi.mulSingle_eq_same] at hkl
            have h7 : ¬ c l ≤ c k := fun h => hkl (sub_eq_zero.1 (mem_unipRadical.1 u.2 k l h))
            refine ⟨(he _ _).2 rfl, ?_⟩
            simp only [c] at h7
            split_ifs at h7 <;> simp_all
          · rw [Pi.mulSingle_eq_of_ne ha] at hkl
            exact absurd rfl hkl
        · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h12, Matrix.one_apply_ne
            (fun h => h12 (congrArg Sigma.fst (e.injective h)))] at hkl
          exact absurd rfl hkl

theorem irr_and_sum_of_isCusp {p n : ℕ} [Fact p.Prime] {χ : GlobalTheory.GLq.Gn p n → ℂ} (h : GlobalTheory.GLq.IsCusp χ) :
    IsIrrChar ℂ ℂ χ ∧ ∀ c : Fin n → ℕ, (∃ i j, c i ≠ c j) → ∑ᶠ u : unipRadical (ZMod p) c, χ u = 0 := by
  classical
  obtain ⟨-, ⟨V, hV, hχ⟩, hres⟩ := h
  obtain rfl : V.character = χ := funext hχ
  have hcusp : IsCuspidal V.ρ := by
    refine (isCuspidal_iff_twoBlocks _).2 fun a h0 ha v hv => ?_
    letI : Fintype (unipRadical (ZMod p) (twoBlocks n a)) := Fintype.ofFinite _
    refine (sum_character_eq_zero_iff (show Representation ℂ _ V from
      MonoidHom.comp V.ρ (unipRadical (ZMod p) (twoBlocks n a)).subtype)).1 ?_ v fun u => hv u u.2
    have h1 := hres a h0 ha
    unfold GlobalTheory.GLq.res at h1
    have hp : ((p : ℂ) ^ (a * (n - a)))⁻¹ ≠ 0 :=
      inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
    have h2 := (mul_eq_zero.1 h1).resolve_left hp
    rw [← Finset.sum_filter] at h2
    rw [← h2]
    refine (Finset.sum_subtype _ (fun u => ?_) V.character).symm
    rw [Finset.mem_filter, ← GlobalTheory.GreenExists.mem_grUnipBlock_iff ha, mem_unipRadical]
    simp only [Finset.mem_univ, true_and, Formalism.D.Classical.grUnipBlock, Set.mem_setOf_eq, twoBlocks, Matrix.sub_apply,
      sub_eq_zero, Matrix.one_apply]
    refine forall₂_congr fun i j => ?_
    by_cases h3 : (i : ℕ) < a <;> by_cases h4 : (j : ℕ) < a <;> simp [h3, h4] <;> omega
  constructor
  · refine (isChar_and_isIrrChar_of_rep ℂ ℂ _ V V.ρ).2 ?_
    have h1 := (FDRep.simple_iff_char_is_norm_one V).1 hV
    have h2 := pair_character_eq_finrank ℂ ℂ _ _ _ V.ρ V.ρ
    rw [pair, finsum_eq_sum_of_fintype] at h2
    have h3 : (Module.finrank ℂ (Representation.IntertwiningMap V.ρ V.ρ) : ℂ) = 1 := by
      rw [← h2, inv_mul_eq_one₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), ← h1]
      rfl
    obtain ⟨h3, h4⟩ := GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one ℂ _ _ V.ρ (by exact_mod_cast h3)
    exact GlobalTheory.GoodFamily.irreducible_of_surjective _ h4
  · intro c hc
    letI : Fintype (unipRadical (ZMod p) c) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype]
    exact (sum_character_eq_zero_iff (show Representation ℂ _ V from
      MonoidHom.comp V.ρ (unipRadical (ZMod p) c).subtype)).2 fun v hv =>
      fixed_eq_bot_iff.1 ((isCuspidal_iff_forall _).1 hcusp c hc) v fun u hu => hv ⟨u, hu⟩

end Datum

section Types

open GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.FiniteGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

theorem isCusp_cuspOn {s : SSParam p ℂ r} (hs : IsRegularParam s) (c : Cyc s.1) : GlobalTheory.GLq.IsCusp (cuspOn (s.2 c)) := by
  obtain ⟨L⟩ := GlobalTheory.GLq.LabelModel.inhab p
  obtain ⟨x, f, h⟩ := exists_labels p L r s
  exact (isCuspOf_cuspOn L (s.2 c) (x c) (cycLen_pos _ c) (h.1 c)
    (((GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.2 (h.regular_iff.1 hs)).1 c)).2.1

def cycEquiv (b : Fin r → Fin r) : (Σ c : Cyc b, Fin (cycLen b c)) ≃ Fin r :=
  Equiv.ofBijective (fun x => ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).1) (by
    have hf : ∀ x : Σ c : Cyc b, Fin (cycLen b c),
        b ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).1 = x.1.1 :=
      fun x => ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).2
    constructor
    · rintro ⟨c, i⟩ ⟨c', j⟩ h
      obtain rfl : c = c' := Subtype.ext ((hf ⟨c, i⟩).symm.trans ((congrArg b h).trans (hf ⟨c', j⟩)))
      obtain rfl : i = j := (Fintype.equivFin {a : Fin r // b a = c.1}).symm.injective (Subtype.ext h)
      rfl
    · intro i
      refine ⟨⟨⟨b i, i, rfl⟩, Fintype.equivFin _ ⟨i, rfl⟩⟩, ?_⟩
      simp only [Equiv.symm_apply_apply])

theorem cycEquiv_apply (b : Fin r → Fin r) (c : Cyc b) (i : {a : Fin r // b a = c.1}) :
    cycEquiv b ⟨c, Fintype.equivFin _ i⟩ = i.1 :=
  congrArg Subtype.val ((Fintype.equivFin {a : Fin r // b a = c.1}).symm_apply_apply i)

theorem apply_cycEquiv (b : Fin r → Fin r) (x : Σ c : Cyc b, Fin (cycLen b c)) : b (cycEquiv b x) = x.1.1 :=
  ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).2

theorem isCuspProdChar_typeChar {s : SSParam p ℂ r} (hs : IsRegularParam s) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (typeChar s) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let b₀ : Fin r → ℕ := fun i => (s.1 i : ℕ)
  let w := Tuple.sort b₀
  let e := (cycEquiv s.1).trans w.symm
  have he : ∀ x y, (b₀ ∘ w) (e x) = (b₀ ∘ w) (e y) ↔ x.1 = y.1 := by
    intro x y
    simp only [e, b₀, Function.comp, Equiv.trans_apply, Equiv.apply_symm_apply, apply_cycEquiv, Fin.val_inj,
      Subtype.ext_iff]
  obtain ⟨n, σ, hσ, hch⟩ := exists_isCuspDatum (F := ZMod p) (Tuple.monotone_sort b₀) e he (fun c => cuspOn (s.2 c))
    (fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).1) fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).2
  refine ⟨n, b₀ ∘ w, σ, hσ, fun x => ?_⟩
  have hm : ∀ z : GL (Fin r) (ZMod p),
      ((permGL (ZMod p) w * z * (permGL (ZMod p) w)⁻¹ : GL (Fin r) (ZMod p)) :
        Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1 ↔ z ∈ blockTri (κ := ZMod p) (b₀ ∘ w) := fun z =>
    Iff.trans Iff.rfl (conj_mem_blockTri (b := b₀))
  rw [character_coind_eq_ind]
  unfold typeChar ind
  congr 1
  · congr 2
    exact (Nat.card_congr ((MulAut.conj (permGL (ZMod p) w)).toEquiv.subtypeEquiv fun z => (hm z).symm)).symm
  · letI := Fintype.ofFinite (GL (Fin r) (ZMod p))
    rw [finsum_eq_sum_of_fintype]
    symm
    refine Fintype.sum_equiv (Equiv.mulRight (permGL (ZMod p) w)⁻¹) _ _ fun y => ?_
    have h1 : (Equiv.mulRight (permGL (ZMod p) w)⁻¹ y)⁻¹ * x * Equiv.mulRight (permGL (ZMod p) w)⁻¹ y =
        permGL (ZMod p) w * (y⁻¹ * x * y) * (permGL (ZMod p) w)⁻¹ := by
      simp only [Equiv.coe_mulRight]
      group
    rw [h1]
    unfold ext0
    by_cases hz : y⁻¹ * x * y ∈ blockTri (κ := ZMod p) (b₀ ∘ w)
    · rw [dif_pos hz, if_pos ((hm _).2 hz), hch]
      refine Finset.prod_congr rfl fun c _ => ?_
      unfold cuspOn
      congr 1
      ext i j
      rw [Matrix.submatrix_apply, blocksHom_apply]
      simp only [e, Equiv.trans_apply, cycEquiv_apply]
      rw [← conj_permGL_apply w, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl
    · rw [dif_neg hz, if_neg (mt (hm _).1 hz)]

theorem isChar_of_isCuspProdChar {θ : GL (Fin r) (ZMod p) → ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ) : IsChar ℂ ℂ θ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨n, b, σ, -, h⟩ := h
  rw [funext h]
  exact (isChar_and_isIrrChar_of_rep ℂ ℂ _ _ (parInd b σ)).1

end Types

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare

theorem isProdCuspChar_of_idemTie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hrec : R.grp_record) {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ}
    (hI : IdemTie D om) {χ : G → D.what₂.LL} (hχ : χ ∈ A.X) :
    CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) := by
  classical
  obtain ⟨eR, plg, iso, h1, -, h2⟩ := hrec
  let π : LevelCuspCharacters.LevelGroup D.host ≃* G0g D.nd :=
    MulEquiv.ofBijective (⟨⟨pull, rfl⟩, fun _ _ => rfl⟩ : LevelCuspCharacters.LevelGroup D.host →* G0g D.nd) pull_bijective
  let φ : G ≃* LevelCuspCharacters.LevelGroup D.host := eR.trans π.symm
  have hφ : ∀ g, pull (φ g) = eR g := fun g => π.apply_symm_apply (eR g)
  have hreg : ∀ s : ∀ v : LevelCuspCharacters.Sq D.host, LevelCuspCharacters.SSParam (D.host.g v.1) ℂ D.R.r, LevelCuspCharacters.IsGoodParam om s →
      ∀ v, CuspidalProductMultiplicity.IsCuspProdChar (LevelCuspCharacters.typeChar (s v)) := fun s hs v => isCuspProdChar_typeChar ((hs v.1).1 v.2)
  obtain ⟨τ, hτ, hχτ⟩ := exists_eq_of_idemOf D.what₂.embLL A.X hX (LevelCuspCharacters.goodTypes_finite (H := D.host) om).toFinset
    (fun τ g => τ (φ g)) (fun τ hτ => by
      obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
      letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
      refine isChar_prod (χ := fun v g => LevelCuspCharacters.typeChar (s v) (φ g v)) fun v => ?_
      obtain ⟨n, ρ, hρ⟩ := isChar_of_isCuspProdChar (hreg s hs v)
      exact ⟨n, ρ.comp ((Pi.evalMonoidHom _ v).comp φ.toMonoidHom), fun g => hρ _⟩) (fun g => by
      rw [h1, ← hφ, hI, Nat.card_congr φ.toEquiv]
      simp only [LevelCuspCharacters.goodIdem, LevelCuspCharacters.centralIdem, MonoidAlgebra.coeff_sum, Finset.sum_apply', map_one, map_inv]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [Finsupp.single_apply]) hχ
  obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
  let f : (Σ k : Fin 2, D.nd.PlG k) → G → ℂ := fun kv g => LevelCuspCharacters.typeChar (s (sqEquiv D kv)) (φ g (sqEquiv D kv))
  have key : ∀ PP : R.Pg, ∃ θ : GL (Fin D.R.r) (kP PP.1) → ℂ,
      @CuspidalProductMultiplicity.IsCuspProdChar (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) D.R.r θ ∧
        ∀ g, θ (R.eG g PP) = f (plg.symm PP) g := by
    intro PP
    obtain ⟨kv, rfl⟩ := plg.surjective PP
    letI := Ideal.Quotient.field (plg kv).1.asIdeal
    refine ⟨_, GlobalTheory.FinGL.Transport.isCuspProdChar_transport _ _ (iso kv) _ _ (hreg s hs (sqEquiv D kv)), fun g => ?_⟩
    rw [Equiv.symm_apply_apply, h2, ← hφ]
    exact congrArg _ ((GlobalTheory.FinGL.Transport.glEquiv (iso kv) D.R.r).symm_apply_apply _)
  choose θ hθ hθ' using key
  refine ⟨θ, hθ, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := R.eG.surjective x
  simp only [hθ', MulEquiv.symm_apply_apply, hχτ]
  letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
  exact (Fintype.prod_equiv (plg.symm.trans (sqEquiv D)) _ _ fun _ => rfl).symm

theorem chiIdem_mul_lvlIdem_base_ne_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → R.toLevCh.Is A.μ0 → R.IsGrp F →
    ∀ (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), GlobalTheory.DimPartsCompare.IdemTie D om →
    ∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk _ hG om hI χ hχ
  letI : Fintype F.P0 := Fintype.ofFinite _
  refine chiIdem_mul_lvlIdem_ne_zero _ _ (fun h => ?_) ?_
  · exact GlobalTheory.FinGL.LeviChar.irrChar_one_ne_zero (isIrrChar_of_isAbsIrrChar D.what₂.embLL (hOk.irr χ hχ))
      (by rw [h, map_zero])
  · rw [GlobalTheory.RealOneVector.typeSum_base_eq_card D G Pl0 T A Ks R F hG.levels
      (fun χ hχ => isProdCuspChar_of_idemTie R hOk.irr hG.record hI hχ) χ hχ]
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

end GlobalTheory.GoodTypeGeneric

end
end
