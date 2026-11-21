import Formalism.LocalRingCardinality.SpanPowerMembership.CodeRecordDiscriminantLevel
import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero
import Formalism.LocalRingCardinality.SpanPowerMembership.TrivialColumnsRamifiedTop
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowD
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.ND

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι]

abbrev stdHLat : HLat K where
  V := ι → K
  ι := ι
  b := Pi.basisFun K ι
  X := fun _ => 1
  L := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K ι))

theorem stdHLat_span : Submodule.span K ((stdHLat K ι).L : Set (stdHLat K ι).V) = ⊤ := by
  show Submodule.span K ((Submodule.span (𝓞 K) (Set.range (stdHLat K ι).b) : Submodule (𝓞 K) (ι → K)) : Set (ι → K)) = ⊤
  rw [Submodule.span_span_of_tower]
  exact (stdHLat K ι).b.span_eq

theorem stdHLat_good : (stdHLat K ι).Good := by
  refine ⟨fun _ => ?_, Submodule.fg_span (Set.finite_range _), stdHLat_span K ι⟩
  rw [show (stdHLat K ι).X _ = 1 from rfl, Matrix.det_one]
  exact isUnit_one


variable {K ι} (σ : K →+* ℂ)

abbrev FK (ι : Type) : Type := ι → Unit → ℂ

def eF (ι : Type) : (ι → ℂ) ≃ₗ[ℂ] FK ι where
  toFun f := fun c _ => f c
  invFun g := fun c => g c ()
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def slK : (ι → K) →ₛₗ[σ] FK ι where
  toFun x := fun c _ => σ (x c)
  map_add' x y := by funext _ _; simp
  map_smul' c x := by funext _ _; simp


theorem slK_basis : LinearIndependent ℂ (fun i => slK σ ((stdHLat K ι).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => slK σ ((stdHLat K ι).b i))) = ⊤ := by
  have h : (fun i => slK σ ((stdHLat K ι).b i)) = ((Pi.basisFun ℂ ι).map (eF ι)) := by
    funext i c y
    show σ ((stdHLat K ι).b i c) = (Pi.basisFun ℂ ι) i c
    show σ ((Pi.basisFun K ι) i c) = _
    rw [Pi.basisFun_apply, Pi.basisFun_apply]
    by_cases hc : c = i
    · subst hc; simp
    · simp [Pi.single_eq_of_ne hc]
  rw [h]
  exact ⟨((Pi.basisFun ℂ ι).map (eF ι)).linearIndependent, ((Pi.basisFun ℂ ι).map (eF ι)).span_eq⟩

theorem fcoord_std (v : InfinitePlace K) (x : ι → K) (i : ι) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun _ => (1 : Matrix ι ι ℂ)) v x i = v.embedding (x i) := by
  classical
  simp [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt]

theorem maj_std (x : ι → K) :
    (Formalism.HermitianLatticesTheory.majAt (stdHLat K ι).b (stdHLat K ι).X (InfinitePlace.mk σ) x x).re = ∑ c, ‖σ (x c)‖ ^ 2 := by
  show (∑ i : ι, star (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun _ => (1 : Matrix ι ι ℂ)) _ x i) *
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun _ => (1 : Matrix ι ι ℂ)) _ x i).re = _
  simp only [fcoord_std, Complex.star_def]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, InfinitePlace.norm_embedding_eq,
    InfinitePlace.apply]


end Std

section Member

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg)

abbrev chainN : ColumnChain R Tau hc :=
  { chain3 hc K with
    Y := fun _ => Unit
    de := fun _ _ _ => 1
    de_ne := fun _ _ _ => one_ne_zero
    unf := fun _ _ _ => LinearMap.id }

instance (i : ℕ) : Fintype (K.cls i) := K.clsFin i

instance (i : ℕ) : DecidableEq (K.cls i) := Classical.decEq _

instance (i : ℕ) (c : K.cls i) : Group (K.stab i c) := K.stabGrp i c

variable (T : ℕ) [hT : Fact T.Prime]

def rhoN (ι : Type) : (ZMod T)ˣ →* (FK ι →ₗ[ℂ] FK ι) :=
  (algebraMap ℂ (Module.End ℂ (FK ι))).toMonoidHom.comp ((Units.coeHom ℂ).comp (chiU T))

theorem rhoN_apply (ι : Type) (a : (ZMod T)ˣ) (φ : FK ι) : rhoN T ι a φ = ((chiU T a : ℂˣ) : ℂ) • φ := rfl

abbrev atTN (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) :
    ColumnsAtT R (chainN hc K) :=
  haveI : NeZero T := ⟨hT.out.ne_zero⟩
  { T := T
    T_prime := hT.out
    vT := Fin R.f
    card_vT := Fintype.card_fin _
    Fv := fun _ => ZMod T
    card_Fv := fun _ => ZMod.card T
    psiT := fun _ => ZMod.stdAddChar
    psiT_ne := fun _ => by
      have := ZMod.isPrimitive_stdAddChar T (one_ne_zero (α := ZMod T))
      rwa [AddChar.mulShift_one] at this
    rhoT := fun _ => rhoN T (K.cls 0)
    Mu0 := ⊤
    Mu0_fd := inferInstanceAs (FiniteDimensional ℂ (⊤ : Submodule ℂ (FK (K.cls 0))))
    Mu0_stable := fun _ _ => le_top
    duStar := du
    duStar_pos := hdu
    Dstar := Dst
    Dstar_pos := hD
    GamP := Gam
    one_lt_gammaP := hG }

variable (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)

theorem atTN_Nm (hT2 : T ≠ 2) (v : (atTN hc K T Dst hD du hdu Gam hG).vT) :
    (atTN hc K T Dst hD du hdu Gam hG).Nm v = 0 := by
  refine LinearMap.ext fun φ => ?_
  show (∑ c : (ZMod T)ˣ, rhoN T (K.cls 0) c) φ = 0
  rw [LinearMap.sum_apply]
  simp only [rhoN_apply]
  rw [← Finset.sum_smul, chiU_sum T hT2, zero_smul]

theorem atTN_Mram (hT2 : T ≠ 2) : (atTN hc K T Dst hD du hdu Gam hG).Mram = ⊤ := by
  unfold ColumnsAtT.Mram
  simp only [atTN_Nm hc K T Dst hD du hdu Gam hG hT2, LinearMap.ker_zero, iInf_top, inf_top_eq]

theorem finrank_FK (ι : Type) [Fintype ι] : Module.finrank ℂ (FK ι) = Fintype.card ι :=
  ((eF ι).finrank_eq).symm.trans (Module.finrank_fintype_fun_eq_card ℂ)

theorem atTN_rank : Module.finrank ℂ (atTN hc K T Dst hD du hdu Gam hG).Mu0 = Fintype.card (K.cls 0) := by
  show Module.finrank ℂ (⊤ : Submodule ℂ (FK (K.cls 0))) = _
  rw [finrank_top, finrank_FK]

theorem atTN_du (hT2 : T ≠ 2) : (atTN hc K T Dst hD du hdu Gam hG).du = Fintype.card (K.cls 0) := by
  unfold ColumnsAtT.du
  rw [atTN_Mram hc K T Dst hD du hdu Gam hG hT2, finrank_top, finrank_FK]

abbrev periodN (Mt : Type) [AddCommGroup Mt] [Module ℂ Mt] (per : FK (K.cls R.m) →ₗ[ℂ] Mt →ₗ[ℂ] ℂ) :
    PeriodMap R (chainN hc K) where
  Mt := Mt
  Wz := FK (K.cls R.m)
  evz := LinearMap.id
  Wrow := FK (K.cls R.m)
  lowerMap := LinearMap.id
  period := per

end Member

section Forms

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg) (T : ℕ) [hT : Fact T.Prime]
  (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (Mt : Type) [AddCommGroup Mt] [Module ℂ Mt] (per : FK (K.cls R.m) →ₗ[ℂ] Mt →ₗ[ℂ] ℂ)
  {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) (hTau : Fintype.card Tau = R.f)

theorem card_stab_ne (i : ℕ) (c : K.cls i) : ((Nat.card (K.stab i c) : ℕ) : ℂ) ≠ 0 := by
  have := K.stabFin i c
  have := K.stabGrp i c
  exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'

def ipS (ι : Type) [Fintype ι] : FK ι →ₗ⋆[ℂ] FK ι →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun f g => ∑ c, starRingEnd ℂ (f c ()) * g c ())
    (by intros; simp [add_mul, Finset.sum_add_distrib]) (by intros; simp [mul_assoc, Finset.mul_sum])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring)

theorem ipS_apply (ι : Type) [Fintype ι] (f g : FK ι) : ipS ι f g = ∑ c, starRingEnd ℂ (f c ()) * g c () := rfl

def formsN : MemberForms LL embLL Pl Tau hc (chainN hc K) (atTN hc K T Dst hD du hdu Gam hG)
    (periodN hc K Mt per) where
  lv := fun i _ _ => Fin (R.N i) → ZMod T
  lv_rank := fun _ _ _ => Module.finrank_fin_fun (ZMod T)
  fv := fun i _ _ => LinearMap.proj ⟨0, R.N_pos i⟩
  fv_ne := fun i _ _ h => by
    have := LinearMap.congr_fun h (Pi.single ⟨0, R.N_pos i⟩ 1)
    simp at this
  up := fun _ _ c _ => c
  upT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  lk := fun i _ _ => Fin (R.N i) → ZMod T
  lk_rank := fun _ _ _ => Module.finrank_fin_fun (ZMod T)
  te := fun i _ _ => Pi.single ⟨0, R.N_pos i⟩ 1
  te_ne := fun i _ _ h => by
    have := congrFun h ⟨0, R.N_pos i⟩
    simp at this
  dn := fun _ _ c _ => c
  dnT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  dil := fun _ _ _ c => c
  dilT := fun _ _ a _ => LinearEquiv.smulOfUnit (chiU T a)
  dil_one := fun _ _ _ => rfl
  dil_mul := fun _ _ _ _ _ => rfl
  dil_fv := fun i _ a _ => ⟨LinearEquiv.smulOfUnit a⁻¹, by
    refine LinearMap.ext fun x => ?_
    show x ⟨0, R.N_pos i⟩ = (a : ZMod T) * ((a⁻¹ : (ZMod T)ˣ) • x) ⟨0, R.N_pos i⟩
    rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]⟩
  dil_stab := fun _ _ _ _ => rfl
  rhoT_dil := fun _ _ _ _ => rfl
  tauOf := fun _ => Fintype.equivOfCardEq (by rw [(atTN hc K T Dst hD du hdu Gam hG).card_vT, hTau])
  seenP := fun _ => true
  lam := fun j τ => lamOf (hc τ) j
  lam_eq := fun j hj τ i => lamOf_eq (hc τ) j hj i
  sg := fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
  Fi := fun _ => ⊤
  Fi_zero := rfl
  ipV := fun i c => ((Nat.card (K.stab i c) : ℕ) : ℂ) • ip1
  lat := fun i => stdHLat LL (K.cls i)
  lat_good := fun i => stdHLat_good LL (K.cls i)
  emb := fun _ => slK embLL
  emb_basis := fun _ => slK_basis embLL
  emb_norm := fun i x => by
    rw [maj_std, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = ((((Nat.card (K.stab i c) : ℕ) : ℂ))⁻¹ * (((Nat.card (K.stab i c) : ℕ) : ℂ) *
      (starRingEnd ℂ (embLL (x c)) * embLL (x c)))).re
    rw [inv_mul_cancel_left₀ (card_stab_ne K i c), Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rhoT_lat := fun _ a x hx => by
    rcases chiU_pm T a with h | h
    · exact ⟨x, hx, by
        show slK embLL x = ((chiU T a : ℂˣ) : ℂ) • slK embLL x
        rw [h, one_smul]⟩
    · exact ⟨-x, neg_mem hx, by
        show slK embLL (-x) = ((chiU T a : ℂˣ) : ℂ) • slK embLL x
        rw [h, map_neg, neg_one_smul]⟩
  Bw := fun _ _ _ => ⊤
  Bw_span := fun _ _ _ => by simp
  clsP := K.cls R.m
  stabilizer₂ := K.stab R.m
  stabPGrp := K.stabGrp R.m
  stabPFin := K.stabFin R.m
  til := id
  stabMap := fun c => MonoidHom.id (K.stab R.m c)
  stabMap_inj := fun _ _ _ h => h
  evz_til := fun φ ψ h => by
    have : φ = ψ := funext h
    rw [this]
  ptC := ⊤
  ipP := ipS (K.cls R.m)
  ptLat := stdHLat LL (K.cls R.m)
  ptLat_good := stdHLat_good LL (K.cls R.m)
  ptEmb := slK embLL
  ptEmb_basis := slK_basis embLL
  ptEmb_norm := fun x => by
    rw [maj_std, ipS_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = (starRingEnd ℂ (embLL (x c)) * embLL (x c)).re
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  beOn := fun _ => 0
  beOn_nonneg := fun _ => le_rfl
  thFree := fun _ _ _ _ => 1
  thFree_nonneg := fun _ _ _ _ => zero_le_one

theorem formsN_ipC (i : ℕ) (φ ψ : FK (K.cls i)) :
    (formsN hc K T Dst hD du hdu Gam hG Mt per embLL Pl hTau).ipC i φ ψ = ipS (K.cls i) φ ψ := by
  show ∑ c, (((Nat.card (K.stab i c) : ℕ) : ℂ))⁻¹ * (((Nat.card (K.stab i c) : ℕ) : ℂ) *
      (starRingEnd ℂ (φ c ()) * ψ c ())) = _
  rw [ipS_apply]
  exact Finset.sum_congr rfl fun c _ => inv_mul_cancel_left₀ (card_stab_ne K i c) _

theorem formsN_ramSub (hT2 : T ≠ 2) :
    (formsN hc K T Dst hD du hdu Gam hG Mt per embLL Pl hTau).ramSub = ⊤ := by
  unfold MemberForms.ramSub
  rw [atTN_Mram hc K T Dst hD du hdu Gam hG hT2]
  rfl

end Forms

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.ND

section

variable (ι : Type) [Fintype ι] [DecidableEq ι]

abbrev MuN : Type := EuclideanSpace ℂ ι

def eE : MuN ι ≃ₗ[ℂ] FK ι := (EuclideanSpace.equiv ι ℂ).toLinearEquiv.trans (eF ι)

theorem eE_apply (φ : MuN ι) (c : ι) (y : Unit) : eE ι φ c y = φ c := rfl

theorem inner_eE (φ ψ : MuN ι) : inner ℂ φ ψ = ipS ι (eE ι φ) (eE ι ψ) := by
  rw [ipS_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [eE_apply, eE_apply, RCLike.inner_apply]
  exact mul_comm _ _

variable {ι} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (σ : LL →+* ℂ)

def jE : (ι → LL) →ₛₗ[σ] MuN ι where
  toFun x := (eE ι).symm (slK σ x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c x := by rw [LinearMap.map_smulₛₗ, map_smul]

theorem eE_jE (x : ι → LL) : eE ι (jE σ x) = slK σ x := (eE ι).apply_symm_apply _

theorem jE_basis : LinearIndependent ℂ (fun i => jE σ ((stdHLat LL ι).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jE σ ((stdHLat LL ι).b i))) = ⊤ := by
  obtain ⟨h1, h2⟩ := slK_basis (ι := ι) σ
  have h : (fun i => jE σ ((stdHLat LL ι).b i)) = (eE ι).symm ∘ fun i => slK σ ((stdHLat LL ι).b i) := rfl
  rw [h]
  refine ⟨h1.map' _ (LinearEquiv.ker _), ?_⟩
  rw [Set.range_comp]
  have h3 := Submodule.map_span (eE ι).symm.toLinearMap (Set.range fun i => slK σ ((stdHLat LL ι).b i))
  rw [h2, Submodule.map_top, LinearEquiv.range] at h3
  exact h3.symm


end

section Rec

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg) (T : ℕ) [hT : Fact T.Prime]
  (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)

def eMuN (hT2 : T ≠ 2) : MuN (K.cls 0) ≃ₗ[ℂ] (atTN hc K T Dst hD du hdu Gam hG).Mram :=
  (eE (K.cls 0)).trans (LinearEquiv.ofTop _ (atTN_Mram hc K T Dst hD du hdu Gam hG hT2)).symm


def eCuN : MuN (K.cls 0) ≃ₗ[ℂ] (atTN hc K T Dst hD du hdu Gam hG).Mu0 :=
  (eE (K.cls 0)).trans (LinearEquiv.ofTop (⊤ : Submodule ℂ (FK (K.cls 0))) rfl).symm


end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

def padConj {d n : ℕ} (h : d ≤ n) : En d →ₗᵢ⋆[ℂ] En n where
  toFun x := WithLp.toLp 2 fun i => if hi : (i : ℕ) < d then starRingEnd ℂ (x ⟨i, hi⟩) else 0
  map_add' x y := by
    ext i
    by_cases hi : (i : ℕ) < d <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : (i : ℕ) < d <;> simp [hi]
  norm_map' x := by
    show ‖WithLp.toLp 2 fun i : Fin n => if hi : (i : ℕ) < d then starRingEnd ℂ (x ⟨i, hi⟩) else 0‖ = ‖x‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun i hi => ?_)
      (fun k => ?_)).symm
    · have : ¬ (i : ℕ) < d := fun hlt => hi ⟨⟨i, hlt⟩, rfl⟩
      simp [this]
    · simp

section Chain

theorem chainOpM_add {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (f g : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (f + g) = Formalism.ThetaLiftIndependence.chainOpM w Km m f + Formalism.ThetaLiftIndependence.chainOpM w Km m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext j
    simp only [Formalism.ThetaLiftIndependence.kerOpM, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

theorem chainOpM_smul {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (c : Rg) (f : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f) = c • Formalism.ThetaLiftIndependence.chainOpM w Km m f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext j
    simp only [Formalism.ThetaLiftIndependence.kerOpM, Pi.smul_apply, map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact smul_comm _ _ _

theorem col_add {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (f g : C.cls 0 → C.Y 0 → ℂ) : C.col (f + g) = C.col f + C.col g := chainOpM_add C.wt C.Kmap R.m f g

theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (c : ℂ) (f : C.cls 0 → C.Y 0 → ℂ) : C.col (c • f) = c • C.col f := chainOpM_smul C.wt C.Kmap R.m c f

end Chain

abbrev divN (F : Type) [Field F] [NumberField F] [StarRing F] {W : Type} [Fintype W] (K : W → ClsPkg) (etaF : ℝ)
    (hv : W → ℝ) (d Dall : ℕ) (NuL : ∀ u : W, Submodule (𝓞 F) ((K u).cls 0 → F)) : DivData F W where
  RR := stdH F d
  Nu := fun u => { stdHLat F ((K u).cls 0) with L := NuL u }
  Bk := fun _ => 0
  h := hv
  HH := sFrame (fun u : W => { stdHLat F ((K u).cls 0) with L := NuL u }) hv + (stdH F d).muMax
  HH_ge := le_refl _
  etaF := etaF
  Dall := Dall
  delP := 1 - (d : ℝ) / Dall
  delP_le_one := by
    have : (0 : ℝ) ≤ (d : ℝ) / Dall := by positivity
    linarith

section Record

variable {R : Ranks} (H : Host R)

section Per

variable {W : Type} (hcW : W → Tau2 R → HCParam R) (K : W → ClsPkg) (d : ℕ)
  (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)

def perN (u : W) (μ : Bool) (φ : MuN ((K u).cls 0)) (F : En d) : ℂ :=
  (periodN (hcW u) (K u) (En d) (per u μ)).PtilCol (eE _ φ) F

theorem perN_linL (u : W) (μ : Bool) (F : En d) : IsLinearMap ℂ (fun φ => perN hcW K d per u μ φ F) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩
  · unfold perN Formalism.BasicNotions.PeriodMap.PtilCol Formalism.BasicNotions.PeriodMap.Ptil
    rw [map_add, col_add, map_add, map_add, map_add, LinearMap.add_apply]
  · unfold perN Formalism.BasicNotions.PeriodMap.PtilCol Formalism.BasicNotions.PeriodMap.Ptil
    rw [map_smul, col_smul, map_smul, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem perN_linR (u : W) (μ : Bool) (φ : MuN ((K u).cls 0)) : IsLinearMap ℂ (fun F => perN hcW K d per u μ φ F) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩
  · unfold perN Formalism.BasicNotions.PeriodMap.PtilCol Formalism.BasicNotions.PeriodMap.Ptil
    rw [map_add]
  · unfold perN Formalism.BasicNotions.PeriodMap.PtilCol Formalism.BasicNotions.PeriodMap.Ptil
    rw [map_smul, smul_eq_mul]

end Per

abbrev rowsHN {W : Type} (hcW : W → Tau2 R → HCParam R) (K : W → ClsPkg) (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
    (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
    (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)
    (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)
    (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ) : Rows.Data R :=
  rowsN H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) (Tau2 R) (card_realPlaces_eq_degree R) Dst (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H) kb ks tw htw W (fun u => (K u).cls 0) d Dall d0 hd FT ft ft0
    (perN hcW K d per) (fun _ _ => 0) (fun _ _ => le_refl _)

theorem nHypN {W : Type} (hcW : W → Tau2 R → HCParam R) (K : W → ClsPkg) (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
    (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
    (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)
    (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)
    (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) where
  hsha := fun p _ e _ _ => shaExample_eq H p e
  hcard := rfl
  hg := hg

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

abbrev sDataN (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) (K : W → ClsPkg)
    (Dall : ℕ) : Formalism.MainNotions.S.Draft.SData R H.F H.E (conjF H) W (Tau2 R) hcW :=
  { sData5 H hcW Del hDel hgap lt hlt hlet cdS hcdS hg ht with
    HH := En Dall
    hhN := inferInstance
    hhI := inferInstance
    hhF := inferInstance
    Cu := fun u => MuN ((K u).cls 0)
    cuN := fun _ => inferInstance
    cuI := fun _ => inferInstance
    cuF := fun _ => inferInstance
    Pu := fun _ => 0
    aTerm := fun _ _ t => t.elim }

abbrev memC (K : W → ClsPkg) (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ)
    (hdu : ∀ u, 0 < du u) (Gam : ℝ) (hG : 1 < Gam) (d : ℕ)
    (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ) (u : W) : Member R (Tau2 R) (hcW u) :=
  ⟨chainN (hcW u) (K u), atTN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG,
    periodN (hcW u) (K u) (En d) (per u false)⟩

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

def hostLevelRecord : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R
    host := H
    sp := hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)
    what₂ := rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per
    eTau := Equiv.refl _
    hc := hcW u0
    wordFin := inferInstanceAs (Fintype W)
    u₀ := u0
    hcW := hcW
    hcW_base := rfl
    hcW_v := hv0
    hcW_b := hb0
    hcW_e := he0
    hcW_first := hf0
    hcW_last := hl0
    mem := fun u => memC hcW K T Dst hD du hdu Gam hG d per u
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := divN H.E K etaF hv d Dall NuL
    div_good := ⟨stdH_frames H.E d, fun u => (stdHLat_good H.E ((K u).cls 0)).1⟩
    embE := RingHom.id _
    embE_φ₀ := rfl
    conjF := conjF H
    conjF_eq := conjF_apply H
    embE_conj := fun x => (star_eq_conj H x).symm
    LL0 := ⊤
    hostField_le_fixedField := fun _ => IntermediateField.mem_top
    O_contains := fun x => ⟨x, rfl⟩
    plEq := Equiv.refl _
    val_eq := placesOf_val_eq H.E
    ram_eq := placesOf_ram_eq H.E
    conj_val := placesOf_conj_val H.E
    T_level := hlev
    T_norm := fun u => ⟨pz u, hK u, hpz u, hcong u⟩
    sp_T := rfl
    cOf := fun u => (pz u0 : H.E) / (pz u : H.E)
    cOf_ne := fun u => div_ne_zero (pz_ne H (hpz u0)) (pz_ne H (hpz u))
    cOf_eq := fun u => norm_quotient_mul_conj H (hpz u0) (hpz u)
    T_win := hwin
    GamP_eq := fun _ => rfl
    T_ne_pde := hpde
    Dstar_eq := fun _ => rfl
    clsLat := lat
    clsLat_lat := hlat
    eMu := fun u => eMuN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (hT2 u)
    eMt := fun _ => LinearEquiv.refl ℂ (En d)
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun u F => perN_linL hcW K d per u false F
    Bu_linR := fun u φ => perN_linR hcW K d per u false φ
    chTw := fun u _ => (memC hcW K T Dst hD du hdu Gam hG d per u).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun u μ => periodN (hcW u) (K u) (En d) (per u μ)
    eMtTw := fun _ _ => LinearEquiv.refl ℂ (En d)
    perCol_tie := fun _ _ _ _ _ => rfl
    vol := vol
    vol_pos := hvol
    O_int := fun y => RingOfIntegers.isIntegral_coe y
    jEE := jB H.φ₀ (eb d)
    jEE_basis := jB_basis H.φ₀ (eb d)
    jN := fun _ => jE H.φ₀
    jN_basis := fun _ => jE_basis H.φ₀
    Dall_eq := rfl
    delP_eq := rfl
    Dt := ℂˣ
    detCls := fun _ _ _ => 1
    muTil := fun _ => 1
    chiD := MonoidHom.id _
    UO := ⊥
    chiD_UO := fun _ hx => Subgroup.mem_bot.mp hx
    e1Dt := exampleInverseEmbeddingProduct H (Equiv.refl (Tau2 R))
    rest_detCharacter_on_unitary_eq := exampleCharacter_unitary_product H (Equiv.refl (Tau2 R))
    relDet := fun N L L' => QuotientGroup.mk (relDetExample H (Equiv.refl (Tau2 R)) N L L')
    relDet_self := fun N L => congrArg QuotientGroup.mk (relDetExample_self H (Equiv.refl (Tau2 R)) N L)
    relDet_mul := fun N L L' L'' =>
      congrArg QuotientGroup.mk (relDetExample_mul H (Equiv.refl (Tau2 R)) N L L' L'')
    relDet_smul := fun N L L' γ h => congrArg _ (relDetExample_smul H (Equiv.refl (Tau2 R)) N L L' γ h)
    rhoDet_eq_inv_muTilde_chiD_pow := fun _ _ _ => by simp
    rhoDetPrime_eq_muTilde_mul_chi_pow := fun _ _ _ => by simp
    dsig := dsg
    dsig_pos := hdsg
    s := sDataN H hcW Del hDel hgap lt hlt hlet cdS hcdS hg ht K Dall
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := finrank_euclideanSpace_fin
    s_Cu := fun u => eCuN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG
    s_PlF := Equiv.refl _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndG H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg)
    ntw := ntwL H ⊤ (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb)
    naut := nautL H (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb)
    nbc := nbcL H (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb)
    nexp := nexpL H ⊤ (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb)
      (fun g => ((qcL H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) g : ℚ) : ↥(⊤ : IntermediateField ℚ H.E)))
    ntypes := ntypesL H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) ht G.tame
    nStage_trivialCharacter_compat := ntypesL_E0Tie H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) ht G.tame (fun _ => rfl) (fun _ _ => rfl)
    nth := nthL H ⊤ (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb) _
    nbr := fun i => Empty.elim i
    self_good := fun i => Empty.elim i
    ntwbr := fun i => Empty.elim i
    nbr_ind := fun i => Empty.elim i
    ntwbr_ind := fun i => Empty.elim i
    loc_tie := fun i => Empty.elim i
    bc_tie := fun i => Empty.elim i
    rbar_tie := fun i => Empty.elim i
    mtpar_tie := fun i => Empty.elim i
    jetW := fun i => Empty.elim i
    jetW_l := fun i => Empty.elim i
    jetTau := fun i => Empty.elim i
    jetW1 := fun i => Empty.elim i
    resChar_thetaJetPlaceDegOne := fun i => Empty.elim i
    jetTau1 := fun i => Empty.elim i
    nStage_trivialCharacter_coeff_eq := fun g => labelIdempotent_baseField H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) ⊤ ht G.tame g
    Z_tie := l_Z_tie H _ _ _ _
    Zgood_tie := l_Zgood_tie H _ _ _ _
    etaJ_tie := l_etaJ_tie H _ _ _ _ (fun _ _ => rfl)
    fm := fun u => formsN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u false) H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R)
    eMu_isom := fun u φ ψ => (inner_eE _ φ ψ).trans
      (formsN_ipC (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u false) H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R) 0 _ _).symm
    nuIn := fun _ => LinearMap.id
    nuIn_inj := fun _ => Function.injective_id
    nuIn_range := fun u => LinearMap.range_id.trans
      (formsN_ramSub (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u false) H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R) (hT2 u)).symm
    nuIn_jN := fun _ x => eE_jE H.φ₀ x
    nuIn_norm := fun _ _ _ => rfl
    jEE_norm := jB_norm H.φ₀ (eb d)
    sEE := padConj hd
    s_Cu_isom := fun u φ ψ => (inner_eE _ φ ψ).trans
      (formsN_ipC (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u false) H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R) 0 _ _).symm
    cd := G.cd
    jet := jetToy R H
    jetU := fun i => Empty.elim i
    jetL := fun i => Empty.elim i
    jetL' := fun i => Empty.elim i
    jetU1 := fun i => Empty.elim i
    jetL1 := fun i => Empty.elim i
    jetL1' := fun i => Empty.elim i
    gx := gxExample _ _
    gat := gat
    gat_d := fun u w h => (hgat u w h).trans (atTN_rank (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG).symm
    Y_sigval := spaces_signature_eq R _ _ _ _ _ _ _ }

end Record

end Formalism.BasicNotions.Examples₂.NZ
end
end
