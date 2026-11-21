import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowA
import Formalism.LocalRingCardinality.DataBu

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

section Gen

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem baseSubspace_top_of_identity {μ} (he : S.eOp μ = LinearMap.id) : S.V0 μ = ⊤ := by
  unfold RowSide.V0; rw [he]; exact LinearMap.range_id

theorem Usp_bot {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) : S.Usp μ = ⊥ := by
  unfold RowSide.Usp; rw [baseSubspace_top_of_identity S he, LinearMap.ker_eq_bot.mpr hi, inf_bot_eq]

theorem Qsp_top {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) : S.Qsp μ = ⊤ := by
  unfold RowSide.Qsp; rw [baseSubspace_top_of_identity S he, Usp_bot S he hi, Submodule.bot_orthogonal_eq_top, inf_top_eq]

theorem LamSet_eq {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) :
    S.LamSet μ = (S.Mtilde μ).carrier := by
  unfold RowSide.LamSet
  have hp : ∀ x, (S.Qsp μ).starProjection x = x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (by rw [Qsp_top S he hi]; trivial)
  rw [baseSubspace_top_of_identity S he]
  ext x
  simp [hp]

theorem RRset_eq {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) :
    S.RRset μ = S.iota μ '' (S.Mtilde μ).carrier := by
  unfold RowSide.RRset; rw [LamSet_eq S he hi]

theorem rrDef_of (Λ : Submodule (𝓞 D.what₂.LL) S.RR.V)
    (h : ∀ w y, S.jEE y ∈ S.RRset (D.what₂.muAt w) ↔ y ∈ Λ) (hL : S.RR.L = Λ) : S.RRDef := by
  intro x
  have hs : ∀ w, Submodule.span (𝓞 D.what₂.LL) {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)} = Λ := fun w => by
    have : {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)} = (Λ : Set S.RR.V) := Set.ext fun y => h w y
    rw [this, Submodule.span_eq]
  rw [hL]
  constructor
  · intro hx w
    exact ⟨1, fun h1 => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by
      rw [one_smul, hs]; exact hx⟩
  · intro hx
    refine mem_of_local Λ x fun P hP => ?_
    have hne : P ≠ ⊥ := fun hb => RingOfIntegers.not_isField D.what₂.LL
      (Ring.isField_iff_maximal_bot.mpr (hb ▸ hP))
    obtain ⟨d, hd, hdx⟩ := hx (D.plEq.symm ⟨P, hP.isPrime, hne⟩)
    rw [hs] at hdx
    rw [Equiv.apply_symm_apply] at hd
    exact ⟨d, hd, hdx⟩

end Gen

structure CentralCharacterOne (D : D7) where
  χ : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] ℂ
  cen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
  one : χ ⟨D.ntypes.e0, cen⟩ = 1

section Std

variable (D : D7) (c : CentralCharacterOne D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)

def stdSide : RowSide D EE where
  Amb := fun _ => EE
  Mult := fun _ _ => EE
  multZero := fun _ => LinearIsometryEquiv.refl ℂ EE
  multTop := fun _ => LinearIsometryEquiv.refl ℂ EE
  io := fun _ _ => LinearMap.id
  Mtilde := fun _ => oB b _
  cen := fun _ => (Algebra.ofId ℂ (Module.End ℂ EE)).comp c.χ
  eOp := fun _ => LinearMap.id
  eOp_idem := fun _ => rfl
  eOp_sa := fun _ _ _ => rfl
  eOp_tie := fun _ => by
    rw [dif_pos c.cen]
    show LinearMap.id = algebraMap ℂ (Module.End ℂ EE) (c.χ ⟨D.ntypes.e0, c.cen⟩)
    rw [c.one, map_one]; rfl
  RR := stdH D.what₂.LL n
  RR_frames := stdH_frames _ n
  jEE := jB D.what₂.embLL b
  jEE_basis := jB_basis _ b
  jEE_norm := jB_norm _ b

theorem stdSide_downTo (μ) (j : ℕ) : (stdSide D c b).downTo μ j = LinearMap.id := by
  induction j with
  | zero => rfl
  | succ j ih => show ((stdSide D c b).downTo μ j).comp LinearMap.id = _; rw [ih]; rfl

theorem stdSide_iota (μ) : (stdSide D c b).iota μ = LinearMap.id := by
  show (LinearMap.id : EE →ₗ[ℂ] EE) ∘ₗ (stdSide D c b).downTo μ D.R.m ∘ₗ (LinearMap.id : EE →ₗ[ℂ] EE) = _
  rw [stdSide_downTo]; rfl

end Std

theorem jB_mem_oB {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
    {O : Type} [CommRing O] (f : O →+* K) (hf : ∀ z : K, (∃ y, f y = z) ↔ ∃ c : 𝓞 K, z = (c : K))
    (x : Fin n → K) : jB σ b x ∈ (oB b (σ.comp f)).carrier ↔ x ∈ (stdH K n).L := by
  rw [mem_oB, mem_stdL]
  constructor
  · rintro ⟨c, hc⟩ i
    refine (hf (x i)).mp ⟨c i, σ.injective ?_⟩
    have h2 : (∑ k, (σ.comp f) (c k) • b k) = jB σ b (fun k => f (c k)) := rfl
    have h1 := congrArg (fun y => b.repr y i) hc
    simp only [h2, repr_jB] at h1
    exact h1.symm
  · intro h
    have h' := fun i => (hf (x i)).mpr (h i)
    choose c hc using h'
    exact ⟨c, by rw [jB_apply]; exact Finset.sum_congr rfl fun i _ => by rw [RingHom.comp_apply, hc i]⟩

def OFull (D : D7) : Prop := ∀ z : D.what₂.LL, (∃ y, D.what₂.OtoLL y = z) ↔ ∃ c : 𝓞 D.what₂.LL, z = (c : D.what₂.LL)

section Std2

variable (D : D7) (c : CentralCharacterOne D) (hO : OFull D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)

include hO in
theorem stdSide_rrDef : (stdSide D c b).RRDef := by
  refine rrDef_of _ (stdH D.what₂.LL n).L (fun w y => ?_) rfl
  rw [RRset_eq _ rfl (by rw [stdSide_iota]; exact Function.injective_id), stdSide_iota]
  have e : (⇑(LinearMap.id : EE →ₗ[ℂ] EE)) '' ((stdSide D c b).Mtilde (D.what₂.muAt w)).carrier =
      (oB b (D.what₂.embLL.comp D.what₂.OtoLL)).carrier := Set.image_id _
  exact (iff_of_eq (congrArg (fun s => jB D.what₂.embLL b y ∈ s) e)).trans
    (jB_mem_oB D.what₂.embLL b D.what₂.OtoLL hO y)


def ambOf (S : RowSide D EE) (m : D.what₂.Tup → ℕ) (bA : ∀ μ, OrthonormalBasis (Fin (m μ)) ℂ (S.Amb μ))
    (hg : ∀ μ, (S.Mtilde μ).gen = genB (bA μ)) : AmbForm D S where
  MtH := fun μ => stdH D.what₂.LL (m μ)
  jAmb := fun μ => jB D.what₂.embLL (bA μ)
  MtH_good := fun μ _ => stdH_good _ _
  jAmb_basis := fun μ _ => jB_basis _ _
  jAmb_lat := fun μ _ x => by rw [hg]; exact jB_lat _ _ x
  jAmb_gen := fun μ _ => by rw [hg]; exact jB_gen _ _
  jAmb_norm := fun μ _ => jB_norm _ _

def standardBaseSide : BaseLevelRowSide D := ⟨stdSide D c D.what₂.onb0⟩

include hO in
theorem standardBaseSide_latticeDefined : (standardBaseSide D c).s.RRDef := stdSide_rrDef D c hO _

def standardAmbientForm : AmbForm D (standardBaseSide D c).s := ambOf D _ (fun _ => D.what₂.D0) (fun _ => D.what₂.onb0) (fun _ => rfl)

end Std2

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

abbrev En (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

abbrev eb (n : ℕ) : OrthonormalBasis (Fin n) ℂ (En n) := EuclideanSpace.basisFun (Fin n) ℂ

section Rows

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
  (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)
  (Word : Type) (cI : Word → Type) [∀ u, Fintype (cI u)] (d Dall d0 : ℕ) (hd : d ≤ Dall)
  (FT : Type) [Fintype FT] [DecidableEq FT] (ft : Fin d → FT) (ft0 : Fin d0 → FT)
  (per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ)
  (eta : ℕ → P.Pl → ℚ) (heta : ∀ j w, 0 ≤ eta j w)

theorem rank_eq_ratio_identity (d Dall : ℕ) (hd : d ≤ Dall) : (d : ℝ) = (1 - (1 - (d : ℝ) / Dall)) * Dall := by
  rcases Nat.eq_zero_or_pos Dall with h | h
  · subst h
    have : d = 0 := by omega
    subst this; simp
  · have : (Dall : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp
    ring

abbrev rowsN : Rows.Data R where
  LL := LL
  embLL := embLL
  places := P
  O := 𝓞 LL
  OtoLL := algebraMap (𝓞 LL) LL
  Tau := Tau
  card_Tau := hTau
  Tup := Bool
  mu0 := false
  muStar := true
  muStar' := true
  muAt := tw
  muAt_conj := htw
  muTw := fun _ => true
  muTw_conj := fun _ => rfl
  muAt_or := fun w => Bool.eq_false_or_eq_true (tw w) |>.symm
  EE := En d
  Drows := d
  onb := eb d
  Dall := Dall
  delp := 1 - (d : ℝ) / Dall
  delp_le_one := by
    have : (0 : ℝ) ≤ (d : ℝ) / Dall := by positivity
    linarith
  D_eq := rank_eq_ratio_identity d Dall hd
  EE0 := En d0
  D0 := d0
  onb0 := eb d0
  FT := FT
  ft := ft
  ft0 := ft0
  Dstar := Dst
  Amb := fun _ => En d
  Mult := fun _ _ => En d
  multZero := fun _ => LinearIsometryEquiv.refl ℂ (En d)
  multTop := fun _ => LinearIsometryEquiv.refl ℂ (En d)
  io := fun _ _ => LinearMap.id
  Mtilde := fun _ => oB (eb d) _
  eOp := fun _ => LinearMap.id
  eOp_idem := fun _ => rfl
  eOp_sa := fun _ _ _ => rfl
  restRowsFiniteGroupCard := cg
  restRowsFiniteGroupCard_pos := hcg
  Word := Word
  Mu := fun u => EuclideanSpace ℂ (cI u)
  perCol := per
  Bu := fun u φ F => per u false φ F
  ze := fun _ _ => 1
  rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
  Mj := fun _ => En d0
  MjLat := fun _ => oB (eb d0) _
  kaBig := kb
  kaSmall := ks
  Mt := fun _ _ => En d0
  MtLat := fun _ _ => oB (eb d0) _
  MtL := fun _ _ => Fin d0 → LL
  jMt := fun _ _ => jB embLL (eb d0)
  jMt_basis := fun _ _ b => basis_of_basis embLL (jB embLL (eb d0)) (Pi.basisFun LL (Fin d0))
    (jB_basis0 embLL (eb d0)) b
  MtLat_sub := fun _ _ => generators_mem_range embLL (eb d0)
  eMt := fun _ _ => LinearMap.id
  eMt_idem := fun _ _ => rfl
  eMt_sa := fun _ _ _ _ => rfl
  eMt_LL := fun _ _ x => ⟨x, rfl⟩
  thetaP := fun _ _ => LinearMap.id
  isot := fun _ π => Submodule.span ℂ (eb d0 '' {σ | ft0 σ = π})
  lamP := fun _ _ _ => 1
  Ij := fun _ _ _ => 0
  jw := fun _ _ _ => 0
  etaJ := eta
  etaJ_nonneg := heta
  shaLen := sha
  shaLen_nonneg := hsha

end Rows

section RowsLemmas

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] {embLL : LL →+* ℂ} {P : Rows.Places LL}
  {Tau : Type} [Fintype Tau] {hTau : Fintype.card Tau = R.f} {Dst : ℝ}
  {sha : ℕ → ℕ → ℚ} {hsha : ∀ l e, 0 ≤ sha l e} {cg : ℕ} {hcg : 0 < cg}
  {kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ} {ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ}
  {tw : P.Pl → Bool} {htw : ∀ w, tw (P.conj w) = tw w}
  {Word : Type} {cI : Word → Type} [∀ u, Fintype (cI u)] {d Dall d0 : ℕ} {hd : d ≤ Dall}
  {FT : Type} [Fintype FT] [DecidableEq FT] {ft : Fin d → FT} {ft0 : Fin d0 → FT}
  {per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ}
  {eta : ℕ → P.Pl → ℚ} {heta : ∀ j w, 0 ≤ eta j w}

local notation "RN" => (rowsN (R := R) LL embLL P Tau hTau Dst sha hsha cg hcg kb ks tw htw Word cI d Dall d0 hd FT ft ft0
  per eta heta)

theorem rowsN_downTo (μ : Bool) (j : ℕ) : (RN).downTo μ j = (LinearMap.id : En d →ₗ[ℂ] En d) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RN).downTo μ j).comp (LinearMap.id : En d →ₗ[ℂ] En d) = _
    rw [ih]; rfl

theorem rowsN_iota (μ : Bool) : (RN).iota μ = (LinearMap.id : En d →ₗ[ℂ] En d) := by
  show (LinearMap.id : En d →ₗ[ℂ] En d) ∘ₗ (RN).downTo μ R.m ∘ₗ (LinearMap.id : En d →ₗ[ℂ] En d) = _
  rw [rowsN_downTo]; rfl

theorem rowsN_thetaT (μ : Bool) (j : ℕ) : (RN).thetaT μ j = (LinearMap.id : En d0 →ₗ[ℂ] En d0) :=
  LinearMap.adjoint_id

theorem rowsN_TjSet (μ : Bool) (j : ℕ) :
    (RN).TjSet μ j = (oB (eb d0) (embLL.comp (algebraMap (𝓞 LL) LL))).carrier := by
  have hZ : (RN).Zj μ j = ⊤ := by
    unfold Rows.Data.Zj; rw [rowsN_thetaT]; exact LinearMap.range_id
  have hp : ∀ x, ((RN).Zj μ j).starProjection x = x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (by rw [hZ]; trivial)
  unfold Rows.Data.TjSet
  ext x
  simp only [hp, Set.mem_image]
  exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

end RowsLemmas

section Gen

variable {R : Ranks} (D : Rows.Data R)





end Gen


end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

variable (D : D7)

def divXStd (n : ℕ → ℕ) (bM : ∀ j, OrthonormalBasis (Fin (n j)) ℂ (D.what₂.Mj j))
    (hg : ∀ j, (D.what₂.MjLat j).gen = genB (bM j)) (kap : ℝ) (hk : 0 < kap) : DivX D where
  geo := geoExample _
  Lev := Empty
  levPr := fun κ => κ.elim
  shv := fun _ κ => κ.elim
  shv_N := fun _ κ => κ.elim
  shv_lev := fun _ κ => κ.elim
  PlP := fun p _ => {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}
  plpFin := fun p _ => PlOver.plFin D p
  plpNe := fun p _ => PlOver.plNe D p
  wtP := fun p _ la => PlOver.wt D p la.1
  divisorWeight_nonneg := fun p _ la => PlOver.wt_nonneg D p la.1
  divisorWeight_sum := fun p _ => PlOver.wt_sum D p
  plP := fun _ _ => Equiv.refl _
  divisorWeight_def := fun _ _ _ => rfl
  jC := fun p _ _ => (teich_Om_equiv p).some.toRingHom.comp (algebraMap (DV.KW p) (TeichOm p))
  Mp := fun _ κ => κ.elim
  md := fun _ κ => κ.elim
  vdd := fun _ _ => 0
  vdd_unram := fun _ _ _ => rfl
  vdd_nonneg := fun _ _ => le_rfl
  CurveM := fun _ κ => κ.elim
  degM := fun _ κ => κ.elim
  htMdl := fun _ κ => κ.elim
  htCurve := fun _ κ => κ.elim
  htCurve_deg := fun _ κ => κ.elim
  MjH := fun j => stdH D.what₂.LL (n j)
  MjH_good := fun j => stdH_good _ _
  jM := fun j => jB D.what₂.embLL (bM j)
  jM_basis := fun j => jB_basis _ _
  jM_lat := fun j _ _ x => by rw [hg]; exact jB_lat _ _ x
  jM_metric := fun j _ _ x => jB_norm _ _ x
  Qp := fun _ => ∅
  degreeZero_partial_set_empty := rfl
  Qp_muAt := fun _ => Finset.notMem_empty _
  Qp_g := fun _ _ _ => Finset.notMem_empty _
  QPl := fun _ => Empty
  qv := fun _ v => v.elim
  qv_gt := fun _ v => v.elim
  qv_char := fun _ _ v => v.elim
  nu := fun _ v => v.elim
  nu_ne := fun _ v => v.elim
  nu_abs := fun _ v => v.elim
  ZQ := fun _ v => v.elim
  quotientLocalValueFirst := fun _ v => v.elim
  typeDim := fun _ v => v.elim
  Comp := fun _ => Empty
  degHH := fun _ c => c.elim
  Yv := fun _ c => c.elim
  Ybd := fun _ c => c.elim
  Lw := fun _ c => c.elim
  iMj := fun _ c => c.elim
  iMj_mem := fun _ c => c.elim
  logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
  logLam_base := fun _ _ => rfl
  kapR := fun _ => kap
  kapR_pos := fun _ => hk
  kapR_conj := fun _ => rfl
  MjLat_sub := fun j _ _ => by rw [hg]; exact jB_gen _ _
  phiFr_unram := fun _ κ => κ.elim
  Surf := Empty
  surfCh2 := fun _ => 0
  surfDegOm := fun _ => 0
  SurfFp := Empty
  surfFpCh2 := fun _ => 0

theorem ijIdx_zero {D : D7} (X : DivX D) (μ j w) (h : (X.MjH j).L = Idx.thTj X μ j) : Idx.IjIdx X μ j w = 0 := by
  unfold Idx.IjIdx Formalism.HermitianLatticesTheory.lidx
  rw [h]; exact sub_self _

theorem jwIdx_zero (μ j w) (h : Idx.TjL D μ j = Idx.TjDual D μ j) : Idx.jwIdx D μ j w = 0 := by
  unfold Idx.jwIdx Formalism.HermitianLatticesTheory.lidx
  rw [← h]; exact sub_self _

theorem lamDef_of (h : ∀ μ j π, ∀ x ∈ D.what₂.isot j π,
    D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = ((D.what₂.lamP μ j π : ℝ) : ℂ) • x) : DV.LamDef D :=
  fun μ j _ _ π h0 => (DV.lamTr_of_scalar D μ j π _ h0 (h μ j π)).symm

section Kap

variable {D} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

theorem iiStar_id (he : S.eOp D.what₂.mu0 = LinearMap.id)
    (hiso : ∀ x y, inner ℂ (S.iota D.what₂.mu0 x) (S.iota D.what₂.mu0 y) = inner ℂ x y)
    (hs : Function.Surjective (S.iota D.what₂.mu0)) : S.iiStar = LinearMap.id := by
  have hi : Function.Injective (S.iota D.what₂.mu0) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have := hiso x x
    rw [LinearMap.mem_ker.mp hx, inner_zero_left] at this
    exact inner_self_eq_zero.mp this.symm
  ext x
  refine ext_inner_right ℂ fun y => ?_
  obtain ⟨z, rfl⟩ := hs y
  have hz : z ∈ S.Qsp D.what₂.mu0 := by rw [Qsp_top S he hi]; trivial
  show inner ℂ (S.iota D.what₂.mu0 (LinearMap.adjoint (S.iotaQ D.what₂.mu0) x : S.Amb D.what₂.mu0))
    (S.iota D.what₂.mu0 z) = inner ℂ x (S.iota D.what₂.mu0 z)
  rw [hiso]
  have h1 : inner ℂ (LinearMap.adjoint (S.iotaQ D.what₂.mu0) x) (⟨z, hz⟩ : S.Qsp D.what₂.mu0) =
      inner ℂ x (S.iotaQ D.what₂.mu0 ⟨z, hz⟩) := LinearMap.adjoint_inner_left _ _ _
  exact h1

theorem kapOf_one {n : ℕ} (ty : Fin n → D.what₂.FT) (hii : S.iiStar = LinearMap.id)
    (hl : ∀ j π, D.what₂.lamP D.what₂.mu0 j π = 1) : S.kapOf ty = 1 := by
  have hr : S.kapRatio ty = 1 := by
    unfold RowSide.kapRatio DV.lamProd
    rw [hii, LinearMap.det_id]
    simp [hl]
  unfold RowSide.kapOf
  rw [hr, if_pos one_pos, Real.one_rpow]

end Kap

end Formalism.BasicNotions.Examples₂.NZ
end
end
