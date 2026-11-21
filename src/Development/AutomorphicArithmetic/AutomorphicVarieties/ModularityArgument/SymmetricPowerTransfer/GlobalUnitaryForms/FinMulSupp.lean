import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.GqMass
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzdLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.MassFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.StabLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OneD

section
open MulAction

namespace UpperTheory.V.Z.Sym.Glob

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)}

theorem rpg_ext (P : RPG G Gv K) {a b : G} (h : ∀ v, P.p v a = P.p v b) : a = b := by
  have hab := P.inj (a * b⁻¹) fun v => by rw [map_mul, map_inv, h v, mul_inv_cancel]
  exact mul_inv_eq_one.mp hab

theorem mem_box (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

theorem smul_mk_iff {A : Type} [Group A] (U : Subgroup A) (x g : A) : x • (g : A ⧸ U) = g ↔ g⁻¹ * x * g ∈ U := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, ← U.inv_mem_iff]
  simp [mul_assoc]

theorem rpg_hom {T : Type} [Group T] {Tv : I → Type} [∀ v, Group (Tv v)] {C₀ : ∀ v, Subgroup (Tv v)} (P : RPG G Gv K)
    (Q : RPG T Tv C₀) (ιv : ∀ v, Tv v →* Gv v) (h : ∀ᶠ v in Filter.cofinite, (C₀ v).map (ιv v) ≤ K v) :
    ∃ ι : T →* G, ∀ v t, P.p v (ι t) = ιv v (Q.p v t) := by
  have hx : ∀ t : T, ∀ᶠ v in Filter.cofinite, ιv v (Q.p v t) ∈ K v := fun t =>
    ((Q.ae t).and h).mono fun v hv => hv.2 ⟨_, hv.1, rfl⟩
  choose g hg using fun t => P.surj _ (hx t)
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_ }, fun v t => hg t v⟩
  · exact rpg_ext P fun v => by simp only [hg, map_one]
  · intro a b
    exact rpg_ext P fun v => by simp only [hg, map_mul]

private theorem box_relIndex_ne_zero_of_local {T : Type} [Group T] {Tv : I → Type} [∀ v, Group (Tv v)]
    {C₀ : ∀ v, Subgroup (Tv v)} (Q : RPG T Tv C₀) (A B : ∀ v, Subgroup (Tv v))
    (hA : ∀ v, (A v).relIndex (B v) ≠ 0) (hfin : ∀ᶠ v in Filter.cofinite, B v ≤ A v) :
    (Q.box A).relIndex (Q.box B) ≠ 0 := by
  classical
  have key : ∀ F : Finset I, ∃ D : Subgroup T, D.relIndex (Q.box B) ≠ 0 ∧
      ∀ t ∈ D, ∀ v ∈ F, Q.p v t ∈ A v := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨⊤, by simp, fun _ _ v hv => by simp at hv⟩
    | @insert a F _ ih =>
      obtain ⟨D, hD, hDF⟩ := ih
      refine ⟨D ⊓ (A a).comap (Q.p a), Subgroup.relIndex_inf_ne_zero hD ?_, ?_⟩
      · rw [Subgroup.relIndex_comap]
        refine mt (Subgroup.relIndex_eq_zero_of_le_right ?_) (hA a)
        rw [Subgroup.map_le_iff_le_comap]
        intro t ht
        exact (mem_box Q B t).1 ht a
      · intro t ht v hv
        rcases Finset.mem_insert.1 hv with rfl | hv
        · exact ht.2
        · exact hDF t ht.1 v hv
  obtain ⟨D, hD, hDF⟩ := key (Filter.eventually_cofinite.1 hfin).toFinset
  refine mt (Subgroup.relIndex_eq_zero_of_le_left (K := Q.box A) ?_)
    (Subgroup.relIndex_inf_ne_zero hD (by simp : (Q.box B).relIndex (Q.box B) ≠ 0))
  intro t ht
  rw [mem_box]
  intro v
  by_cases hv : B v ≤ A v
  · exact hv ((mem_box Q B t).1 ht.2 v)
  · exact hDF t ht.1 v (by simpa using hv)

theorem gqAbs {T H : Type} [CommGroup T] [Group H] {Tv : I → Type} [∀ v, CommGroup (Tv v)] (U : ∀ v, Subgroup (Gv v))
    {C₀ : ∀ v, Subgroup (Tv v)} (C : ∀ v, Subgroup (Tv v)) (P : RPG G Gv K) (Q : RPG T Tv C₀)
    (ιv : ∀ v, Tv v →* Gv v) (θ : G →* G) (θv : ∀ v, Gv v →* Gv v) (f : G → ℂ) (fv : ∀ v, Gv v → ℂ) (δ : G)
    (φ : H →* T) (j : H →* G) (H₀ : Subgroup H)
    (hj : ∀ h v, P.p v (j h) = ιv v (Q.p v (φ h))) (hθ : ∀ v g, P.p v (θ g) = θv v (P.p v g))
    (hf : ∀ g, f g = ∏ᶠ v, fv v (P.p v g)) (hinv : ∀ v, ∀ u ∈ U v, ∀ x, fv v (u⁻¹ * x * θv v u) = fv v x)
    (hc : ∀ v t, (ιv v t)⁻¹ * P.p v δ * θv v (ιv v t) = P.p v δ) (S : Finset I)
    (hS : ∀ v ∈ S, FinOrb (ιv v) (θv v) (U v) (fv v) (P.p v δ))
    (hoff : ∀ v ∉ S, K v ≤ U v ∧ C₀ v ≤ C v ∧ (C v).map (ιv v) ≤ U v ∧ fv v (P.p v δ) = 1 ∧
      ∀ y, fv v (y⁻¹ * P.p v δ * θv v y) ≠ 0 → ∃ t, ∃ u ∈ U v, y = ιv v t * u)
    (hK : ∀ v ∉ S, (C₀ v).map (ιv v) ≤ K v)
    (hst : ∀ v (y : Gv v ⧸ U v), (stabilizer (Gv v) y).comap (ιv v) ≤ C v ∧ ((stabilizer (Gv v) y).comap (ιv v)).relIndex (C v) ≠ 0)
    (h0 : ∀ z ∈ H₀, ∀ v y, y⁻¹ * P.p v (j z) * y ∈ U v)
    (m1 : (φ.range ⊔ Q.box C).index ≠ 0) (m2 : H₀.relIndex ((Q.box C).comap φ) ≠ 0) :
    gqOn j H₀ (P.box U) (fun y => f (y.out⁻¹ * δ * θ y.out)) =
      mass φ H₀ (Q.box C) * ∏ v ∈ S, orb (ιv v) (C v) (θv v) (U v) (fv v) (P.p v δ) := by
  have hS' : ∀ᶠ v in Filter.cofinite, v ∉ S :=
    Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by simpa using hv)
  obtain ⟨ι, hι⟩ := rpg_hom P Q ιv (hS'.mono hK)
  have hjι : j = ι.comp φ :=
    MonoidHom.ext fun z => rpg_ext P fun v => by rw [hj, MonoidHom.comp_apply, hι]
  subst hjι
  have hbox : ∀ (g x : G), x • (g : G ⧸ P.box U) = g ↔
      ∀ v, (P.p v g)⁻¹ * P.p v x * P.p v g ∈ U v := by
    intro g x
    rw [smul_mk_iff, mem_box]
    simp only [map_mul, map_inv]
  have hprod := Tf.orbProd I G T Gv Tv K U C₀ C P Q ι ιv θ θv f fv δ hι hθ hf hinv hc S hS hoff
  refine (Tf.gqMass H T G φ ι H₀ (Q.box C) θ (P.box U) f δ ?_ ?_ hprod.1 ?_ m1 m2 ?_ ?_).trans ?_
  · intro u hu x
    rw [hf, hf]
    refine finprod_congr fun v => ?_
    simp only [map_mul, map_inv, hθ]
    exact hinv v _ ((mem_box P U u).1 hu v) _
  · intro t
    exact rpg_ext P fun v => by
      simp only [map_mul, map_inv, hθ, hι]
      exact hc v _
  · intro z hz y
    refine QuotientGroup.induction_on y fun g => ?_
    exact (hbox g _).2 fun v => h0 z hz v _
  · intro y
    refine QuotientGroup.induction_on y fun g _ => ?_
    have hEq : (stabilizer G (g : G ⧸ P.box U)).comap ι =
        Q.box (fun v => (stabilizer (Gv v) ((P.p v g : Gv v ⧸ U v))).comap (ιv v)) := by
      ext t
      rw [Subgroup.mem_comap, mem_stabilizer_iff, hbox, mem_box]
      simp only [Subgroup.mem_comap, mem_stabilizer_iff, smul_mk_iff, hι]
    rw [hEq]
    refine ⟨fun t ht => (mem_box Q C t).2 fun v => (hst v _).1 ((mem_box Q _ t).1 ht v), ?_⟩
    refine box_relIndex_ne_zero_of_local Q _ C (fun v => (hst v _).2) ?_
    refine ((P.ae g).and hS').mono fun v hv t ht => ?_
    obtain ⟨hKU, -, hCU, -⟩ := hoff v hv.2
    rw [Subgroup.mem_comap, mem_stabilizer_iff, smul_mk_iff]
    have hg : P.p v g ∈ U v := hKU hv.1
    exact (U v).mul_mem ((U v).mul_mem ((U v).inv_mem hg) (hCU ⟨t, ht, rfl⟩)) hg
  · intro z hz
    rw [Subgroup.mem_comap, mem_box]
    intro v
    refine (hst v ((1 : Gv v) : Gv v ⧸ U v)).1 ?_
    rw [Subgroup.mem_comap, mem_stabilizer_iff, smul_mk_iff]
    have h1 := h0 z hz v 1
    rwa [MonoidHom.comp_apply, hι] at h1
  · rw [hprod.2]

end UpperTheory.V.Z.Sym.Glob
end

section
open Matrix UpperTheory.V.Z.Sym.Loc QuadraticAlgebra

namespace UpperTheory.V.Z.Sym.Glob

variable {K K' : Type} [Field K] [Field K'] {Δ τ : K}

theorem dx_ext {a b : DX Δ} (h : mt a = mt b) : a = b := Subtype.ext (Units.ext h)

theorem zd_scal {s : DX Δ} (h : s ∈ ZD Δ) : ∃ z, IsScal z s := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, (congrArg Units.val hz).symm⟩

theorem scal_comm {z : Kˣ} {s : DX Δ} (h : IsScal z s) (y : DX Δ) : s * y = y * s := by
  refine dx_ext ?_
  change mt s * mt y = mt y * mt s
  rw [h]
  exact (scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem conj_sup {J : Subgroup (DX Δ)} {f : DX Δ → ℂ} (h : ∀ u ∈ J, ∀ x, f (u⁻¹ * x * u) = f x) :
    ∀ u ∈ ZD Δ ⊔ J, ∀ x, f (u⁻¹ * x * u) = f x := by
  let A : Subgroup (DX Δ) :=
    { carrier := {u | ∀ x, f (u⁻¹ * x * u) = f x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb x => by
        have := hb (a⁻¹ * x * a)
        rw [ha] at this
        simpa [mul_assoc] using this
      inv_mem' := fun {a} ha x => by
        have := ha (a * x * a⁻¹)
        simpa [mul_assoc] using this.symm }
  refine fun u hu => (sup_le (fun s hs x => ?_) h : ZD Δ ⊔ J ≤ A) hu
  obtain ⟨z, hz⟩ := zd_scal hs
  rw [mul_assoc, ← scal_comm hz, inv_mul_cancel_left]

theorem mem_center_sup_exists_scalar_mul {J : Subgroup (DX Δ)} {u : DX Δ} (hu : u ∈ ZD Δ ⊔ J) : ∃ z s, ∃ k ∈ J, IsScal z s ∧ u = s * k := by
  haveI : (ZD Δ).Normal := ⟨fun s hs g => by
    obtain ⟨z, hz⟩ := zd_scal hs
    rwa [← scal_comm hz, mul_inv_cancel_right]⟩
  obtain ⟨s, hs, k, hk, e⟩ := Subgroup.mem_sup_of_normal_left.1 hu
  obtain ⟨z, hz⟩ := zd_scal hs
  exact ⟨z, s, k, hk, hz, e.symm⟩

theorem fZD_conj (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O K] (h : IsLoc O Δ) (χ : Kˣ →* ℂˣ)
    (hχ : Unr O χ) : ∀ u ∈ KD Δ O, ∀ x, fZD O χ (u⁻¹ * x * u) = fZD O χ x := by
  intro u hu x
  obtain ⟨h0, h1⟩ := Loc.fzdLaw O K Δ h χ hχ
  have hu' : u ∈ ZD Δ ⊔ KD Δ O := Subgroup.mem_sup_right hu
  by_cases hx : x ∈ ZD Δ ⊔ KD Δ O
  · obtain ⟨z, s, k, hk, hz, rfl⟩ := mem_center_sup_exists_scalar_mul hx
    have e : u⁻¹ * (s * k) * u = s * (u⁻¹ * k * u) := by rw [← mul_assoc, ← scal_comm hz]; simp only [mul_assoc]
    rw [e, h1 z s k hz hk, h1 z s _ hz (mul_mem (mul_mem (inv_mem hu) hk) hu)]
  · rw [h0 x hx, h0]
    exact fun h => hx (by simpa [mul_assoc] using mul_mem (mul_mem hu' h) (inv_mem hu'))

theorem hasTr_map (f : K →+* K') {γ : DX Δ} {γ' : DX (f Δ)} (e : mt γ' = (mt γ).map (lmap f Δ)) (h : HasTr γ τ) : HasTr γ' (f τ) := by
  constructor
  · rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h.1, map_one]
  · have := congrArg (lmap f Δ) h.2
    rw [e, trace_fin_two, map_apply, map_apply, ← map_add, ← trace_fin_two, this]
    ext <;> simp [lmap, QuadraticAlgebra.algebraMap_eq]

theorem emb_map (f : K →+* K') {γ : DX Δ} {γ' : DX (f Δ)} (e : mt γ' = (mt γ).map (lmap f Δ)) {j j'} (h : IsEmb τ γ j)
    (h' : IsEmb (f τ) γ' j') (z : (Etau K τ)ˣ) (z' : (Etau K' (f τ))ˣ) (ez : (z' : Etau K' (f τ)) = emap f τ z) :
    mt (j' z') = (mt (j z)).map (lmap f Δ) := by
  rw [h, h', e, ez]
  ext a b <;> by_cases hab : a = b <;> simp [lmap, emap, hab, Matrix.one_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem emb_comm {γ : DX Δ} {j} (h : IsEmb τ γ j) (z) : j z * γ = γ * j z := by
  refine dx_ext ?_
  change mt (j z) * mt γ = mt γ * mt (j z)
  rw [h]
  simp [add_mul, mul_add]

theorem cu_coords (O : Type) [CommRing O] [Algebra O K] (hτ : IsIntegral O τ) (hu : ∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4)
    (h2 : IsUnit (2 : O)) {x : Etau K τ} (hx : IsIntegral O x) : IsIntegral O x.re ∧ IsIntegral O x.im := by
  obtain ⟨u, hu⟩ := hu
  obtain ⟨w, hw⟩ := h2.exists_right_inv
  let st : Etau K τ →ₐ[O] Etau K τ := { starRingEnd (Etau K τ) with
    commutes' := fun r => by ext <;> simp [QuadraticAlgebra.algebraMap_eq, IsScalarTower.algebraMap_apply O K (Etau K τ), starRingEnd_apply] }
  have hs : IsIntegral O (star x) := hx.map st
  have inj : Function.Injective (algebraMap K (Etau K τ)) := (algebraMap K _).injective
  have h1 : IsIntegral O (x.im ^ 2 * (τ ^ 2 - 4)) := by
    rw [← isIntegral_algebraMap_iff inj]
    convert (hx.sub hs).pow 2 using 1
    ext <;> simp [QuadraticAlgebra.algebraMap_eq, sq] <;> ring
  have h3 : IsIntegral O x.im := by
    refine IsIntegral.of_pow two_pos ?_
    have := h1.mul (isIntegral_algebraMap (R := O) (A := K) (x := (u⁻¹ : Oˣ)))
    rwa [← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one] at this
  have h4 : IsIntegral O (2 * x.re + τ * x.im) := by
    rw [← isIntegral_algebraMap_iff inj]
    convert hx.add hs using 1
    ext <;> simp [QuadraticAlgebra.algebraMap_eq] <;> ring
  refine ⟨?_, h3⟩
  have := (h4.sub (hτ.mul h3)).mul (isIntegral_algebraMap (R := O) (A := K) (x := w))
  have e : (2 : K) * algebraMap O K w = 1 := by rw [← map_ofNat (algebraMap O K) 2, ← map_mul, hw, map_one]
  rwa [show (2 * x.re + τ * x.im - τ * x.im) * algebraMap O K w = x.re by linear_combination x.re * e] at this

theorem cu_map (O : Type) [CommRing O] [Algebra O K] (hτ : IsIntegral O τ) (hu : ∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4)
    (h2 : IsUnit (2 : O)) {γ : DX Δ} {j} (h : IsEmb τ γ j) (hγ : γ ∈ KD Δ O) : (Cu O τ).map j ≤ KD Δ O := by
  have key : ∀ z : (Etau K τ)ˣ, IsIntegral O (z : Etau K τ) → ∀ a b, IsIntegral O (mt (j z) a b) := fun z hz a b => by
    obtain ⟨h1, h3⟩ := cu_coords O hτ hu h2 hz
    rw [h, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def, Algebra.smul_def]
    refine (h1.algebraMap.mul ?_).add (h3.algebraMap.mul ((mem_KD.1 hγ).1 a b))
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab, isIntegral_one, isIntegral_zero]
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  refine mem_KD.2 ⟨key _ w.1.2, ?_⟩
  rw [← map_inv, ← map_inv]
  exact key _ (w⁻¹).1.2

end UpperTheory.V.Z.Sym.Glob
end

section
open NumberField UpperTheory.V.Z.Sym.Loc

namespace UpperTheory.V.Z.Sym.Glob

variable {F : Type} [Field F] [NumberField F] {Δ : F}

theorem cm_ne [IsTotallyReal F] {τ : F} (h : IsCM τ) : τ ^ 2 - 4 ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro e
  have := h (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  rw [e, map_zero] at this
  exact lt_irrefl _ this

theorem Dat.Ok.ne0 {D : Dat Δ} (h : D.Ok) : Δ ≠ 0 := by
  haveI := h.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro e
  have := h.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  rw [e, map_zero] at this
  exact lt_irrefl _ this

theorem cv_reg {τ : F} (h : τ ^ 2 - 4 ≠ 0) (v : Pl F) : cv v τ ^ 2 - 4 ≠ 0 := by
  intro h0
  apply h
  rw [← map_ofNat (cv v) 4, ← map_pow, ← map_sub] at h0
  exact (map_eq_zero (cv v)).1 h0

theorem ae_mem (x : F) : ∀ᶠ v : Pl F in Filter.cofinite, cv v x ∈ v.adicCompletionIntegers F := by
  exact (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 F) F x).2

theorem ae_unit {x : F} (h : x ≠ 0) : ∀ᶠ v : Pl F in Filter.cofinite, ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v x := by
  filter_upwards [ae_mem x, ae_mem x⁻¹] with v h1 h2
  refine ⟨⟨⟨cv v x, h1⟩, ⟨cv v x⁻¹, h2⟩, ?_, ?_⟩, rfl⟩
  · ext
    simp [← map_mul, h]
  · ext
    simp [← map_mul, h]

theorem ae_reg {τ : F} (h : τ ^ 2 - 4 ≠ 0) :
    ∀ᶠ v : Pl F in Filter.cofinite, ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v τ ^ 2 - 4 := by
  filter_upwards [ae_unit h] with v hv
  obtain ⟨u, hu⟩ := hv
  exact ⟨u, by rw [hu, map_sub, map_pow, map_ofNat]⟩

theorem prod_split (Sg S : Finset (Pl F)) (h : Sg ⊆ S) (a b g : Pl F → ℂ) (h1 : ∀ v ∈ Sg, g v = a v) (h2 : ∀ v ∉ Sg, g v = b v)
    (h3 : ∀ v ∉ S, b v = 1) : ∏ v ∈ S, g v = (∏ v ∈ Sg, a v) * ∏ᶠ (v) (_ : v ∉ Sg), b v := by
  classical
  rw [← Finset.prod_sdiff h, mul_comm, Finset.prod_congr rfl h1]
  congr 1
  rw [finprod_cond_eq_prod_of_cond_iff b (t := S \ Sg)]
  · exact Finset.prod_congr rfl fun v hv => h2 v (Finset.mem_sdiff.1 hv).2
  · intro x hx
    have hxS : x ∈ S := by
      by_contra hS
      exact hx (h3 x hS)
    simp [Finset.mem_sdiff, hxS]

theorem zEx {K : Type} [Field K] {τ : K} (h : τ ^ 2 - 4 ≠ 0) : ∃ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + QuadraticAlgebra.omega := by
  have hu : IsUnit (1 + QuadraticAlgebra.omega : Etau K τ) := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, isUnit_iff_ne_zero]
    simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    intro h0
    apply h
    linear_combination (τ - 2) * h0
  exact ⟨hu.unit, rfl⟩

theorem gqOn_zero {H G : Type} [Group H] [Group G] (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ) (h : ∀ y, k y = 0) :
    gqOn j H₀ U k = 0 := by
  simp [gqOn, gq, h]

theorem fin_mulSupp {I : Type} {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (f : ∀ v, Gv v → ℂ) (S : Finset I)
    (h : ∀ v ∉ S, ∀ k ∈ K v, f v k = 1) (g : RP Gv K) {v : I} (hv : f v (g.1 v) = 0) : ∏ᶠ v, f v (g.1 v) = 0 := by
  apply finprod_eq_zero (fun w => f w (g.1 w)) v hv
  have hg : {w | ¬ g.1 w ∈ K w}.Finite := Filter.eventually_cofinite.1 g.2
  show (Function.mulSupport _).Finite
  refine (S.finite_toSet.union hg).subset ?_
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hw (h w hc.1 _ hc.2)

theorem hasTr_conj {K : Type} [Field K] {Δ τ : K} {γ : DX Δ} (h : HasTr γ τ) (y : DX Δ) : HasTr (y⁻¹ * γ * y) τ := by
  obtain ⟨hd, ht⟩ := h
  have hd' : ((γ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = 1 := hd
  refine ⟨?_, ?_⟩
  · show (((y⁻¹ * γ * y : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [Matrix.det_mul, Matrix.det_mul, hd', mul_one, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  · show (((y⁻¹ * γ * y : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).trace = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    have key := Matrix.trace_units_conj ((y : GL (Fin 2) (Lsq K Δ))⁻¹) (mt γ)
    rw [inv_inv] at key
    exact key.trans ht

theorem gqD (D : Dat Δ) (hD : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) (t : Dat.Par F) (ht : D.Cone t) (τ : F) (hτ : IsCM τ)
    (hA : D.admitted t τ) (γ : DX Δ) (j : (Etau F τ)ˣ →* DX Δ) (hγ : HasTr γ τ) (hj : IsEmb τ γ j) (δ : DX Δ)
    (fv : ∀ v : Pl F, DX (cv v Δ) → ℂ) (hinv : ∀ v, ∀ u ∈ D.J2v v, ∀ x, fv v (u⁻¹ * x * u) = fv v x) (a b : Pl F → ℂ)
    (hloc : ∀ v jv, IsEmb (cv v τ) ((ι γ).1 v) jv → (∀ s, jv s * (ι δ).1 v = (ι δ).1 v * jv s) ∧
      FinOrb jv (MonoidHom.id _) (ZD _ ⊔ D.J2v v) (fv v) ((ι δ).1 v) ∧
      (v ∈ D.Sg → orb jv (Cint (Ov v) _) (MonoidHom.id _) (ZD _ ⊔ D.J2v v) (fv v) ((ι δ).1 v) = a v) ∧
      (v ∉ D.Sg → orb jv (Cint (Ov v) _) (MonoidHom.id _) (ZD _ ⊔ D.J2v v) (fv v) ((ι δ).1 v) = b v ∧
        ((ι γ).1 v ∈ KD _ (Ov v) → (∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v τ ^ 2 - 4) → fv v ((ι δ).1 v) = 1 ∧
          ∀ y, fv v (y⁻¹ * (ι δ).1 v * y) ≠ 0 → ∃ s, ∃ u ∈ ZD _ ⊔ KD _ (Ov v), y = jv s * u))) :
    gqOn (ι.comp j) (scalE τ) D.UZ (fun y => ∏ᶠ v, fv v ((y.out⁻¹ * ι δ * y.out).1 v)) =
      (∏ v ∈ D.Sg, a v) * (ms τ * ∏ᶠ (v) (_ : v ∉ D.Sg), b v) := by
  classical
  haveI := hD.real
  have hτ4 : τ ^ 2 - 4 ≠ 0 := cm_ne hτ
  have hΔ : Δ ≠ 0 := hD.ne0
  have hex : ∃ φ : (Etau F τ)ˣ →* TA τ, IsDiagT τ φ := (iotaEx F Δ).2.2 τ
  have hφ : IsDiagT τ hex.choose := hex.choose_spec
  have hchar : ∀ v : Pl F, CharZero (Kv v) := fun v =>
    charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
  have hΔv : ∀ v : Pl F, cv v Δ ≠ 0 := fun v => (map_ne_zero (cv v)).2 hΔ
  have hτv : ∀ v : Pl F, cv v τ ^ 2 - 4 ≠ 0 := fun v => cv_reg hτ4 v
  have hγv : ∀ v : Pl F, HasTr ((ι γ).1 v) (cv v τ) := fun v => hasTr_map (cv v) (hι γ v) hγ
  have hjex : ∀ v : Pl F, ∃ jv : (Etau (Kv v) (cv v τ))ˣ →* DX (cv v Δ), IsEmb (cv v τ) ((ι γ).1 v) jv := by
    intro v
    haveI := hchar v
    exact (embAlg (Kv v) (cv v Δ) (cv v τ) (hΔv v) (hτv v) _ (hγv v)).1
  choose jv hjv using hjex
  have hιγ : ∀ᶠ v : Pl F in Filter.cofinite, (ι γ).1 v ∈ KD (cv v Δ) (Ov v) := (ι γ).2
  have hgood : ∀ᶠ v : Pl F in Filter.cofinite,
      (ι γ).1 v ∈ KD (cv v Δ) (Ov v) ∧ (∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v τ ^ 2 - 4) ∧
        cv v τ ∈ v.adicCompletionIntegers F :=
    (hιγ.and (ae_reg hτ4)).and (ae_mem τ) |>.mono fun v h => ⟨h.1.1, h.1.2, h.2⟩
  have hSbfin := Filter.eventually_cofinite.1 hgood
  have hSg : D.Sg ⊆ D.Sg ∪ hSbfin.toFinset := Finset.subset_union_left
  have hnotS : ∀ v ∉ D.Sg ∪ hSbfin.toFinset, v ∉ D.Sg ∧ ((ι γ).1 v ∈ KD (cv v Δ) (Ov v) ∧
      (∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v τ ^ 2 - 4) ∧ cv v τ ∈ v.adicCompletionIntegers F) := by
    intro v hv
    simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
    exact hv
  have hJ : ∀ v ∉ D.Sg, D.J2v v = KD (cv v Δ) (Ov v) := fun v hv => by simp [Dat.J2v, hv]
  have hcomm : ∀ v (s : (Etau (Kv v) (cv v τ))ˣ), (jv v s)⁻¹ * (ι δ).1 v * jv v s = (ι δ).1 v := by
    intro v s
    have hc := (hloc v (jv v) (hjv v)).1 s
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hoff : ∀ v ∉ D.Sg ∪ hSbfin.toFinset, Subgroup.comap (jv v) (ZD (cv v Δ) ⊔ KD (cv v Δ) (Ov v)) =
      Cint (Ov v) (cv v τ) ∧ Subgroup.map (jv v) (Cu (Ov v) (cv v τ)) ≤ KD (cv v Δ) (Ov v) := by
    intro v hv
    obtain ⟨hvSg, hKD, hunit, hint⟩ := hnotS v hv
    have hL := hD.off v hvSg
    exact ⟨(oneD (Ov v) (Kv v) (cv v Δ) (cv v τ) hL (hτv v) _ (jv v) (hγv v) (hjv v) hKD hunit).1,
      cu_map (Ov v) (isIntegral_Ov.2 hint) hunit hL.two (hjv v) hKD⟩
  refine (gqAbs (fun v => ZD (cv v Δ) ⊔ D.J2v v) (fun v => Cint (Ov v) (cv v τ))
    (rpg (fun v : Pl F => DX (cv v Δ)) fun v => KD (cv v Δ) (Ov v))
    (rpg (fun v : Pl F => (Etau (Kv v) (cv v τ))ˣ) fun v => Cu (Ov v) (cv v τ))
    jv (MonoidHom.id _) (fun v => MonoidHom.id _) (fun g => ∏ᶠ v, fv v (g.1 v)) fv (ι δ) hex.choose (ι.comp j)
    (scalE τ) ?_ (fun v g => rfl) (fun g => rfl) ?_ ?_ (D.Sg ∪ hSbfin.toFinset) ?_ ?_ ?_ ?_ ?_
    (massFin F τ hτ hex.choose hφ).1 (massFin F τ hτ hex.choose hφ).2).trans ?_
  · intro h v
    apply dx_ext
    show mt ((ι (j h)).1 v) = mt (jv v ((hex.choose h).1 v))
    rw [hι (j h) v]
    exact (emb_map (cv v) (hι γ v) hj (hjv v) h ((hex.choose h).1 v) (hφ h v)).symm
  · intro v u hu x
    exact conj_sup (hinv v) u hu x
  · intro v s
    exact hcomm v s
  · intro v _
    exact (hloc v (jv v) (hjv v)).2.1
  · intro v hv
    obtain ⟨hvSg, hKD, hunit, hint⟩ := hnotS v hv
    have hl := ((hloc v (jv v) (hjv v)).2.2.2 hvSg).2 hKD hunit
    obtain ⟨h1, h2⟩ := hoff v hv
    rw [hJ v hvSg]
    refine ⟨le_sup_right, ?_, ?_, hl.1, hl.2⟩
    · rw [← h1]
      exact Subgroup.map_le_iff_le_comap.1 (h2.trans le_sup_right)
    · rw [← h1]
      exact Subgroup.map_comap_le _ _
  · intro v hv
    exact (hoff v hv).2
  · intro v
    by_cases hvSg : v ∈ D.Sg
    · have hJS : D.J2v v = (D.S v).J2 := by simp [Dat.J2v, hvSg]
      obtain ⟨z, hz⟩ := zEx (hτv v)
      have hdo := SigOk.D_orb (hD.sig v hvSg) (t v) (ht v hvSg) (cv v τ) _ (jv v) (hτv v) (hγv v) (hjv v) z hz
      haveI := hchar v
      have hsl := (stabLe (Ov v) (Kv v) (cv v Δ) (cv v τ) (hΔv v) (hτv v)).1 _ (jv v) (hγv v) (hjv v)
      show ∀ y : DX (cv v Δ) ⧸ (ZD (cv v Δ) ⊔ D.J2v v), _
      rw [hJS]
      intro y
      refine ⟨?_, hdo.2.2.2.2 (hA v hvSg) y⟩
      intro s hs
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hs
      have hs' : jv v s • ((y.out : DX (cv v Δ)) : DX (cv v Δ) ⧸ (ZD (cv v Δ) ⊔ (D.S v).J2)) = y.out := by
        rw [QuotientGroup.out_eq']
        exact hs
      rw [smul_mk_iff] at hs'
      exact hsl y.out s (sup_le_sup_left (SigOk.levelTwoLeIntegral (hD.sig v hvSg)) _ hs')
    · show ∀ y : DX (cv v Δ) ⧸ (ZD (cv v Δ) ⊔ D.J2v v), _
      rw [hJ v hvSg]
      intro y
      exact (finD (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v hvSg) (hτv v) _ (jv v) (hγv v) (hjv v)).2.2 y
  · intro z hz v y
    obtain ⟨c, hc⟩ := hz
    have hsc : IsScal (Units.map (cv v : F →* Kv v) c) ((ι (j z)).1 v) := by
      unfold IsScal
      rw [hι, hj, ← hc]
      simp only [Units.coe_map, MonoidHom.coe_coe, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
        zero_smul, add_zero]
      ext i k : 1
      by_cases hik : i = k
      · subst hik
        ext <;> simp [lmap, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      · ext <;> simp [lmap, hik]
    have hZ : (ι (j z)).1 v ∈ ZD (cv v Δ) := by
      rw [ZD, Subgroup.mem_subgroupOf]
      refine ⟨Units.map (cv v : F →* Kv v) c, ?_⟩
      ext : 1
      simp
      exact hsc.symm
    show y⁻¹ * (ι (j z)).1 v * y ∈ ZD (cv v Δ) ⊔ D.J2v v
    rw [mul_assoc, scal_comm hsc y, ← mul_assoc, inv_mul_cancel, one_mul]
    exact Subgroup.mem_sup_left hZ
  · have hms : ms τ = mass hex.choose (scalE τ)
        ((rpg (fun v : Pl F => (Etau (Kv v) (cv v τ))ˣ) fun v => Cu (Ov v) (cv v τ)).box
          fun v => Cint (Ov v) (cv v τ)) := by
      rw [ms, dif_pos hex]
    have hb1 : ∀ v ∉ D.Sg ∪ hSbfin.toFinset, b v = 1 := by
      intro v hv
      obtain ⟨hvSg, hKD, hunit, hint⟩ := hnotS v hv
      have hl := (hloc v (jv v) (hjv v)).2.2.2 hvSg
      have hl2 := hl.2 hKD hunit
      have hmap : Subgroup.map (jv v) (Cint (Ov v) (cv v τ)) ≤ ZD (cv v Δ) ⊔ D.J2v v := by
        rw [hJ v hvSg, ← (hoff v hv).1]
        exact Subgroup.map_comap_le _ _
      have horb : ∀ y : DX (cv v Δ), fv v (y⁻¹ * (ι δ).1 v * (MonoidHom.id _) y) ≠ 0 →
          ∃ s, ∃ u ∈ ZD (cv v Δ) ⊔ D.J2v v, y = jv v s * u := by
        rw [hJ v hvSg]
        exact hl2.2
      rw [← hl.1]
      exact (UpperTheory.V.Z.Sym.Tf.orbOne _ _ (jv v) (Cint (Ov v) (cv v τ)) (MonoidHom.id _) (ZD (cv v Δ) ⊔ D.J2v v) (fv v) ((ι δ).1 v)
        (conj_sup (hinv v)) (hcomm v) hmap horb).trans hl2.1
    have e := prod_split D.Sg (D.Sg ∪ hSbfin.toFinset) hSg a b
      (fun v => orb (jv v) (Cint (Ov v) (cv v τ)) (MonoidHom.id _) (ZD (cv v Δ) ⊔ D.J2v v) (fv v) ((ι δ).1 v))
      (fun v hv => (hloc v (jv v) (hjv v)).2.2.1 hv) (fun v hv => ((hloc v (jv v) (hjv v)).2.2.2 hv).1) hb1
    rw [hms]
    change _ * ∏ v ∈ D.Sg ∪ hSbfin.toFinset, orb (jv v) (Cint (Ov v) (cv v τ)) (MonoidHom.id _)
      (ZD (cv v Δ) ⊔ D.J2v v) (fv v) ((ι δ).1 v) = _
    rw [e]
    ring

end UpperTheory.V.Z.Sym.Glob
end
