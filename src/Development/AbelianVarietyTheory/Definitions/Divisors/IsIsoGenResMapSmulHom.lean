import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)
open GlobalTheory.Cartier (IsRegularFn IsRegularSec SecMaps germ_resG ext_germK)

namespace GlobalTheory.Vert

theorem shortExact_cokernel_comp {C : Type*} [Category C] [Abelian C] {A B E : C} (f : A ⟶ B)
    (g : B ⟶ E) [Mono g] : (kernelCokernelCompSequence.snakeInput f g).L₃.ShortExact where
  exact := (kernelCokernelCompSequence.snakeInput f g).L₃_exact
  mono_f := (kernelCokernelCompSequence.snakeInput f g).L₂'_exact.mono_g
    ((isZero_kernel_of_mono g).eq_of_src _ _)
  epi_g :=
    have : Epi (kernelCokernelCompSequence.snakeInput f g).L₂.g :=
      inferInstanceAs (Epi (biprod.snd : B ⊞ E ⟶ E))
    (kernelCokernelCompSequence.snakeInput f g).epi_L₃_g

section Divisor

variable {X : Scheme.{0}}

def divMod (I : X.IdealSheafData) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (structureModule I.subscheme)

variable (D D' : EffCartierData X)

theorem secIdeal_canonical :
    ThickeningDetermines.secIdeal D.isLB_lb D.canonical = D.idealSheaf :=
  D.eq_idealSheaf fun x =>
    have ⟨i, hi⟩ := D.exists_mem x
    have ⟨W, hx, hW⟩ := EffCartierData.exists_affine_le hi
    ⟨W, i, hW, hx, ideal_secIdeal D.isLB_lb D.canonical W i hW⟩

theorem nonempty_cokernel_iso {G : X.Modules} [G.IsQuasicoherent] {φ : G ⟶ structureModule X}
    (h : IsMulBy φ D.canonical) : Nonempty (cokernel φ ≅ divMod D.idealSheaf) := by
  rw [← secIdeal_canonical]
  exact ⟨(h.exists_cokernel_iso D.isLB_lb _ (surjective_and_ker_unitToPush_subschemeι _)).choose⟩

theorem nonempty_cut_iso :
    Nonempty (cut (structureModule X) D.isLB_lb D.canonical ≅ divMod D.idealSheaf) :=
  have := Twist.isQuasicoherent_twist (F := structureModule X) (Twist.isLB_lbZPow D.isLB_lb (-1))
  nonempty_cokernel_iso D (isMulBy_cutHom _ _ _)

instance mono_cutHom_canonical : Mono (cutHom (structureModule X) D.isLB_lb D.canonical) :=
  mono_of_locally_app_injective _ fun W x hx =>
    have ⟨i, hi⟩ := D.exists_mem x
    ⟨W ⊓ D.U i, ⟨hx, hi⟩, inf_le_left,
      ((isMulBy_cutHom _ D.isLB_lb D.canonical).injective_app_iff i inf_le_right).2
        fun _ _ h => (mul_cancel_left_mem_nonZeroDivisors (D.regular i _ inf_le_right)).1 h⟩

instance isFiniteQC_divMod : IsFiniteQC (divMod D.idealSheaf) :=
  (nonempty_cut_iso D).elim fun e => .of_iso e

theorem support_divMod : support (divMod D.idealSheaf) = D.idealSheaf.support := by
  obtain ⟨e⟩ := nonempty_cut_iso D
  rw [← support_eq_of_iso e, support_cut_eq_inter, support_structureModule, Set.univ_inter,
    secIdeal_canonical]

theorem exists_shortExact_add : ∃ S : ShortComplex X.Modules, S.ShortExact ∧
    Nonempty (S.X₁ ≅ twistZ (divMod D.idealSheaf) D'.lb (-1)) ∧
    Nonempty (S.X₂ ≅ divMod (D.idealSheaf * D'.idealSheaf)) ∧
    Nonempty (S.X₃ ≅ divMod D'.idealSheaf) := by
  have hM := Twist.isLB_lbZPow D'.isLB_lb (-1)
  let a := Twist.map (lbZPow D'.lb (-1)) (cutHom (structureModule X) D.isLB_lb D.canonical)
  let b := cutHom (structureModule X) D'.isLB_lb D'.canonical
  have := Twist.preservesFiniteColimits_twistFunctor hM
  refine ⟨_, shortExact_cokernel_comp a b, (nonempty_cut_iso D).map fun e =>
    (PreservesCokernel.iso (twistFunctor _) _).symm ≪≫ (twistFunctor _).mapIso e, ?_,
    nonempty_cut_iso D'⟩
  rw [← D.idealSheaf_add]
  have := Twist.isQuasicoherent_twist (F := structureModule X) (Twist.isLB_lbZPow D.isLB_lb (-1))
  have := Twist.isQuasicoherent_twist (F := twistZ (structureModule X) D.lb (-1)) hM
  refine nonempty_cokernel_iso (D.add D') fun p V h => ⟨(Twist.zchartEquiv D'.isLB_lb (-1) p.2
    (h.trans inf_le_right)).trans (Twist.zchartEquiv D.isLB_lb (-1) p.1 (h.trans inf_le_left)),
    fun t => ?_⟩
  have e : Twist.zchartEquiv D'.isLB_lb (-1) p.2 (h.trans inf_le_right) (a.app V t) =
      (cutHom (structureModule X) D.isLB_lb D.canonical).app V
        (Twist.zchartEquiv D'.isLB_lb (-1) p.2 (h.trans inf_le_right) t) :=
    Twist.chartEquiv_map_app hM _ _ _ t
  change b.app V (a.app V t) = resG X h ((D.add D').f (p.1, p.2)) • _
  rw [cutHom_app _ _ _ p.2 (h.trans inf_le_right), e, cutHom_app _ _ _ p.1 (h.trans inf_le_left),
    smul_smul, mul_comm]
  exact congrArg (· • _) (D.resG_add_f D' p.1 p.2 h).symm

theorem idealSheaf_eq_of_germ
    (h : ∀ (x : X) (i : D.ι) (j : D'.ι) (hi : x ∈ D.U i) (hj : x ∈ D'.U j),
      Associated ((X.presheaf.germ _ x hi).hom (D.f i)) ((X.presheaf.germ _ x hj).hom (D'.f j))) :
    D.idealSheaf = D'.idealSheaf := by
  ext W a
  rw [EffCartierData.idealSheaf, EffCartierData.idealSheaf, EffCartierData.mem_locIdeal_iff,
    EffCartierData.mem_locIdeal_iff]
  refine ⟨fun H j x hx hj => ?_, fun H i x hx hi => ?_⟩
  · obtain ⟨i, hi⟩ := D.exists_mem x
    exact (h x i j hi hj).symm.dvd.trans (H i x hx hi)
  · obtain ⟨j, hj⟩ := D'.exists_mem x
    exact (h x i j hi hj).dvd.trans (H j x hx hj)

theorem germ_add_f (x : X) (p : (D.add D').ι) (h : x ∈ (D.add D').U p) :
    (X.presheaf.germ _ x h).hom ((D.add D').f p) =
      (X.presheaf.germ _ x h.1).hom (D.f p.1) * (X.presheaf.germ _ x h.2).hom (D'.f p.2) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (germ_resG _ _ _ _) (germ_resG _ _ _ _))

theorem idealSheaf_mul_left_cancel {E D D' : EffCartierData X}
    (h : E.idealSheaf * D.idealSheaf = E.idealSheaf * D'.idealSheaf) :
    D.idealSheaf = D'.idealSheaf := by
  rw [← E.idealSheaf_add, ← E.idealSheaf_add] at h
  refine idealSheaf_eq_of_germ D D' fun x i j hi hj => ?_
  obtain ⟨k, hk⟩ := E.exists_mem x
  obtain ⟨u, hu⟩ := (EffCartierData.associated_of_idealSheaf_eq _ _ h (k, j) (k, i)).map
    (X.presheaf.germ _ x (show x ∈ E.U k ⊓ D'.U j ⊓ (E.U k ⊓ D.U i) from ⟨⟨hk, hj⟩, hk, hi⟩)).hom
  refine ⟨u, (mul_cancel_left_mem_nonZeroDivisors
    (Cartier.isRegularFn_iff_germ.1 (E.regular k) x hk)).1 ?_⟩
  rw [← mul_assoc]
  exact (congrArg (· * _) ((germ_resG _ _ _ _).trans (germ_add_f E D x (k, i) ⟨hk, hi⟩))).symm.trans
    (hu.trans ((germ_resG _ _ _ _).trans (germ_add_f E D' x (k, j) ⟨hk, hj⟩)))

theorem le_basicOpen_of_isUnit {U V : X.Opens} (h : V ≤ U) {a : Γ(X, U)}
    (ha : IsUnit (resG X h a)) : V ≤ X.basicOpen a := by
  rw [← X.basicOpen_of_isUnit ha]
  exact (X.basicOpen_res a (homOfLE h).op).le.trans inf_le_right

end Divisor

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

structure Model (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] where

  X : Scheme.{0}

  str : X ⟶ Sp O

  [isIntegral : IsIntegral X]

  isProjOver : IsProjOver str

  [flat : Flat str]

attribute [instance] Model.isIntegral Model.flat

theorem topologicalKrullDim_pspace (N : ℕ) :
    topologicalKrullDim (PSpace O N) = (N + 1 : ℕ) := by
  have hc : ∀ i, topologicalKrullDim (ProjSpace.chart O N i : Set (PSpace O N)) = (N + 1 : ℕ) :=
    fun i => by
      rw [topologicalKrullDim_eq_of_isEmbedding (ProjSpace.chartι O N i).isOpenEmbedding.isEmbedding
        (congrArg SetLike.coe (ProjSpace.opensRange_chartι O N i))]
      refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
        (R := MvPolynomial {j // j ≠ i} O)).trans ?_
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
      simp [add_comm]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
    ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart O N x
  exact ⟨_, (ProjSpace.chart O N i).isOpen, hi, (hc i).le⟩

namespace Model

variable {O} (Z Z₁ Z₂ : Model O)

instance algebraTop : Algebra O Γ(Z.X, ⊤) := algebraΓOfHom Z.str

abbrev const (g : O) : Γ(Z.X, ⊤) := algebraMap O Γ(Z.X, ⊤) g

theorem const_eq (g : O) : algebraMap O Γ(Z.X, ⊤) g =
    Z.str.appTop ((Scheme.ΓSpecIso (.of O)).inv g) := rfl

instance isNoetherian : AlgebraicGeometry.IsNoetherian Z.X :=
  isNoetherian_of_isProjOver Z.isProjOver

instance isProper : IsProper Z.str := (isProper_and_exists_isAmpleLB_of_isProjOver Z.isProjOver).1

theorem exists_isAmpleLB : ∃ A : LB Z.X, IsAmpleLB A :=
  (isProper_and_exists_isAmpleLB_of_isProjOver Z.isProjOver).2

def gen : Z.X.Opens :=
  Z.str ⁻¹ᵁ ⟨{closedPoint O}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint O).isOpen_compl⟩

variable {Z} in

theorem mem_gen {x : Z.X} : x ∈ Z.gen ↔ Z.str x ≠ closedPoint O := Iff.rfl

variable {Z} in

theorem mem_gen_iff_eq_bot {x : Z.X} : x ∈ Z.gen ↔ (Z.str x).asIdeal = ⊥ := by
  refine ⟨fun h => by_contra fun h' => h (PrimeSpectrum.ext
    (eq_maximalIdeal ((Z.str x).isPrime.isMaximal h'))), fun h h' => ?_⟩
  exact IsDiscreteValuationRing.not_a_field O ((congrArg PrimeSpectrum.asIdeal h').symm.trans h)

variable {Z} in

theorem mem_basicOpen_const {x : Z.X} {g : O} :
    x ∈ Z.X.basicOpen (Z.const g) ↔ g ∉ (Z.str x).asIdeal := by
  rw [const, const_eq, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

theorem gen_le_basicOpen {g : O} (hg : g ≠ 0) : Z.gen ≤ Z.X.basicOpen (Z.const g) :=
  fun _ hx => mem_basicOpen_const.2 (by rwa [mem_gen_iff_eq_bot.1 hx])

theorem gen_eq_basicOpen {g : O} (hg : g ≠ 0) (hm : g ∈ maximalIdeal O) :
    Z.gen = Z.X.basicOpen (Z.const g) :=
  (Z.gen_le_basicOpen hg).antisymm fun _ hx h => mem_basicOpen_const.1 hx (h ▸ hm)

theorem isUnit_const {g : O} (hg : g ≠ 0) {V : Z.X.Opens} (h : V ≤ Z.gen) :
    IsUnit (resG Z.X (le_top : V ≤ ⊤) (Z.const g)) := by
  rw [← resG_resG (Z.X.basicOpen_le (Z.const g)) (h.trans (Z.gen_le_basicOpen hg))]
  exact (Z.X.toRingedSpace.isUnit_res_basicOpen _).map _

theorem isRegularFn_const {g : O} (hg : g ≠ 0) : IsRegularFn (Z.const g) :=
  (EffCartierData.isRegularFn_spec (mem_nonZeroDivisors_of_ne_zero hg)).app_of_flat Z.str

theorem genericPoint_mem_gen : genericPoint Z.X ∈ Z.gen := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [Z.gen_eq_basicOpen hϖ.ne_zero hϖ.not_isUnit]
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 (mt (basicOpen_eq_bot_iff _).1
    (Z.isRegularFn_const hϖ.ne_zero).ne_zero)
  exact VB.genericPoint_mem hx

theorem exists_notMem_gen : ∃ x : Z.X, x ∉ Z.gen := by
  obtain ⟨x, hx⟩ := (specializes_closedPoint (Z.str (genericPoint Z.X))).mem_closed
    Z.str.isClosedMap.isClosed_range ⟨_, rfl⟩
  exact ⟨x, fun h => h hx⟩

theorem resG_injective {V W : Z.X.Opens} (h : W ≤ V) (hW : Z.gen ⊓ V ≤ W) :
    Function.Injective (resG Z.X h) := fun _ _ e => ext_germK fun hV => by
  rw [← germ_resG h _ (hW ⟨Z.genericPoint_mem_gen, hV⟩), e, germ_resG]

theorem dim_special_add_one_le :
    topologicalKrullDim ((Z.gen : Set Z.X)ᶜ : Set Z.X) + 1 ≤ topologicalKrullDim Z.X := by
  have := topologicalKrullDim_add_one_le Z.gen.isOpen.isClosed_compl isClosed_univ
    fun x _ => ⟨genericPoint Z.X, trivial, not_not.2 Z.genericPoint_mem_gen,
      genericPoint_specializes x⟩
  rwa [topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id] at this

theorem exists_dim_eq : ∃ d : ℕ, topologicalKrullDim Z.X = (d + 1 : ℕ) := by
  obtain ⟨N, i, _, -⟩ := Z.isProjOver
  have h₁ := i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans_eq
    (topologicalKrullDim_pspace O N)
  have h₂ := Z.dim_special_add_one_le
  have h₃ : topologicalKrullDim ((Z.gen : Set Z.X)ᶜ : Set Z.X) ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 (nonempty_subtype.2 Z.exists_notMem_gen))
  generalize topologicalKrullDim Z.X = a at *
  generalize topologicalKrullDim ((Z.gen : Set Z.X)ᶜ : Set Z.X) = b at *
  lift b to ℕ∞ using h₃
  have h₄ : (1 : WithBot ℕ∞) ≤ a := le_trans (by exact_mod_cast le_add_self) h₂
  lift a to ℕ∞ using by rintro rfl; simp at h₄
  lift a to ℕ using by rintro rfl; exact absurd h₁ (by exact_mod_cast (ENat.natCast_lt_top _).not_ge)
  have : 1 ≤ a := by exact_mod_cast h₄
  exact ⟨a - 1, by rw [Nat.sub_add_cancel this]; rfl⟩

def relDim : ℕ := Z.exists_dim_eq.choose

theorem dim_eq : topologicalKrullDim Z.X = (Z.relDim + 1 : ℕ) := Z.exists_dim_eq.choose_spec

variable {Z} in

theorem relDim_eq_iff {d : ℕ} : Z.relDim = d ↔ topologicalKrullDim Z.X = (d + 1 : ℕ) := by
  rw [dim_eq]
  exact ⟨fun h => h ▸ rfl, fun h => Nat.succ_injective (by exact_mod_cast h)⟩

theorem dim_special_le : topologicalKrullDim ((Z.gen : Set Z.X)ᶜ : Set Z.X) ≤ Z.relDim :=
  ENat.WithBot.add_le_add_one_right_iff.1 (Z.dim_special_add_one_le.trans_eq Z.dim_eq)

variable (O) in

def projSpace (N : ℕ) : Model O where
  X := PSpace O N
  str := PSpace.str O N
  isIntegral := ProjSpace.isIntegral_of_isDomain O N
  isProjOver := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  flat := Models.flat_projSpace O N

@[simp] theorem relDim_projSpace (N : ℕ) : (projSpace O N).relDim = N :=
  relDim_eq_iff.2 (topologicalKrullDim_pspace O N)

structure Hom (Z₁ Z : Model O) where

  f : Z₁.X ⟶ Z.X

  comp_str : f ≫ Z.str = Z₁.str

  [surjective : Surjective f]

attribute [instance] Hom.surjective

def Hom.id : Hom Z Z := ⟨𝟙 _, Category.id_comp _⟩

def Hom.comp {Z Z₁ Z₂ : Model O} (g : Hom Z₂ Z₁) (f : Hom Z₁ Z) : Hom Z₂ Z :=
  ⟨g.f ≫ f.f, by rw [Category.assoc, f.comp_str, g.comp_str]⟩

section Over

variable {Z Z₁} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
include hf

theorem isProper_of_comp_str : IsProper f :=
  have : IsProper (f ≫ Z.str) := hf ▸ Z₁.isProper
  .of_comp f Z.str

theorem preimage_gen : f ⁻¹ᵁ Z.gen = Z₁.gen := by
  rw [gen, ← Scheme.Hom.comp_preimage, hf]; rfl

theorem appTop_const (g : O) : f.appTop (Z.const g) = Z₁.const g := by
  rw [const, const, const_eq, const_eq, ← hf, Scheme.Hom.comp_appTop]; rfl

end Over

def IsVertical (F : Z.X.Modules) : Prop := ∀ x ∈ support F, x ∉ Z.gen

variable {Z} {F G : Z.X.Modules}

theorem IsVertical.suppDim_lt (h : Z.IsVertical F) : suppDim F < (Z.relDim + 1 : ℕ) :=
  ((topologicalKrullDim_mono h).trans Z.dim_special_le).trans_lt
    (by exact_mod_cast Z.relDim.lt_succ_self)

theorem IsVertical.finiteLenTwists [IsFiniteQC F] (h : Z.IsVertical F) : FiniteLenTwists O F :=
  have ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  finiteLenTwists_of_support Z.const_eq Z.isProjOver h.suppDim_lt hϖ.ne_zero
    (Z.gen_eq_basicOpen hϖ.ne_zero hϖ.not_isUnit ▸ h)

theorem IsVertical.diffVanish [IsFiniteQC F] (h : Z.IsVertical F) :
    DiffVanish (Z.relDim + 1) (chiLenPic O F) :=
  have ⟨_, hA⟩ := Z.exists_isAmpleLB
  diffVanish_chiLenPic hA h.finiteLenTwists h.suppDim_lt

def IsVertical.deg [IsFiniteQC F] (h : Z.IsVertical F) : PicSym Z.X →ₗ[ℚ] ℚ := picForm h.diffVanish

theorem IsVertical.deg_prod [IsFiniteQC F] (h : Z.IsVertical F) {ι : Type} [Fintype ι]
    {L : ι → LB Z.X} (hL : ∀ i, (L i).IsLB) : h.deg (∏ i, c1 (L i) (hL i)) =
      if Fintype.card ι = Z.relDim then (interLen O F L : ℚ) else 0 := by
  rw [interLen_eq_multiDiff O F hL]
  exact picForm_prod _ fun i => cls (L i) (hL i)

end Model

namespace Model

variable {O} (Z Z₁ : Model O)

def effVert : Submonoid Z.X.IdealSheafData where
  carrier := {I | FinalTheorems.EffCartier I ∧ ∀ x ∈ I.support, x ∉ Z.gen}
  one_mem' := ⟨(EffCartierData.idealSheaf_zero (X := Z.X)).subst
    (EffCartierData.zero _).effCartier_idealSheaf, fun x hx => by
      rw [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top] at hx
      exact hx.elim⟩
  mul_mem' := fun {I J} hI hJ => by
    obtain ⟨D, rfl⟩ := EffCartierData.exists_idealSheaf_eq hI.1
    obtain ⟨D', rfl⟩ := EffCartierData.exists_idealSheaf_eq hJ.1
    exact ⟨D.idealSheaf_add D' ▸ (D.add D').effCartier_idealSheaf,
      fun x hx => Or.elim hx (hI.2 x) (hJ.2 x)⟩

variable {Z}

def effData (I : Z.effVert) : EffCartierData Z.X :=
  (EffCartierData.exists_idealSheaf_eq I.2.1).choose

@[simp] theorem idealSheaf_effData (I : Z.effVert) : (effData I).idealSheaf = I.1 :=
  (EffCartierData.exists_idealSheaf_eq I.2.1).choose_spec

def effMk (D : EffCartierData Z.X) (h : ∀ i, Z.gen ⊓ D.U i ≤ Z.X.basicOpen (D.f i)) : Z.effVert :=
  ⟨D.idealSheaf, D.effCartier_idealSheaf, fun x hx hg =>
    have ⟨i, hi⟩ := D.exists_mem x
    (D.mem_support_iff i hi).1 hx (h i ⟨hg, hi⟩)⟩

theorem le_basicOpen_effData (I : Z.effVert) (i : (effData I).ι) :
    Z.gen ⊓ (effData I).U i ≤ Z.X.basicOpen ((effData I).f i) := fun x hx =>
  by_contra fun h => I.2.2 x (idealSheaf_effData I ▸ ((effData I).mem_support_iff i hx.2).2 h) hx.1

instance : IsCancelMul Z.effVert :=
  have : IsLeftCancelMul Z.effVert := ⟨fun E D D' h => Subtype.ext <| by
    rw [← idealSheaf_effData, ← idealSheaf_effData]
    refine idealSheaf_mul_left_cancel (E := effData E) ?_
    simp only [idealSheaf_effData]
    exact congrArg Subtype.val h⟩
  CommMagma.IsLeftCancelMul.toIsCancelMul _

instance (I : Z.effVert) : IsFiniteQC (divMod I.1) := idealSheaf_effData I ▸ isFiniteQC_divMod _

theorem isVertical_divMod (I : Z.effVert) : Z.IsVertical (divMod I.1) := fun x hx =>
  I.2.2 x (by rwa [← idealSheaf_effData, support_divMod, idealSheaf_effData] at hx)

def effCls (I : Z.effVert) : Pic Z.X := cls _ (effData I).isLB_lb

theorem effCls_eq {I : Z.effVert} {D : EffCartierData Z.X} (h : D.idealSheaf = I.1) :
    effCls I = cls _ D.isLB_lb :=
  (cls_eq_iff _ _).2 (EffCartierData.lbIso_of_idealSheaf_eq _ _ ((idealSheaf_effData I).trans h.symm))

theorem effCls_mul (I J : Z.effVert) : effCls (I * J) = effCls I + effCls J := by
  have h := (cls_eq_iff (effData J).isLB_lb (Semi.LB.isLB_div ((effData I).add (effData J)).isLB_lb
    (effData I).isLB_lb)).2 ((effData I).lbIso_add (effData J))
  rw [cls_div ((effData I).add (effData J)).isLB_lb (effData I).isLB_lb] at h
  rw [effCls_eq (D := (effData I).add (effData J)) (by simp [EffCartierData.idealSheaf_add]),
    effCls, effCls, h, add_sub_cancel]

def effDeg (I : Z.effVert) : PicSym Z.X →ₗ[ℚ] ℚ := (isVertical_divMod I).deg

theorem effDeg_mul (I J : Z.effVert) : effDeg (I * J) = effDeg I + effDeg J := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_shortExact_add (effData I) (effData J)
  simp only [idealSheaf_effData] at e₁ e₂ e₃
  have hM := Twist.isLB_lbZPow (effData J).isLB_lb (-1)
  refine picForm_eq_add (isVertical_divMod (I * J)).diffVanish (isVertical_divMod I).diffVanish
    (isVertical_divMod J).diffVanish (cls _ hM) fun c => ?_
  have := chiLenPic_shortExact hS (((isVertical_divMod I).finiteLenTwists.twist hM).of_iso e₁.symm)
    ((isVertical_divMod J).finiteLenTwists.of_iso e₃.symm)
  rw [chiLenPic_congr O e₁, chiLenPic_congr O e₂, chiLenPic_congr O e₃] at this
  exact (congrFun this c).trans (congrArg (· + _) (chiLenPic_twist O _ hM c))

variable (Z) in

abbrev VDivZ : Type := Algebra.GrothendieckAddGroup (Additive Z.effVert)

def ofEff (I : Z.effVert) : Z.VDivZ := Algebra.GrothendieckAddGroup.of (Additive.ofMul I)

theorem ofEff_mul (I J : Z.effVert) : ofEff (I * J) = ofEff I + ofEff J :=
  map_add Algebra.GrothendieckAddGroup.of (Additive.ofMul I) (Additive.ofMul J)

@[simp] theorem ofEff_one : ofEff (1 : Z.effVert) = 0 := map_zero Algebra.GrothendieckAddGroup.of

theorem ofEff_injective : Function.Injective (ofEff (Z := Z)) :=
  Algebra.GrothendieckAddGroup.of_injective (M := Additive Z.effVert)

theorem exists_eq_ofEff_sub (D : Z.VDivZ) : ∃ I J, D = ofEff I - ofEff J := by
  induction D using AddLocalization.induction_on with
  | H p =>
    refine ⟨p.1.toMul, p.2.1.toMul, ?_⟩
    exact ((Algebra.GrothendieckAddGroup.mk_sub_mk p.1 p.2.1 0 0).trans (by simp)).symm

def IsEff (D : Z.VDivZ) : Prop := ∃ I, ofEff I = D

def vLift {A : Type*} [AddCommGroup A] (f : Z.effVert → A) (h : ∀ I J, f (I * J) = f I + f J) :
    Z.VDivZ →+ A :=
  Algebra.GrothendieckAddGroup.lift (AddMonoidHom.mk' (fun I => f I.toMul) h)

@[simp] theorem vLift_ofEff {A : Type*} [AddCommGroup A] (f : Z.effVert → A)
    (h : ∀ I J, f (I * J) = f I + f J) (I : Z.effVert) : vLift f h (ofEff I) = f I :=
  DFunLike.congr_fun (Algebra.GrothendieckAddGroup.lift.symm_apply_apply
    (AddMonoidHom.mk' (fun I : Additive Z.effVert => f I.toMul) h)) (Additive.ofMul I)

theorem vDivZ_hom_ext {A : Type*} [AddCommGroup A] {f g : Z.VDivZ →+ A}
    (h : ∀ I, f (ofEff I) = g (ofEff I)) : f = g := AddMonoidHom.ext fun D => by
  obtain ⟨I, J, rfl⟩ := exists_eq_ofEff_sub D
  rw [map_sub, map_sub, h, h]

variable (Z)

def vCls : Z.VDivZ →+ Pic Z.X := vLift effCls effCls_mul

def vDeg : Z.VDivZ →+ (PicSym Z.X →ₗ[ℚ] ℚ) := vLift effDeg effDeg_mul

variable {Z} in

@[simp] theorem vCls_ofEff (I : Z.effVert) : Z.vCls (ofEff I) = effCls I := vLift_ofEff _ _ I

variable {Z} in

@[simp] theorem vDeg_ofEff (I : Z.effVert) : Z.vDeg (ofEff I) = effDeg I := vLift_ofEff _ _ I

variable {Z} in

theorem vDeg_ofEff_prod (I : Z.effVert) {ι : Type} [Fintype ι] {L : ι → LB Z.X}
    (hL : ∀ i, (L i).IsLB) : Z.vDeg (ofEff I) (∏ i, c1 (L i) (hL i)) =
      if Fintype.card ι = Z.relDim then (interLen O (divMod I.1) L : ℚ) else 0 := by
  rw [vDeg_ofEff]
  exact (isVertical_divMod I).deg_prod hL

variable {Z} in

theorem vDeg_eq_zero (D : Z.VDivZ) {n : ℕ} (hn : n ≠ Z.relDim) {x : PicSym Z.X}
    (hx : x ∈ symDeg (SmallPic Z.X) n) : Z.vDeg D x = 0 := by
  obtain ⟨I, J, rfl⟩ := exists_eq_ofEff_sub D
  rw [map_sub, vDeg_ofEff, vDeg_ofEff, LinearMap.sub_apply, effDeg, effDeg, IsVertical.deg,
    IsVertical.deg, picForm_eq_zero _ hn hx, picForm_eq_zero _ hn hx, sub_zero]

def effConst (g : O) (hg : g ≠ 0) : Z.effVert :=
  effMk (.principal (Z.const g) (Z.isRegularFn_const hg))
    fun _ => inf_le_left.trans (Z.gen_le_basicOpen hg)


def div (g : O) (hg : g ≠ 0) : Z.VDivZ := ofEff (Z.effConst g hg)

theorem div_mul {g g' : O} (hg : g ≠ 0) (hg' : g' ≠ 0) (h : g * g' ≠ 0) :
    Z.div (g * g') h = Z.div g hg + Z.div g' hg' := by
  rw [div, div, div, ← ofEff_mul]
  refine congrArg ofEff (Subtype.ext ((idealSheaf_eq_of_germ _ _ fun x i j hi hj => ?_).trans
    (EffCartierData.idealSheaf_add _ _)))
  rw [germ_add_f]
  exact Associated.of_eq ((congrArg _ (map_mul _ g g')).trans (map_mul _ _ _))

theorem div_of_isUnit {g : O} (h : IsUnit g) (hg : g ≠ 0) : Z.div g hg = 0 := by
  rw [← ofEff_one]
  refine congrArg ofEff (Subtype.ext ((idealSheaf_eq_of_germ _ _ fun x i j hi hj => ?_).trans
    EffCartierData.idealSheaf_zero))
  exact (associated_one_iff_isUnit.2 (h.map (algebraMap O Γ(Z.X, ⊤)))).map _

theorem div_pow {g : O} (hg : g ≠ 0) (n : ℕ) (h : g ^ n ≠ 0) :
    Z.div (g ^ n) h = n • Z.div g hg := by
  induction n with
  | zero => simpa using Z.div_of_isUnit isUnit_one _
  | succ n ih => simp only [pow_succ, succ_nsmul, Z.div_mul (pow_ne_zero n hg) hg, ih]

theorem div_eq_addVal_smul {ϖ g : O} (hϖ : Irreducible ϖ) (hg : g ≠ 0) :
    Z.div g hg = (IsDiscreteValuationRing.addVal O g).toNat • Z.div ϖ hϖ.ne_zero := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl, ENat.toNat_natCast,
    Z.div_mul u.ne_zero (pow_ne_zero n hϖ.ne_zero), Z.div_of_isUnit u.isUnit, zero_add, div_pow]

@[simp] theorem vCls_div (g : O) (hg : g ≠ 0) : Z.vCls (Z.div g hg) = 0 := by
  rw [div, vCls_ofEff, effCls_eq (D := .principal (Z.const g) (Z.isRegularFn_const hg)) rfl]
  simp only [EffCartierData.lb_principal]
  rfl

section Pull

variable {Z Z₁} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
include hf

theorem keepsRegular {I : Z.effVert} {D : EffCartierData Z.X} (h : D.idealSheaf = I.1) :
    D.KeepsRegular f :=
  D.keepsRegular_of_notMem_support f (y := genericPoint Z₁.X) fun hx =>
    I.2.2 _ (h ▸ hx) ((preimage_gen hf).ge Z₁.genericPoint_mem_gen)

def effPull (I : Z.effVert) : Z₁.effVert :=
  ⟨I.1.comap f, idealSheaf_effData I ▸ ((effData I).keepsRegular_iff_effCartier f).1
    (keepsRegular hf (idealSheaf_effData I)), fun x hx h => by
      rw [Scheme.IdealSheafData.support_comap] at hx
      exact I.2.2 _ hx ((preimage_gen hf).ge h)⟩

theorem effPull_mul (I J : Z.effVert) : effPull hf (I * J) = effPull hf I * effPull hf J := by
  refine Subtype.ext ?_
  have hI := keepsRegular hf (idealSheaf_effData I)
  have hJ := keepsRegular hf (idealSheaf_effData J)
  change (I.1 * J.1).comap f = I.1.comap f * J.1.comap f
  rw [← idealSheaf_effData I, ← idealSheaf_effData J, ← EffCartierData.idealSheaf_add,
    ← EffCartierData.idealSheaf_pull _ f (hI.add hJ), EffCartierData.pull_add _ _ f hI hJ,
    EffCartierData.idealSheaf_add, EffCartierData.idealSheaf_pull, EffCartierData.idealSheaf_pull]

def vPull : Z.VDivZ →+ Z₁.VDivZ :=
  vLift (fun I => ofEff (effPull hf I)) fun I J => by rw [effPull_mul, ofEff_mul]

@[simp] theorem vPull_ofEff (I : Z.effVert) : vPull hf (ofEff I) = ofEff (effPull hf I) :=
  vLift_ofEff _ _ I

theorem vCls_vPull (D : Z.VDivZ) : Z₁.vCls (vPull hf D) = pull f (Z.vCls D) := by
  refine DFunLike.congr_fun (vDivZ_hom_ext (f := Z₁.vCls.comp (vPull hf))
    (g := (pull f).comp Z.vCls) fun I => ?_) D
  have hI := keepsRegular hf (idealSheaf_effData I)
  simp only [AddMonoidHom.comp_apply, vPull_ofEff, vCls_ofEff]
  rw [effCls_eq (D := (effData I).pull f hI) (by
    rw [EffCartierData.idealSheaf_pull, idealSheaf_effData]; rfl), effCls,
    ← cls_pull _ f (Semi.LB.isLB_pull (effData I).isLB_lb f), cls_eq_iff]
  exact (effData I).lbIso_pull f hI

@[simp] theorem vPull_div (g : O) (hg : g ≠ 0) : vPull hf (Z.div g hg) = Z₁.div g hg := by
  rw [div, vPull_ofEff]
  refine congrArg ofEff (Subtype.ext ((EffCartierData.idealSheaf_pull _ f
    (keepsRegular hf (I := Z.effConst g hg) rfl)).symm.trans
      (idealSheaf_eq_of_germ _ _ fun x i j hi hj => ?_)))
  exact Associated.of_eq (congrArg _ (appTop_const hf g))

end Pull

end Model

variable {O} in

structure VertDiv (Z : Model O) where

  M : LB Z.X

  isLB : M.IsLB

  t : Γ(toMod M, Z.gen)

  isUnit : ∀ i, IsUnit (coord t i)

namespace VertDiv

open Model

variable {O} {Z : Model O} (P P' P'' : VertDiv Z)

def eqn (i : P.M.ι) {W : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) : Γ(Z.X, W) :=
  resG Z.X h (coord P.t i)

theorem isUnit_eqn (i : P.M.ι) {W : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) : IsUnit (P.eqn i h) :=
  (P.isUnit i).map _

@[simp] theorem resG_eqn (i : P.M.ι) {W W' : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) (h' : W' ≤ W) :
    resG Z.X h' (P.eqn i h) = P.eqn i (h'.trans h) := resG_resG _ _ _

theorem eqn_rel (i j : P.M.ι) {W : Z.X.Opens} (hi : W ≤ Z.gen ⊓ P.M.U i)
    (hj : W ≤ Z.gen ⊓ P.M.U j) (hij : W ≤ P.M.U i ⊓ P.M.U j) :
    P.eqn i hi = resG Z.X hij (P.M.g i j : Γ(Z.X, P.M.U i ⊓ P.M.U j)) * P.eqn j hj :=
  LB.coord_rel P.t i j hi hj hij

theorem eqn_mul_rel (i j : P.M.ι) (i' j' : P'.M.ι) {W V : Z.X.Opens} (hi : W ≤ Z.gen ⊓ P.M.U i)
    (hj : W ≤ Z.gen ⊓ P.M.U j) (hi' : W ≤ Z.gen ⊓ P'.M.U i') (hj' : W ≤ Z.gen ⊓ P'.M.U j')
    (h : W ≤ V) (hij : V ≤ P.M.U i ⊓ P.M.U j) (hij' : V ≤ P'.M.U i' ⊓ P'.M.U j') :
    P.eqn i hi * P'.eqn i' hi' =
      resG Z.X h (res hij (P.M.g i j) * res hij' (P'.M.g i' j')).val *
        (P.eqn j hj * P'.eqn j' hj') := by
  rw [P.eqn_rel i j hi hj (h.trans hij), P'.eqn_rel i' j' hi' hj' (h.trans hij'), mul_mul_mul_comm,
    Units.val_mul, map_mul, val_res, val_res, resG_resG, resG_resG]

def ofUnits (M : LB Z.X) (hM : M.IsLB) (u : ∀ i, Γ(Z.X, Z.gen ⊓ M.U i))
    (hu : ∀ i, IsUnit (u i)) (h : u ∈ secOn M Z.gen) : VertDiv Z :=
  ⟨M, hM, LB.mkSec u h, hu⟩

variable (Z) in

def zero : VertDiv Z :=
  ofUnits (LB.triv _) (LB.isLB_triv _) (fun _ => 1) (fun _ => isUnit_one) fun _ _ => by
    change _ = resG Z.X _ 1 * _
    simp only [map_one, mul_one]

variable (Z) in

def const (g : O) (hg : g ≠ 0) : VertDiv Z :=
  ofUnits (LB.triv _) (LB.isLB_triv _) (fun _ => resG Z.X le_top (Z.const g))
    (fun _ => Z.isUnit_const hg inf_le_left) fun _ _ => by
      change _ = resG Z.X _ 1 * _
      simp only [map_one, one_mul, resG_resG]

def add : VertDiv Z :=
  ofUnits (tens P.M P'.M) (isLB_tens P.isLB P'.isLB)
    (fun p => P.eqn p.1 (inf_le_inf_left _ inf_le_left) * P'.eqn p.2 (inf_le_inf_left _ inf_le_right))
    (fun _ => (P.isUnit_eqn _ _).mul (P'.isUnit_eqn _ _)) fun p q => by
      simp only [map_mul, resG_eqn]
      exact eqn_mul_rel P P' p.1 q.1 p.2 q.2 _ _ _ _ _ _ _

def neg : VertDiv Z :=
  ofUnits (dual P.M) (isLB_dual P.isLB) (fun i => ((P.isUnit i).unit⁻¹).val)
    (fun _ => Units.isUnit _) fun i j => by
      have : res (inf_le_left : Z.gen ⊓ P.M.U i ⊓ P.M.U j ≤ _) (P.isUnit i).unit =
          res (inf_le_inf_right _ inf_le_right) (P.M.g i j) *
            res (inf_le_inf_right _ inf_le_left) (P.isUnit j).unit :=
        Units.ext (LB.coord_mem P.t i j)
      have := congrArg (fun u => Units.val u⁻¹) this
      simp only [mul_inv, ← map_inv] at this
      exact this

def ofEff (I : Z.effVert) : VertDiv Z :=
  ⟨(effData I).lb, (effData I).isLB_lb, ofSec (effData I).canonical _, fun i => by
    refine (resG_resG (Z.X.basicOpen_le ((effData I).f i)) (le_basicOpen_effData I i) _).subst ?_
    exact (Z.X.toRingedSpace.isUnit_res_basicOpen _).map _⟩

def IsIsom : Prop := ∃ w : LB.Iso P.M P'.M, w.IsGen ∧ ∀ (p : P'.M.ι) (q : P.M.ι),
  P'.eqn p (inf_le_inf_left _ inf_le_left : Z.gen ⊓ (P'.M.U p ⊓ P.M.U q) ≤ _) =
    resG Z.X inf_le_right (Twist.isoUnit w p q : Γ(Z.X, P'.M.U p ⊓ P.M.U q)) *
      P.eqn q (inf_le_inf_left _ inf_le_right)

def Extends (g : O) (s : P.M.Sec) : Prop :=
  ofSec s Z.gen = resG Z.X (le_top : Z.gen ≤ ⊤) (Z.const g) • P.t

variable {P P' P''} {g g' g'' : O} {s : P.M.Sec} {s' : P'.M.Sec} {s'' : P''.M.Sec}

theorem Extends.resG_f (h : P.Extends g s) (i : P.M.ι) {W : Z.X.Opens}
    (hW : W ≤ Z.gen ⊓ P.M.U i) :
    resG Z.X (hW.trans inf_le_right) (s.f i) = resG Z.X le_top (Z.const g) * P.eqn i hW := by
  have := congrArg (fun t => resG Z.X hW (coord t i)) h
  simpa only [LB.coord_ofSec, LB.coord_smul, map_mul, resG_resG, eqn] using this

theorem Extends.le_basicOpen (h : P.Extends g s) (hg : g ≠ 0) (i : P.M.ι) :
    Z.gen ⊓ P.M.U i ≤ Z.X.basicOpen (s.f i) :=
  le_basicOpen_of_isUnit inf_le_right
    (h.resG_f i le_rfl ▸ (Z.isUnit_const hg inf_le_left).mul (P.isUnit_eqn i _))

theorem Extends.isRegularSec (h : P.Extends g s) (hg : g ≠ 0) : IsRegularSec s :=
  Cartier.isRegularSec_of_ne_zero s (i := Cartier.genericChart P.isLB) fun e => by
    simpa [e] using h.le_basicOpen hg _ ⟨Z.genericPoint_mem_gen, Cartier.mem_genericChart P.isLB⟩

def Extends.eff (h : P.Extends g s) (hg : g ≠ 0) : Z.effVert :=
  effMk (.ofSec P.isLB s (h.isRegularSec hg)) (h.le_basicOpen hg)

theorem Extends.smul (h : P.Extends g s) (g' : O) : P.Extends (g' * g) (Z.const g' • s) :=
  LB.sec_ext fun i => by
    have := h.resG_f i le_rfl
    simp only [LB.coord_ofSec, LB.coord_smul, LB.smul_f, map_mul, resG_resG, this, eqn, resG_self,
      mul_assoc]

variable (P) in

theorem exists_extends {a : O} (ha : a ≠ 0) (hm : a ∈ maximalIdeal O) :
    ∃ (m : ℕ) (s : P.M.Sec), P.Extends (a ^ m) s := by
  have := LB.isQuasicoherent_toMod P.isLB
  obtain ⟨m, t, ht⟩ := Qcqs.exists_pow_smul_eq_res_of_qcqs (toMod P.M) (U := ⊤) isCompact_univ
    isQuasiSeparated_univ (Z.const a) le_top (Z.gen_eq_basicOpen ha hm) P.t
  refine ⟨m, LB.globalEquiv _ t, ?_⟩
  rw [Extends, ← LB.map_ofSec _ (le_top : Z.gen ≤ ⊤), ← LB.globalEquiv_symm_apply,
    LinearEquiv.symm_apply_apply, ← ht]
  simp only [Model.const, map_pow]

variable (P P' P'') in

def IsSum : Prop := ∀ (i : P.M.ι) (j : P'.M.ι) (k : P''.M.ι),
  ∃ u : Γ(Z.X, P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k)ˣ,
    P''.eqn k (inf_le_inf_left _ inf_le_right : Z.gen ⊓ (P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k) ≤ _) =
      resG Z.X inf_le_right u * (P.eqn i (inf_le_inf_left _ (inf_le_left.trans inf_le_left)) *
        P'.eqn j (inf_le_inf_left _ (inf_le_left.trans inf_le_right)))

theorem IsSum.ofEff_sub (H : IsSum P P' P'') (h : P.Extends g s) (h' : P'.Extends g' s')
    (h'' : P''.Extends g'' s'') (hg : g ≠ 0) (hg' : g' ≠ 0) (hg'' : g'' ≠ 0) :
    Model.ofEff (h''.eff hg'') - Z.div g'' hg'' =
      (Model.ofEff (h.eff hg) - Z.div g hg) + (Model.ofEff (h'.eff hg') - Z.div g' hg') := by
  suffices e : h''.eff hg'' * Z.effConst g hg * Z.effConst g' hg' =
      h.eff hg * h'.eff hg' * Z.effConst g'' hg'' by
    have := congrArg Model.ofEff e
    simp only [ofEff_mul] at this
    simp only [div]
    rw [sub_add_sub_comm, sub_eq_sub_iff_add_eq_add, ← add_assoc, this]
  refine Subtype.ext ?_
  simp only [Submonoid.coe_mul, Extends.eff, effConst, effMk, ← EffCartierData.idealSheaf_add]
  refine idealSheaf_eq_of_germ _ _ fun x k p hk hp => ?_
  simp only [germ_add_f]
  obtain ⟨u, hu⟩ := H p.1.1 p.1.2 k.1.1
  have e : resG Z.X (inf_le_right : P.M.U p.1.1 ⊓ P'.M.U p.1.2 ⊓ P''.M.U k.1.1 ≤ _)
      (s''.f k.1.1) * resG Z.X le_top (Z.const g) *
      resG Z.X le_top (Z.const g') = u.val * (resG Z.X (inf_le_left.trans inf_le_left) (s.f p.1.1) *
        resG Z.X (inf_le_left.trans inf_le_right) (s'.f p.1.2) * resG Z.X le_top (Z.const g'')) := by
    refine Z.resG_injective inf_le_right le_rfl ?_
    simp only [map_mul, resG_resG]
    rw [h''.resG_f _ (inf_le_inf_left _ inf_le_right), hu,
      h.resG_f _ (inf_le_inf_left _ (inf_le_left.trans inf_le_left)),
      h'.resG_f _ (inf_le_inf_left _ (inf_le_left.trans inf_le_right))]
    ring
  have e' := congrArg (Z.X.presheaf.germ _ x (show x ∈ P.M.U p.1.1 ⊓ P'.M.U p.1.2 ⊓ P''.M.U k.1.1
    from ⟨⟨hp.1.1, hp.1.2⟩, hk.1.1⟩)).hom e
  simp only [map_mul, germ_resG] at e'
  exact (Associated.of_eq e').trans (associated_unit_mul_left _ _ (u.isUnit.map _))

variable (P) in

theorem exists_extends' : ∃ q : {g : O // g ≠ 0} × P.M.Sec, P.Extends q.1 q.2 :=
  have ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have ⟨m, s, h⟩ := P.exists_extends hϖ.ne_zero hϖ.not_isUnit
  ⟨⟨⟨_, pow_ne_zero m hϖ.ne_zero⟩, s⟩, h⟩

variable (P) in

def cls : Z.VDivZ :=
  Model.ofEff (P.exists_extends'.choose_spec.eff P.exists_extends'.choose.1.2) -
    Z.div _ P.exists_extends'.choose.1.2

theorem IsSum.cls_eq (H : IsSum P P' P'') : P''.cls = P.cls + P'.cls := H.ofEff_sub _ _ _ _ _ _

theorem IsIsom.isSum (H : IsIsom P P') : IsSum P (zero Z) P' := fun i _ k => by
  obtain ⟨w, -, hw⟩ := H
  refine ⟨res (le_inf inf_le_right (inf_le_left.trans inf_le_left)) (Twist.isoUnit w k i), ?_⟩
  have := congrArg (resG Z.X (inf_le_inf_left _ (le_inf inf_le_right
    (inf_le_left.trans inf_le_left)) : Z.gen ⊓ (P.M.U i ⊓ ⊤ ⊓ P'.M.U k) ≤ _)) (hw k i)
  simp only [map_mul, resG_eqn, resG_resG] at this
  refine this.trans (congrArg₂ (· * ·) (resG_resG _ _ _).symm ?_)
  exact (mul_one _).symm.trans (congrArg _ (map_one _).symm)

variable (P) in

theorem IsIsom.refl : IsIsom P P :=
  ⟨idIso P.M, idIso_isGen P.isLB, fun p q => P.eqn_rel p q _ _ _⟩

variable (Z) in

@[simp] theorem cls_zero : (zero Z).cls = 0 := by simpa using (IsIsom.refl (zero Z)).isSum.cls_eq

theorem Extends.cls_eq (h : P.Extends g s) (hg : g ≠ 0) :
    P.cls = Model.ofEff (h.eff hg) - Z.div g hg :=
  ((IsIsom.refl P).isSum.ofEff_sub h _ _ hg _ _).trans
    ((congrArg _ (cls_zero Z)).trans (add_zero _))

theorem IsIsom.cls_eq (H : IsIsom P P') : P.cls = P'.cls := by simpa using H.isSum.cls_eq.symm

variable (P P') in

@[simp] theorem cls_add : (P.add P').cls = P.cls + P'.cls :=
  IsSum.cls_eq fun i j k => ⟨res (le_inf (inf_le_right.trans inf_le_left)
    (inf_le_left.trans inf_le_left)) (P.M.g k.1 i) * res (le_inf (inf_le_right.trans inf_le_right)
    (inf_le_left.trans inf_le_right)) (P'.M.g k.2 j), by
      refine Eq.trans ?_ (eqn_mul_rel P P' k.1 i k.2 j (inf_le_inf_left _
        (inf_le_right.trans inf_le_left)) _ (inf_le_inf_left _ (inf_le_right.trans inf_le_right))
        _ _ _ _)
      exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (resG_eqn _ _ _ _) (resG_eqn _ _ _ _))⟩

variable (P) in

@[simp] theorem cls_neg : P.neg.cls = -P.cls := by
  suffices h : IsSum P P.neg (zero Z) from
    eq_neg_of_add_eq_zero_right (h.cls_eq.symm.trans (cls_zero Z))
  refine fun i j k =>
    ⟨res (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)) (P.M.g j i), ?_⟩
  rw [val_res, resG_resG, ← mul_assoc]
  refine Eq.trans ?_ (congrArg (· * _) (P.eqn_rel j i
    (inf_le_inf_left _ (inf_le_left.trans inf_le_right)) _ _))
  change resG Z.X _ 1 = resG Z.X _ (coord P.t j) * resG Z.X _ ((P.isUnit j).unit⁻¹).val
  rw [← map_mul, IsUnit.mul_val_inv, map_one, map_one]

theorem extends_one (h : ofSec s Z.gen = P.t) : P.Extends 1 s := by
  rw [Extends, Model.const, map_one, map_one, one_smul, h]

theorem Extends.cls_eq_ofEff (h : P.Extends 1 s) : P.cls = Model.ofEff (h.eff one_ne_zero) := by
  rw [h.cls_eq one_ne_zero, Z.div_of_isUnit isUnit_one, sub_zero]

@[simp] theorem cls_ofEff (I : Z.effVert) : (ofEff I).cls = Model.ofEff I := by
  have h : (ofEff I).Extends 1 (effData I).canonical := extends_one rfl
  rw [h.cls_eq_ofEff]
  exact congrArg _ (Subtype.ext (idealSheaf_effData I))

variable (Z) in

@[simp] theorem cls_const (g : O) (hg : g ≠ 0) : (const Z g hg).cls = Z.div g hg := by
  have h : (const Z g hg).Extends 1 ⟨fun _ => Z.const g, fun _ _ => (one_mul _).symm⟩ :=
    extends_one rfl
  exact h.cls_eq_ofEff

variable (P) in

@[simp] theorem vCls_cls : Z.vCls P.cls = CechPic.cls P.M P.isLB := by
  rw [cls, map_sub, vCls_div, sub_zero, vCls_ofEff, effCls_eq rfl, cls_eq_iff]
  exact EffCartierData.lbIso_ofSec _ _ _

theorem cls_surjective : Function.Surjective (cls (Z := Z)) := fun D =>
  have ⟨I, J, e⟩ := exists_eq_ofEff_sub D
  ⟨(ofEff I).add (ofEff J).neg, by simp [e, sub_eq_add_neg]⟩

theorem cls_eq_iff : P.cls = P'.cls ↔ IsIsom P P' := by
  refine ⟨fun e => ?_, IsIsom.cls_eq⟩
  obtain ⟨⟨⟨g, hg⟩, s⟩, h⟩ := P.exists_extends'
  obtain ⟨⟨⟨g', hg'⟩, s'⟩, h'⟩ := P'.exists_extends'
  have h₁ := h.smul g'
  have h₂ := mul_comm g g' ▸ h'.smul g
  have h0 := mul_ne_zero hg' hg
  rw [h₁.cls_eq h0, h₂.cls_eq h0, sub_left_inj] at e
  have e' := congrArg Subtype.val (ofEff_injective e)
  obtain ⟨w, hw, -⟩ := Cartier.existsUnique_secMaps (b := Z.const g • s') (h₁.isRegularSec h0)
    (EffCartierData.associated_of_idealSheaf_eq _ _ e')
  refine ⟨w, hw.1, fun p q => (Z.isUnit_const h0 inf_le_left).mul_left_cancel ?_⟩
  rw [← h₂.resG_f, mul_left_comm, ← h₁.resG_f, hw.2.on p q]
  rfl

section Pull

variable {Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)

variable (P) in

def pull : VertDiv Z₁ where
  M := P.M.pull f
  isLB := Semi.LB.isLB_pull P.isLB f
  t := Twist.resM _ (preimage_gen hf).ge (LB.pullSec P.M f _ P.t)
  isUnit j := ((P.isUnit (j ⟨⟩)).map (f.appLE _ _ (LB.pull_inf_le f _ j)).hom).map _

theorem Extends.pull (h : P.Extends g s) : (P.pull hf).Extends g (Cartier.secPull s f) :=
  LB.sec_ext fun j => by
    have e : Z₁.gen ⊓ (P.M.pull f).U j ≤ f ⁻¹ᵁ (Z.gen ⊓ P.M.U (j ⟨⟩)) :=
      inf_le_inf (preimage_gen hf).ge (LB.pull_U_le f j)
    have := congrArg (f.appLE _ _ e).hom (h.resG_f (j ⟨⟩) le_rfl)
    rw [map_mul, LB.appLE_resG, LB.appLE_resG, eqn, resG_self] at this
    change resG Z₁.X _ (resG Z₁.X _ _) = resG Z₁.X _ (resG Z₁.X _ _) * resG Z₁.X _ _
    rw [resG_resG, resG_resG, ← appTop_const hf]
    exact this.trans (congrArg _ (LB.resG_appLE f (LB.pull_inf_le f _ j) _ _).symm)

variable (P) in

@[simp] theorem cls_pull : (P.pull hf).cls = vPull hf P.cls := by
  obtain ⟨⟨⟨g, hg⟩, s⟩, h⟩ := P.exists_extends'
  rw [h.cls_eq hg, (h.pull hf).cls_eq hg, map_sub, vPull_div, vPull_ofEff, sub_left_inj]
  refine congrArg _ (Subtype.ext (Eq.trans (idealSheaf_eq_of_germ _ _ fun x i j hi hj => ?_)
    (EffCartierData.idealSheaf_pull _ f (keepsRegular hf (I := h.eff hg) rfl))))
  exact (Associated.of_eq (germ_resG _ _ _ _)).trans
    ((EffCartierData.ofSec P.isLB s (h.isRegularSec hg)).associated_germ_app f (i ⟨⟩) j x _ hj)

end Pull

end VertDiv

namespace Model

variable {O} {Z : Model O}



end Model

end GlobalTheory.Vert
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)
open GlobalTheory.Cartier (IsRegularFn IsRegularSec SecMaps germ_resG ext_germK)
open GlobalTheory.VB (IsVB IsFrame IsSubbundle Chart det)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.Vert

section Dim

attribute [local instance low] specializationOrder

theorem dim_add_dim_le {S T W : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [TopologicalSpace W] [QuasiSober S] [T0Space S] [QuasiSober T] [T0Space T] [QuasiSober W]
    [T0Space W] [IrreducibleSpace T] {f : S → T} (hf : IsClosedMap f) {j : W → S}
    (hj : Continuous j) (hi : Function.Injective j) (h : ∀ w, f (j w) = genericPoint T) :
    topologicalKrullDim W + topologicalKrullDim T ≤ topologicalKrullDim S := by
  have key (a : S) : Order.height (f a) ≤ Order.height a := by
    refine Order.height_le_iff'.2 fun p hp => ?_
    induction p using RelSeries.inductionOn' generalizing a with
    | singleton x => simp
    | snoc p x hx ih =>
      simp only [RelSeries.last_snoc] at hp
      subst hp
      have hx' : p.last < f a := hx
      obtain ⟨a', ha, e⟩ := hf.specializingMap (show f a ⤳ p.last from hx'.le)
      have hlt : a' < a := lt_of_le_of_ne ha fun h => hx'.ne (by rw [← e, h])
      grw [RelSeries.snoc_length, Nat.cast_add, Nat.cast_one, ih a' e.symm]
      exact Order.height_add_one_le hlt
  have key' (p : LTSeries W) :
      p.length + Order.height (genericPoint T) ≤ Order.height (j p.last) := by
    induction p using RelSeries.inductionOn' with
    | singleton x => simpa [h] using key (j x)
    | snoc p x hx ih =>
      have hx' : p.last < x := hx
      have hlt : j p.last < j x := lt_of_le_of_ne (Specializes.map hx'.le hj) (hi.ne hx'.ne)
      rw [RelSeries.last_snoc, RelSeries.snoc_length, Nat.cast_add, Nat.cast_one, add_right_comm]
      exact (add_le_add_left ih 1).trans (Order.height_add_one_le hlt)
  have hT : topologicalKrullDim T = Order.height (genericPoint T) := by
    refine (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := T))).trans ?_
    letI : OrderTop T := { top := genericPoint T, le_top := genericPoint_specializes }
    exact Order.height_top_eq_krullDim.symm
  rw [hT, show topologicalKrullDim W = Order.krullDim W from
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := W)),
    show topologicalKrullDim S = Order.krullDim S from
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))]
  rcases isEmpty_or_nonempty W with _ | _
  · simp [Order.krullDim_eq_bot]
  rw [Order.krullDim_eq_iSup_length, ← WithBot.coe_add, ENat.iSup_add, WithBot.coe_iSup
    (OrderTop.bddAbove _)]
  exact iSup_le fun p => (WithBot.coe_le_coe.2 (key' p)).trans (Order.height_le_krullDim _)

end Dim

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

namespace Model

namespace Hom

variable {Z Z₁ : Model O} (f : Hom Z₁ Z)

instance isProper : IsProper f.f := isProper_of_comp_str f.comp_str

def relDim (_ : Hom Z₁ Z) : ℕ := Z₁.relDim - Z.relDim

abbrev fnField (_ : Hom Z₁ Z) : Type := Z.X.residueField (genericPoint Z.X)

def genFibre : Scheme.{0} := f.f.fiber (genericPoint Z.X)

def genFibreι : f.genFibre ⟶ Z₁.X := f.f.fiberι _

def genFibreStr : f.genFibre ⟶ Sp f.fnField := f.f.fiberToSpecResidueField _

instance : Algebra f.fnField Γ(f.genFibre, ⊤) := algebraΓOfHom f.genFibreStr

theorem isPullback_genFibre :
    IsPullback f.genFibreι f.genFibreStr f.f (Z.X.fromSpecResidueField (genericPoint Z.X)) :=
  .of_hasPullback _ _

instance : IsProper f.genFibreStr := MorphismProperty.of_isPullback f.isPullback_genFibre f.isProper

instance : IsAffineHom f.genFibreι :=
  have : IsAffineHom (Z.X.fromSpecResidueField (genericPoint Z.X) ≫ Z.str) := inferInstance
  have : IsAffineHom (Z.X.fromSpecResidueField (genericPoint Z.X)) := .of_comp _ Z.str
  MorphismProperty.of_isPullback f.isPullback_genFibre.flip this

theorem dim_genFibre_add_le : topologicalKrullDim f.genFibre + (Z.relDim + 1 : ℕ) ≤
    (Z₁.relDim + 1 : ℕ) := by
  rw [← Z.dim_eq, ← Z₁.dim_eq]
  exact dim_add_dim_le f.f.isClosedMap f.genFibreι.continuous (f.f.fiberι _).isEmbedding.injective
    fun w => (f.f.range_fiberι _).le ⟨w, rfl⟩

instance : Nonempty f.genFibre :=
  have ⟨x, hx⟩ := f.f.surjective (genericPoint Z.X)
  ((f.f.range_fiberι _).ge hx).elim fun w _ => ⟨w⟩

theorem exists_dim_genFibre :
    ∃ n : ℕ, topologicalKrullDim f.genFibre = n ∧ n + Z.relDim ≤ Z₁.relDim := by
  have h := f.dim_genFibre_add_le
  have h₀ : topologicalKrullDim f.genFibre ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 inferInstance)
  generalize topologicalKrullDim f.genFibre = a at *
  lift a to ℕ∞ using h₀
  have h' : a + (Z.relDim + 1 : ℕ) ≤ (Z₁.relDim + 1 : ℕ) := by exact_mod_cast h
  lift a to ℕ using by rintro rfl; simp at h'
  have h'' : a + (Z.relDim + 1) ≤ Z₁.relDim + 1 := by exact_mod_cast h'
  exact ⟨a, rfl, by omega⟩

include f in

theorem relDim_le : Z.relDim ≤ Z₁.relDim :=
  have ⟨_, _, h⟩ := f.exists_dim_genFibre
  le_of_add_le_right h

theorem relDim_add : Z.relDim + f.relDim = Z₁.relDim := Nat.add_sub_of_le f.relDim_le

theorem dim_genFibre_le : topologicalKrullDim f.genFibre ≤ f.relDim := by
  obtain ⟨n, e, h⟩ := f.exists_dim_genFibre
  rw [e]
  exact_mod_cast Nat.le_sub_of_add_le h

theorem diffVanish_genFibre :
    DiffVanish (f.relDim + 1) (chiPic f.fnField (structureModule f.genFibre)) :=
  have ⟨_, hA⟩ := Z₁.exists_isAmpleLB
  (hA.pull_of_isAffineHom f.genFibreι).diffVanish_chiPic_of_isProper (f := f.genFibreStr)
    (fun _ => rfl) _ (suppDim_structureModule.trans_le f.dim_genFibre_le)

def fibreDeg : PicSym Z₁.X →ₗ[ℚ] ℚ :=
  picForm f.diffVanish_genFibre ∘ₗ (picSymPull f.genFibreι).toLinearMap

theorem fibreDeg_prod {ι : Type} [Fintype ι] {L : ι → LB Z₁.X} (hL : ∀ i, (L i).IsLB) :
    f.fibreDeg (∏ i, c1 (L i) (hL i)) = if Fintype.card ι = f.relDim then
      (interNum f.fnField (structureModule f.genFibre) fun i => (L i).pull f.genFibreι : ℚ)
      else 0 := by
  have h := fun i => Semi.LB.isLB_pull (hL i) f.genFibreι
  rw [interNum_eq_multiDiff _ _ h, ← picForm_prod f.diffVanish_genFibre, fibreDeg,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => pullback_firstChern _ (hL i) (h i))

end Hom

variable (Z : Model O)

abbrev genRes : Z.X.Modules ⥤ Z.gen.toScheme.Modules := Scheme.Modules.pullback Z.gen.ι

abbrev GenIso (E E' : Z.X.Modules) : Type := Z.genRes.obj E ≅ Z.genRes.obj E'

variable {Z} {Z₁ : Model O} {E E' E'' : Z.X.Modules} {r : ℕ}

def genEquiv {V : Z.X.Opens} (h : V ≤ Z.gen) : Γ(Z.X, V) ≃+* Γ(Z.gen.toScheme, Z.gen.ι ⁻¹ᵁ V) :=
  haveI := Z.gen.ι.isIso_app V (h.trans Z.gen.opensRange_ι.ge)
  (asIso (Z.gen.ι.app V)).commRingCatIsoToRingEquiv

theorem genEquiv_apply {V : Z.X.Opens} (h : V ≤ Z.gen) (a : Γ(Z.X, V)) :
    genEquiv h a = (Z.gen.ι.app V).hom a := rfl

theorem genEquiv_resG {U V : Z.X.Opens} (h : V ≤ Z.gen) (h' : V ≤ U) (a : Γ(Z.X, U)) :
    genEquiv h (resG Z.X h' a) = (Z.gen.ι.appLE U _ (Z.gen.ι.preimage_mono h')).hom a :=
  Cartier.app_resG Z.gen.ι h' a

theorem isIso_genRes_map_smulHom (E : Z.X.Modules) {g : O} (hg : g ≠ 0) :
    IsIso (Z.genRes.map (smulHom E (Z.const g))) := by
  rw [VB.pullback_map_smulHom]
  have h : IsUnit (Z.gen.ι.appTop (Z.const g)) :=
    RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x _ => (Scheme.mem_basicOpen_top _ _ x).1
      ((Scheme.preimage_basicOpen_top Z.gen.ι _).le (Z.gen_le_basicOpen hg x.2))
  exact (isUnit_iff_isIso _).1 (h.map (smulEnd _))

namespace GenIso

def ofHom (ψ : E' ⟶ E) [IsIso (Z.genRes.map ψ)] : Z.GenIso E E' := (asIso (Z.genRes.map ψ)).symm

variable (E) in

def smul (g : O) (hg : g ≠ 0) : Z.GenIso E E :=
  haveI := isIso_genRes_map_smulHom E hg
  ofHom (smulHom E (Z.const g))

theorem smul_inv (g : O) (hg : g ≠ 0) :
    (smul E g hg).inv = Z.genRes.map (smulHom E (Z.const g)) := rfl

section Pull

variable {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)

def genMap : Z₁.gen.toScheme ⟶ Z.gen.toScheme := f.resLE _ _ (preimage_gen hf).ge

def genPullIso : Scheme.Modules.pullback f ⋙ Z₁.genRes ≅
    Z.genRes ⋙ Scheme.Modules.pullback (genMap hf) :=
  Scheme.Modules.pullbackComp _ f ≪≫
    Scheme.Modules.pullbackCongr (f.resLE_comp_ι (preimage_gen hf).ge).symm ≪≫
      (Scheme.Modules.pullbackComp _ _).symm

def pull (φ : Z.GenIso E E') :
    Z₁.GenIso ((Scheme.Modules.pullback f).obj E) ((Scheme.Modules.pullback f).obj E') :=
  (genPullIso hf).app E ≪≫ (Scheme.Modules.pullback (genMap hf)).mapIso φ ≪≫
    ((genPullIso hf).app E').symm

theorem pull_inv {φ : Z.GenIso E E'} {ψ : E' ⟶ E} (h : φ.inv = Z.genRes.map ψ) :
    (φ.pull hf).inv = Z₁.genRes.map ((Scheme.Modules.pullback f).map ψ) := by
  simp only [pull, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, h,
    Category.assoc]
  exact NatIso.naturality_2 (genPullIso hf) ψ

theorem pull_smul (g : O) (hg : g ≠ 0) : (smul E g hg).pull hf = smul _ g hg :=
  Iso.ext (Iso.inv_eq_inv _ _ |>.1 (by
    rw [pull_inv hf (smul_inv g hg), VB.pullback_map_smulHom f, appTop_const hf, smul_inv]))

end Pull

variable (φ : Z.GenIso E E')

def detUnit (c : Chart E r) (c' : Chart E' r) [E.IsQuasicoherent] [E'.IsQuasicoherent]
    {T : Z.gen.toScheme.Opens} (h : T ≤ Z.gen.ι ⁻¹ᵁ (c.U ⊓ c'.U)) : Γ(Z.gen.toScheme, T)ˣ :=
  (c.isFrame.pullback Z.gen.ι).detUnit ((c'.isFrame.pullback Z.gen.ι).map_iso φ.inv)
    (h.trans (Z.gen.ι.preimage_mono inf_le_left)) (h.trans (Z.gen.ι.preimage_mono inf_le_right))

theorem detUnit_rel (c d : Chart E r) (c' d' : Chart E' r) [E.IsQuasicoherent]
    [E'.IsQuasicoherent] {V : Z.X.Opens} (hc : V ≤ c.U ⊓ c'.U) (hd : V ≤ d.U ⊓ d'.U)
    {T : Z.gen.toScheme.Opens} (h : T ≤ Z.gen.ι ⁻¹ᵁ V) :
    φ.detUnit c c' (h.trans (Z.gen.ι.preimage_mono hc)) =
      Units.map (Z.gen.ι.appLE V T h).hom.toMonoidHom
        (c.isFrame.detUnit d.isFrame (hc.trans inf_le_left) (hd.trans inf_le_left) *
          (c'.isFrame.detUnit d'.isFrame (hc.trans inf_le_right) (hd.trans inf_le_right))⁻¹) *
        φ.detUnit d d' (h.trans (Z.gen.ι.preimage_mono hd)) := by
  have e := c.isFrame.val_detUnit_pullback d.isFrame Z.gen.ι (hc.trans inf_le_left)
    (hd.trans inf_le_left) h
  have e' := c'.isFrame.val_detUnit_pullback d'.isFrame Z.gen.ι (hc.trans inf_le_right)
    (hd.trans inf_le_right) h
  rw [← (c'.isFrame.pullback Z.gen.ι).detUnit_map_iso _ φ.inv] at e'
  rw [map_mul, map_inv, ← Units.ext (v := Units.map _ _) e, ← Units.ext (v := Units.map _ _) e',
    mul_right_comm, detUnit, detUnit, IsFrame.detUnit_mul, eq_mul_inv_iff_mul_eq,
    IsFrame.detUnit_mul]

def div (hE : IsVB E r) (hE' : IsVB E' r) : VertDiv Z :=
  haveI := hE.isQuasicoherent
  haveI := hE'.isQuasicoherent
  .ofUnits (LB.div (det E r) (det E' r)) (Semi.LB.isLB_div hE.isLB_det hE'.isLB_det)
    (fun p => (genEquiv inf_le_left).symm
      (φ.detUnit p.1 p.2 (Z.gen.ι.preimage_mono inf_le_right)).val)
    (fun _ => (Units.isUnit _).map _) fun p q => by
      have hV := (inf_le_left.trans inf_le_left : Z.gen ⊓ (LB.div (det E r) (det E' r)).U p ⊓
        (LB.div (det E r) (det E' r)).U q ≤ Z.gen)
      have H (p : (LB.div (det E r) (det E' r)).ι) (h) : genEquiv hV (resG Z.X h
          ((genEquiv inf_le_left).symm
            (φ.detUnit p.1 p.2 (Z.gen.ι.preimage_mono inf_le_right)).val)) =
          (φ.detUnit p.1 p.2 (Z.gen.ι.preimage_mono (h.trans inf_le_right))).val := by
        rw [genEquiv_apply, Cartier.app_resG, ← genEquiv_apply inf_le_left,
          RingEquiv.apply_symm_apply]
        exact congrArg Units.val (IsFrame.res_detUnit _ _ _ _ _)
      refine (genEquiv hV).injective ?_
      refine (H p _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg _ (H q _))).symm)
      rw [φ.detUnit_rel p.1 q.1 p.2 q.2 (inf_le_left.trans inf_le_right)
        inf_le_right le_rfl, Units.val_mul]
      refine congrArg (· * _) ?_
      rw [genEquiv_apply, Scheme.Hom.app_eq_appLE, ← val_res]
      refine congrArg (fun u => (Z.gen.ι.appLE _ _ le_rfl).hom (Units.val u)) ?_
      change _ = res _ (res _ (IsFrame.detUnit _ _ _ _) * (res _ (IsFrame.detUnit _ _ _ _))⁻¹)
      simp only [map_mul, map_inv, IsFrame.res_detUnit]

variable (hE : IsVB E r) (hE' : IsVB E' r) (hE'' : IsVB E'' r)

theorem genEquiv_eqn_div (c : Chart E r) (c' : Chart E' r) {W : Z.X.Opens}
    (h : W ≤ Z.gen ⊓ (c.U ⊓ c'.U)) :
    haveI := hE.isQuasicoherent
    haveI := hE'.isQuasicoherent
    genEquiv (h.trans inf_le_left) ((φ.div hE hE').eqn (c, c') h) =
      (φ.detUnit c c' (Z.gen.ι.preimage_mono (h.trans inf_le_right))).val := by
  change genEquiv _ (resG Z.X h ((genEquiv inf_le_left).symm _)) = _
  rw [genEquiv_apply, Cartier.app_resG, ← genEquiv_apply inf_le_left, RingEquiv.apply_symm_apply]
  exact congrArg Units.val (IsFrame.res_detUnit _ _ _ _ _)

theorem vCls_div : Z.vCls (φ.div hE hE').cls = cls _ hE.isLB_det - cls _ hE'.isLB_det :=
  (VertDiv.vCls_cls _).trans (cls_div _ _ _)

theorem cls_div_trans (φ' : Z.GenIso E' E'') :
    (div (φ ≪≫ φ') hE hE'').cls = (φ.div hE hE').cls + (φ'.div hE' hE'').cls := by
  have := hE.isQuasicoherent
  have := hE'.isQuasicoherent
  have := hE''.isQuasicoherent
  refine VertDiv.IsSum.cls_eq fun i j k => ?_
  obtain ⟨c, c'⟩ := i
  obtain ⟨d', d''⟩ := j
  obtain ⟨e, e''⟩ := k
  have h₁ : c.U ⊓ c'.U ⊓ (d'.U ⊓ d''.U) ⊓ (e.U ⊓ e''.U) ≤ c.U ⊓ c'.U := inf_le_left.trans inf_le_left
  have h₂ : c.U ⊓ c'.U ⊓ (d'.U ⊓ d''.U) ⊓ (e.U ⊓ e''.U) ≤ d'.U ⊓ d''.U :=
    inf_le_left.trans inf_le_right
  have h₃ : c.U ⊓ c'.U ⊓ (d'.U ⊓ d''.U) ⊓ (e.U ⊓ e''.U) ≤ e.U ⊓ e''.U := inf_le_right
  refine ⟨e.isFrame.detUnit c.isFrame (h₃.trans inf_le_left) (h₁.trans inf_le_left) *
    c'.isFrame.detUnit d'.isFrame (h₁.trans inf_le_right) (h₂.trans inf_le_left) *
    d''.isFrame.detUnit e''.isFrame (h₂.trans inf_le_right) (h₃.trans inf_le_right),
    (genEquiv inf_le_left).injective ?_⟩
  rw [map_mul, map_mul, genEquiv_eqn_div, genEquiv_eqn_div, genEquiv_eqn_div, genEquiv_resG]
  simp only [Units.val_mul, map_mul, ← IsFrame.val_detUnit_pullback]
  simp only [← Units.val_mul]
  refine congrArg Units.val ?_
  rw [← (c'.isFrame.pullback Z.gen.ι).detUnit_map_iso _ φ.inv,
    ← (d''.isFrame.pullback Z.gen.ι).detUnit_map_iso _ (φ ≪≫ φ').inv, detUnit, detUnit, detUnit,
    ← (d'.isFrame.pullback Z.gen.ι).detUnit_map_iso _ φ.inv,
    show ∀ a b c d e : Γ(Z.gen.toScheme, _)ˣ, a * b * c * (d * e) = a * d * b * e * c from
      fun a b c d e => by ac_rfl, IsFrame.detUnit_mul, IsFrame.detUnit_mul, IsFrame.detUnit_mul]
  exact (IsFrame.detUnit_mul _ _ _ _ _ _).symm

variable {φ} {ψ : E' ⟶ E}

theorem eqn_div_of_hom (hψ : φ.inv = Z.genRes.map ψ) (c : Chart E r) (c' : Chart E' r)
    {W V : Z.X.Opens} (h : W ≤ Z.gen ⊓ V) (hV : V ≤ c.U ⊓ c'.U) :
    (φ.div hE hE').eqn (c, c') (h.trans (inf_le_inf_left _ hV)) =
      resG Z.X (h.trans inf_le_right) ((c.isFrame.basis (hV.trans inf_le_left)).det
        fun i => ψ.app V (resM E' (hV.trans inf_le_right) (c'.e i))) := by
  have := hE.isQuasicoherent
  have := hE'.isQuasicoherent
  refine (genEquiv (h.trans inf_le_left)).injective ?_
  rw [genEquiv_eqn_div, genEquiv_resG, detUnit, IsFrame.val_detUnit, Module.Basis.det_apply,
    Module.Basis.det_apply, RingHom.map_det]
  refine congrArg _ (Matrix.ext fun i j => ?_)
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
    Module.Basis.toMatrix_apply, ← c.isFrame.pullback_basis_repr, hψ,
    pullback_map_app_pullbackSections, app_resM]
  congr 2
  exact (res_pullbackSections _ _ _ _ _).trans (pullbackSections_res _ _ _ _ _).symm


theorem cls_div_of_smul {φ : Z.GenIso E E} {g : O} (hg : g ≠ 0)
    (hφ : φ.inv = Z.genRes.map (smulHom E (Z.const g))) :
    (φ.div hE hE).cls = r • Z.div g hg := by
  rw [← Z.div_pow hg r (pow_ne_zero r hg), ← VertDiv.cls_const, ← add_zero (VertDiv.const Z _ _).cls,
    ← VertDiv.cls_zero Z]
  refine VertDiv.IsSum.cls_eq fun i j k => ?_
  obtain ⟨c, c'⟩ := k
  refine ⟨c.isFrame.detUnit c'.isFrame (inf_le_right.trans inf_le_left)
    (inf_le_right.trans inf_le_right), (eqn_div_of_hom hE hE hφ c c' le_rfl inf_le_right).trans ?_⟩
  change _ = _ * (resG _ _ (resG _ _ _) * resG _ _ 1)
  simp only [smulHom_app_apply, IsFrame.val_detUnit]
  rw [AlternatingMap.map_smul_univ, map_one, mul_one, smul_eq_mul, map_mul, mul_comm, resG_resG]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Model.const, map_pow]
  exact congrArg (_ * · ^ r) (resG_resG _ _ _)

end GenIso

end Model

structure Flag {X : Scheme.{0}} (E : X.Modules) (N : ℕ) where

  F : Fin (N + 1) → X.Modules

  ι : ∀ i, F i ⟶ E

  isSubbundle : ∀ i, IsSubbundle (ι i)

  isVB : ∀ i, IsVB (F i) i

  step : ∀ i : Fin N, F i.castSucc ⟶ F i.succ

  step_ι : ∀ i, step i ≫ ι i.succ = ι i.castSucc

  isIso_last : IsIso (ι (Fin.last N))

namespace Flag

variable {X : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E N)

attribute [instance] isIso_last

attribute [reassoc (attr := simp)] step_ι

instance mono_ι (i : Fin (N + 1)) : Mono (fl.ι i) := (fl.isSubbundle i).mono

instance mono_step (i : Fin N) : Mono (fl.step i) := mono_of_mono_fac (fl.step_ι i)

include fl in

theorem isVB_self : IsVB E N := (fl.isVB (Fin.last N)).of_iso (asIso (fl.ι _))

def gr (i : Fin N) : X.Modules := cokernel (fl.step i)

def π (i : Fin N) : fl.F i.succ ⟶ fl.gr i := cokernel.π _

instance epi_π (i : Fin N) : Epi (fl.π i) := inferInstanceAs (Epi (cokernel.π _))

theorem isVB_cokernel (i : Fin (N + 1)) : IsVB (cokernel (fl.ι i)) (N - i) := fun x => by
  have : Nonempty X := ⟨x⟩
  obtain ⟨s, hs⟩ := (fl.isSubbundle i).isVB_cokernel
  obtain ⟨h, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X (.mk (fl.ι i) (cokernel.π _)
    (cokernel.condition _)) i s { exact := ShortComplex.exact_cokernel _ } (fl.isVB i) hs
  obtain rfl : s = N - i := by have := h.rank_unique fl.isVB_self; omega
  exact hs x

theorem isVB_gr (i : Fin N) : IsVB (fl.gr i) 1 := by
  refine VB.isVB_X₁_of_shortExact X _ 1 _ (shortExact_cokernel_comp (fl.step i) (fl.ι i.succ)) ?_
    (fl.isVB_cokernel i.succ)
  have h := (fl.isVB_cokernel i.castSucc).of_iso (cokernelIsoOfEq (fl.step_ι i).symm)
  rwa [show N - (i.castSucc : ℕ) = 1 + (N - (i.succ : ℕ)) by simp; omega] at h

def root (i : Fin N) : LB X := det (fl.gr i) 1

theorem isLB_root (i : Fin N) : (fl.root i).IsLB := (fl.isVB_gr i).isLB_det

theorem cls_det : cls _ fl.isVB_self.isLB_det = ∑ i, cls _ (fl.isLB_root i) := by
  have key (i : Fin (N + 1)) : cls _ (fl.isVB i).isLB_det =
      ∑ j : Fin N, if (j : ℕ) < i then cls _ (fl.isLB_root j) else 0 := by
    induction i using Fin.induction with
    | zero =>
      have := VB.isVB_zero_iff.1 (fl.isVB 0)
      exact (((VB.isFrame_freeFrame X (Fin 0)).map_iso ((VB.isVB_zero_iff.1
        (VB.isVB_freeModule_fin X 0)).iso this).hom).cls_det_eq_zero _).trans (by simp)
    | succ i ih =>
      obtain ⟨h, e⟩ := VBExt.isVB_and_cls_det_of_shortExact X (.mk (fl.step i) (cokernel.π _)
        (cokernel.condition _)) _ _ { exact := ShortComplex.exact_cokernel _ } (fl.isVB _)
        (fl.isVB_gr i)
      refine e.trans ((congrArg (· + _) ih).trans ?_)
      refine (congrArg _ (Finset.sum_ite_eq_of_mem' Finset.univ i
        (fun j => cls _ (fl.isLB_root j)) (Finset.mem_univ i)).symm).trans ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
      split_ifs <;> first | omega | simp
  exact ((cls_eq_iff (fl.isVB (Fin.last N)).isLB_det _).2
    ((fl.isVB _).lbIso_det_of_iso (asIso (fl.ι _)))).symm.trans ((key _).trans (by simp))

def ofIso {E' : X.Modules} (e : E ≅ E') : Flag E' N where
  F := fl.F
  ι i := fl.ι i ≫ e.hom
  isSubbundle i := ⟨inferInstance, _, (fl.isVB_cokernel i).of_iso (cokernelCompIsIso _ _).symm⟩
  isVB := fl.isVB
  step := fl.step
  step_ι i := fl.step_ι_assoc i _
  isIso_last := inferInstance

open ZeroObject in

def ofRankOne {L : X.Modules} (h : IsVB L 1) : Flag L 1 where
  F := ![0, L]
  ι := Fin.cons 0 (Fin.cons (𝟙 L) finZeroElim)
  isSubbundle := Fin.cons ⟨(isZero_zero _).mono _, 1, h.of_iso cokernelZeroIsoTarget.symm⟩
    (Fin.cons (VB.isSubbundle_of_isIso (𝟙 L)) finZeroElim)
  isVB := Fin.cons (VB.isVB_zero_iff.2 (isZero_zero _)) (Fin.cons h finZeroElim)
  step := Fin.cons 0 finZeroElim
  step_ι := Fin.cons zero_comp finZeroElim
  isIso_last := IsIso.id L

def grOfRankOne {L : X.Modules} (h : IsVB L 1) : (ofRankOne h).gr 0 ≅ L := cokernelZeroIsoTarget

open ZeroObject in

def ofBiprod {L M : X.Modules} (hL : IsVB L 1) (hM : IsVB M 1) : Flag (L ⊞ M) 2 where
  F := ![0, L, L ⊞ M]
  ι := Fin.cons 0 (Fin.cons biprod.inl (Fin.cons (𝟙 _) finZeroElim))
  isSubbundle := Fin.cons
    ⟨(isZero_zero _).mono _, 2, (hL.biprod hM).of_iso cokernelZeroIsoTarget.symm⟩
    (Fin.cons (VB.isSubbundle_inl hM) (Fin.cons (VB.isSubbundle_of_isIso (𝟙 _)) finZeroElim))
  isVB := Fin.cons (VB.isVB_zero_iff.2 (isZero_zero _))
    (Fin.cons hL (Fin.cons (hL.biprod hM) finZeroElim))
  step := Fin.cons 0 (Fin.cons biprod.inl finZeroElim)
  step_ι := Fin.cons zero_comp (Fin.cons (Category.comp_id _) finZeroElim)
  isIso_last := IsIso.id _

theorem nonempty_gr_ofBiprod {L M : X.Modules} (hL : IsVB L 1) (hM : IsVB M 1) :
    Nonempty ((ofBiprod hL hM).gr 0 ≅ L) ∧ Nonempty ((ofBiprod hL hM).gr 1 ≅ M) :=
  ⟨⟨cokernelZeroIsoTarget⟩, ⟨cokernelBiprodInlIso⟩⟩

end Flag

namespace Model

variable {Z : Model O} {E E' : Z.X.Modules} {N : ℕ}

structure FlagPair (φ : Z.GenIso E E') (N : ℕ) where

  fl : Flag E N

  fl' : Flag E' N

  gen : ∀ i, Z.GenIso (fl.F i) (fl'.F i)

  gen_ι : ∀ i, (gen i).hom ≫ Z.genRes.map (fl'.ι i) = Z.genRes.map (fl.ι i) ≫ φ.hom

instance mono_genRes_map_ι (fl : Flag E N) (i : Fin (N + 1)) : Mono (Z.genRes.map (fl.ι i)) :=
  have := (fl.isVB i).isQuasicoherent
  have := fl.isVB_self.isQuasicoherent
  mono_pullback_map _ _

namespace FlagPair

variable {φ : Z.GenIso E E'} (P : FlagPair φ N)

theorem gen_unique (i : Fin (N + 1)) (ψ : Z.GenIso (P.fl.F i) (P.fl'.F i))
    (h : ψ.hom ≫ Z.genRes.map (P.fl'.ι i) = Z.genRes.map (P.fl.ι i) ≫ φ.hom) : ψ = P.gen i :=
  Iso.ext ((cancel_mono _).1 (h.trans (P.gen_ι i).symm))

theorem gen_step (i : Fin N) : Z.genRes.map (P.fl.step i) ≫ (P.gen i.succ).hom =
    (P.gen i.castSucc).hom ≫ Z.genRes.map (P.fl'.step i) := by
  rw [← cancel_mono (Z.genRes.map (P.fl'.ι i.succ)), Category.assoc, Category.assoc, gen_ι,
    ← Functor.map_comp, ← Functor.map_comp_assoc, Flag.step_ι, Flag.step_ι, gen_ι]

def grIso (i : Fin N) : Z.GenIso (P.fl.gr i) (P.fl'.gr i) :=
  PreservesCokernel.iso Z.genRes (P.fl.step i) ≪≫
    cokernel.mapIso _ _ (P.gen i.castSucc) (P.gen i.succ) (P.gen_step i) ≪≫
      (PreservesCokernel.iso Z.genRes (P.fl'.step i)).symm

theorem π_grIso_hom (i : Fin N) : Z.genRes.map (P.fl.π i) ≫ (P.grIso i).hom =
    (P.gen i.succ).hom ≫ Z.genRes.map (P.fl'.π i) := by
  simp [grIso, Flag.π, Flag.gr]

def div (i : Fin N) : VertDiv Z := (P.grIso i).div (P.fl.isVB_gr i) (P.fl'.isVB_gr i)

theorem cls_root' (i : Fin N) :
    cls _ (P.fl'.isLB_root i) = cls _ (P.fl.isLB_root i) - Z.vCls (P.div i).cls := by
  rw [div, GenIso.vCls_div]
  exact (sub_sub_cancel _ _).symm

def ofRankOne (φ : Z.GenIso E E') (h : IsVB E 1) (h' : IsVB E' 1) : FlagPair φ 1 where
  fl := .ofRankOne h
  fl' := .ofRankOne h'
  gen := Fin.cons (Iso.refl _) (Fin.cons φ finZeroElim)
  gen_ι := Fin.cons ((Z.genRes.map_isZero (isZero_zero _)).eq_of_src _ _)
    (Fin.cons (by
      change φ.hom ≫ Z.genRes.map (𝟙 _) = Z.genRes.map (𝟙 _) ≫ φ.hom
      simp) finZeroElim)

def ofSMul (fl : Flag E N) (g : O) (hg : g ≠ 0) : FlagPair (GenIso.smul E g hg) N where
  fl := fl
  fl' := fl
  gen i := GenIso.smul _ g hg
  gen_ι i := by
    rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq, GenIso.smul_inv, GenIso.smul_inv,
      ← Functor.map_comp, ← Functor.map_comp, smulHom_comp]

theorem cls_div_ofSMul (fl : Flag E N) (g : O) (hg : g ≠ 0) (i : Fin N) :
    ((ofSMul fl g hg).div i).cls = Z.div g hg := by
  refine (GenIso.cls_div_of_smul (fl.isVB_gr i) hg ?_).trans (one_nsmul _)
  have h := (ofSMul fl g hg).π_grIso_hom i
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv] at h
  rw [← cancel_epi (Z.genRes.map (fl.π i)), ← Functor.map_comp, ← smulHom_comp, Functor.map_comp]
  exact h.symm

end FlagPair

structure FlagModel (φ : Z.GenIso E E') (N : ℕ) where

  B : Model O

  π : Hom B Z

  pair : FlagPair (φ.pull π.comp_str) N

def FlagModel.relDim {φ : Z.GenIso E E'} (M : FlagModel φ N) : ℕ := M.π.relDim

def FlagModel.ofRankOne (φ : Z.GenIso E E') (h : IsVB E 1) (h' : IsVB E' 1) {B : Model O}
    (π : Hom B Z) : FlagModel φ 1 :=
  ⟨B, π, .ofRankOne _ (h.pullback _) (h'.pullback _)⟩

def FlagModel.ofSMul {B : Model O} (π : Hom B Z)
    (fl : Flag ((Scheme.Modules.pullback π.f).obj E) N) (g : O) (hg : g ≠ 0) :
    FlagModel (GenIso.smul E g hg) N :=
  ⟨B, π, fl, fl, (FlagPair.ofSMul fl g hg).gen, fun i => by
    rw [GenIso.pull_smul]; exact (FlagPair.ofSMul fl g hg).gen_ι i⟩

def FlagModel.ofBiprod {L M : Z.X.Modules} (hL : IsVB L 1) (hM : IsVB M 1) {B : Model O}
    (π : Hom B Z) (g : O) (hg : g ≠ 0) : FlagModel (GenIso.smul (L ⊞ M) g hg) 2 :=
  haveI := preservesBinaryBiproduct_of_preservesBinaryCoproduct (Scheme.Modules.pullback π.f)
    (X := L) (Y := M)
  .ofSMul π ((Flag.ofBiprod (hL.pullback π.f) (hM.pullback π.f)).ofIso
    ((Scheme.Modules.pullback π.f).mapBiprod L M).symm) g hg

end Model

end GlobalTheory.Vert
end
end
