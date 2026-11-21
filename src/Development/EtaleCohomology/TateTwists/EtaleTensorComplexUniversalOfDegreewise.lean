import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensUnivPf

theorem sec_eq_zero_of_isZero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h1 : (𝟙 F : F ⟶ F) = 0 := hF.eq_of_src _ _
  have := congrArg (fun φ : F ⟶ F => (φ.hom.app (op U)).hom x) h1
  simpa using this

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

def postPair {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    rw [← μ.nat g s t w h a b]
    exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) (μ.mul _ s t w h a b)) ((u.f w).hom.naturality g.op)).symm
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    have hc : Sec.map (K'.d w (w+1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = Sec.map (u.f (w+1)) (Sec.map (K.d w (w+1)) (μ.mul U s t w h a b)) := by
      rw [← secMap_comp, ← secMap_comp, u.comm]
    change Sec.map (K'.d w (w+1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = _
    rw [hc, μ.leibniz]
    simp [map_add]

theorem part3 {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) {K' : Cx R} (u : K ⟶ K') :
    ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u :=
  ⟨postPair τ u, fun U s t w h a b => rfl⟩

theorem sep {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (y z : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g y = Sec.res g z) : y = z := by
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem sep_loc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hh⟩ := h
  exact sep S hS y z hh

theorem isZero_of_sec {R : Type} [CommRing R] {F : Shv R} (h : ∀ (U : Scheme.{0}) (x : Sec F U), x = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact (h _ _).trans (h _ _).symm

theorem lift_ind {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (V : Scheme.{0}) (w : ℤ)
    (P : Sec (K.X w) V → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hm : ∀ (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) V) (b : Sec (J.X t) V), P (μ.mul V s t w h a b))
    (x : Tens I J V w) : P (μ.lift V w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simpa using h0
  | of p t =>
    simp only [Pair.lift]
    rw [← DirectSum.lof_eq_of (ULift.{1} R), DirectSum.toModule_lof]
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => simpa using hm p.1.1 p.1.2 p.2 a b
    | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

theorem part2 {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) :
    I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0 := by
  intro hI hJ
  rw [CochainComplex.isStrictlyGE_iff]
  intro w hw
  apply isZero_of_sec
  intro U y
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hh V g hg
  rw [← hx]
  simp only [map_zero]
  refine lift_ind τ V w (fun z => z = 0) rfl (fun a b ha hb => by rw [ha, hb]; simp) ?_ x
  intro s t h a b
  rcases (show s < 0 ∨ t < 0 by omega) with hs | ht
  · rw [sec_eq_zero_of_isZero (I.isZero_of_isStrictlyGE 0 s hs) a]; simp
  · rw [sec_eq_zero_of_isZero (J.isZero_of_isStrictlyGE 0 t ht) b]; simp

theorem uniq {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor)
    {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u v : K ⟶ K')
    (hu : τ.Compat ν f g u) (hv : τ.Compat ν f g v) : u = v := by
  ext w U y
  obtain ⟨U⟩ := U
  change Sec.map (u.f w) y = Sec.map (v.f w) y
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V e he => ?_⟩
  obtain ⟨x, hx⟩ := hh V e he
  have nu : ∀ (φ : K ⟶ K') (z : Sec (K.X w) U), Sec.res e (Sec.map (φ.f w) z) = Sec.map (φ.f w) (Sec.res e z) :=
    fun φ z => (congrArg (fun ψ => (ModuleCat.Hom.hom ψ) z) ((φ.f w).hom.naturality e.op)).symm
  rw [nu, nu, ← hx]
  refine lift_ind τ V w (fun z => Sec.map (u.f w) z = Sec.map (v.f w) z) (by simp) ?_ ?_ x
  · intro a b ha hb
    simp only [Sec.map, map_add] at ha hb ⊢
    rw [ha, hb]
  · intro s t h a b
    rw [hu, hv]

theorem nat_sec {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (e : V ⟶ U) (z : Sec F U) :
    Sec.res e (Sec.map φ z) = Sec.map φ (Sec.res e z) :=
  (congrArg (fun ψ => (ModuleCat.Hom.hom ψ) z) (φ.hom.naturality e.op)).symm

theorem secMap_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ a b

theorem secMap_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℤˣ) (a : Sec F U) :
    Sec.map φ (n • a) = n • Sec.map φ a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ a

theorem exists_of_degreewise {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor)
    {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (m : ∀ w, K.X w ⟶ K'.X w)
    (hm : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (m w) (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)) :
    ∃ u : K ⟶ K', τ.Compat ν f g u := by
  refine ⟨{ f := m, comm' := ?_ }, fun U s t w h a b => hm U s t w h a b⟩
  rintro w _ rfl
  ext U y
  obtain ⟨U⟩ := U
  change Sec.map (K'.d w (w+1)) (Sec.map (m w) y) = Sec.map (m (w+1)) (Sec.map (K.d w (w+1)) y)
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V e he => ?_⟩
  obtain ⟨x, hx⟩ := hh V e he
  rw [nat_sec, nat_sec, nat_sec, nat_sec, ← hx]
  refine lift_ind τ V w (fun z => Sec.map (K'.d w (w+1)) (Sec.map (m w) z) = Sec.map (m (w+1)) (Sec.map (K.d w (w+1)) z))
    (by simp [Sec.map]) ?_ ?_ x
  · intro a b ha hb
    simp only [secMap_add] at ha hb ⊢
    rw [ha, hb]
  · intro s t h a b
    have cf : Sec.map (f.f (s+1)) (Sec.map (I.d s (s+1)) a) = Sec.map (I'.d s (s+1)) (Sec.map (f.f s) a) := by
      rw [← secMap_comp, ← secMap_comp, f.comm]
    have cg : Sec.map (g.f (t+1)) (Sec.map (J.d t (t+1)) b) = Sec.map (J'.d t (t+1)) (Sec.map (g.f t) b) := by
      rw [← secMap_comp, ← secMap_comp, g.comm]
    rw [hm, τ.leibniz, secMap_add, secMap_zsmul, hm, hm, ν.leibniz, cf, cg]

end LateralTheory.EtaleFoundations.TensUnivPf

def LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ),
      ∃ m : K.X w ⟶ K'.X w, ∀ (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
        Sec.map m (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

theorem LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise (hdeg : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists) :
    LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  intro R _ I J K τ hτ
  refine ⟨fun {I' J' K'} ν f g => ?_, LateralTheory.EtaleFoundations.TensUnivPf.part2 τ hτ,
    fun u => LateralTheory.EtaleFoundations.TensUnivPf.part3 τ u⟩
  obtain ⟨u, hu⟩ := LateralTheory.EtaleFoundations.TensUnivPf.exists_of_degreewise τ hτ ν f g
    (fun w => (hdeg R τ hτ ν f g w).choose) (fun U s t w h a b => (hdeg R τ hτ ν f g w).choose_spec U s t h a b)
  exact ⟨u, hu, fun v hv => LateralTheory.EtaleFoundations.TensUnivPf.uniq τ hτ ν f g v u hv hu⟩
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensUnivDeg

variable {R : Type} [CommRing R]

theorem tens_ind {I J : Cx R} (V : Scheme.{0}) (w : ℤ) (P : Tens I J V w → Prop) (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hm : ∀ (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) V) (b : Sec (J.X p.1.2) V),
      P (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V)) p (a ⊗ₜ b)))
    (x : Tens I J V w) : P x := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | of p t =>
    rw [← DirectSum.lof_eq_of (ULift.{1} R)]
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => exact hm p a b
    | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb
  | add a b ha hb => exact hadd _ _ ha hb

theorem res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V)) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  classical
  simp [Tens.res, Sec.res]

theorem lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  classical
  simp [Pair.lift]

def Tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Tens I' J' U w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op U)).hom ((g.f p.1.2).hom.app (op U)).hom

theorem tmap_lof {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tmap f g U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I'.X p.1.1) U ⊗[ULift.{1} R] Sec (J'.X p.1.2) U)) p (Sec.map (f.f p.1.1) a ⊗ₜ Sec.map (g.f p.1.2) b) := by
  classical
  simp [Tmap, Sec.map]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => Tens.res (𝟙 U.unop) w x = x) (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · rw [map_add, ha, hb]
    · rw [res_lof]; simp [Sec.res]
  map_comp g h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind _ w (fun x => Tens.res (g ≫ h).unop w x = Tens.res h.unop w (Tens.res g.unop w x))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · rw [map_add, ha, hb, map_add, map_add]
    · rw [res_lof, res_lof, res_lof]; simp [Sec.res]

def alpha {I J K : Cx R} (τ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (τ.lift U.unop w)
  naturality U V g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => τ.lift V.unop w (Tens.res g.unop w x) = Sec.res g.unop (τ.lift U.unop w x))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · simp only [map_add, ha, hb]
    · rw [res_lof, lift_lof, lift_lof, τ.nat]

def beta {I J I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) : TP I J w ⟶ (K'.X w).obj where
  app U := ModuleCat.ofHom (ν.lift U.unop w ∘ₗ Tmap f g U.unop w)
  naturality U V e := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => ν.lift V.unop w (Tmap f g V.unop w (Tens.res e.unop w x)) =
        Sec.res e.unop (ν.lift U.unop w (Tmap f g U.unop w x)))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · simp only [map_add, ha, hb]
    · rw [res_lof, tmap_lof, tmap_lof, lift_lof, lift_lof, ν.nat, TensUnivPf.nat_sec, TensUnivPf.nat_sec]

theorem alpha_locSurj {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology (alpha τ w) where
  imageSieve_mem {U} y := by
    obtain ⟨S, hS, hh⟩ := hτ.1 U w y
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    obtain ⟨x, hx⟩ := hh V g hg
    exact ⟨x, hx⟩

theorem etale_tensor_pairing_lift_eq_locally_res_eq {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) {U : Scheme.{0}}
    (x y : Tens I J U w) (h : τ.lift U w x = τ.lift U w y) :
    Loc U fun _ g => Tens.res g w x = Tens.res g w y := by
  obtain ⟨S, hS, hh⟩ := hτ.2 U w (x - y) (by rw [map_sub, h, sub_self])
  exact ⟨S, hS, fun V g hg => sub_eq_zero.1 (by rw [← map_sub]; exact hh V g hg)⟩

theorem alpha_locInj {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology (alpha τ w) where
  equalizerSieve_mem {U} x y h := by
    obtain ⟨S, hS, hh⟩ := etale_tensor_pairing_lift_eq_locally_res_eq τ hτ w x y h
    exact Scheme.etaleTopology.superset_covering (fun V g hg => hh V g hg) hS

end LateralTheory.EtaleFoundations.TensUnivDeg

open LateralTheory.EtaleFoundations.TensUnivDeg in
theorem LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  intro R _ I J K τ hτ I' J' K' ν f g w
  have := alpha_locSurj τ hτ w
  have := alpha_locInj τ hτ w
  have hW : Scheme.etaleTopology.W (alpha τ w) := GrothendieckTopology.W_of_isLocallyBijective _ _
  obtain ⟨m, hm⟩ := (hW (K'.X w).obj (K'.X w).property).2 (beta ν f g w)
  refine ⟨⟨m⟩, fun U s t h a b => ?_⟩
  have e := congrArg (fun φ : TP I J w ⟶ (K'.X w).obj => (φ.app (op U)).hom
    (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) ⟨(s, t), h⟩ (a ⊗ₜ b))) hm
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  change Sec.map ⟨m⟩ (τ.lift U w _) = (ν.lift U w ∘ₗ Tmap f g U w) _ at e
  rw [lift_lof, LinearMap.comp_apply, tmap_lof, lift_lof] at e
  exact e
end

section
namespace LateralTheory.Fin.EtaleTensorPairUniversalProperty
theorem etale_tensor_complex_degreewise_universal : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification
theorem etale_tensor_complex_universal_of_degreewise : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise <;> first | exact etale_tensor_complex_degreewise_universal
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := etale_tensor_complex_universal_of_degreewise
end LateralTheory.Fin.EtaleTensorPairUniversalProperty
end
