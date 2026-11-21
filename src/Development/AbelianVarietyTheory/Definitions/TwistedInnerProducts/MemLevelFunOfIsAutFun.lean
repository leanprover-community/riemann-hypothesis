import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil
open GlobalTheory.AdelicU (splitProj compFin splitEquiv splitEquivIn splitHom isCMExt_host)
open GlobalTheory.EmbChart (tensAt atPlace idem)
open GlobalTheory.StepData (LatFrame reGL)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocFrame

section Inst

variable {F : Type} [Field F] [NumberField F]

scoped instance relFv (v : HeightOneSpectrum (𝓞 F)) : ValuativeRel (Fv F v) := GlobalTheory.LocalData.complRel v

scoped instance locFieldFv (v : HeightOneSpectrum (𝓞 F)) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

scoped instance borelFv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩

def locChar (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {v : HeightOneSpectrum (𝓞 F)} (a : Fv F v) :
    AddChar (Fv F v) Circle where
  toFun x := ⟨ψ (atPlace v (a * x)), mem_sphere_zero_iff_norm.2 (hψ _)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' x y := Circle.ext (by
    change ψ _ = ψ _ * ψ _
    rw [mul_add, map_add, AddChar.map_add_eq_mul])

theorem coe_locChar (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {v : HeightOneSpectrum (𝓞 F)} (a x : Fv F v) :
    (locChar ψ hψ a x : ℂ) = psiV F ψ v (a * x) := rfl

theorem continuous_locChar {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {v : HeightOneSpectrum (𝓞 F)} (a : Fv F v) : Continuous (locChar ψ hψ a) :=
  Continuous.subtype_mk (hc.comp (continuous_const.prodMk
    ((GlobalTheory.AdelicU.continuous_singleFin v).comp (continuous_const.mul continuous_id)))) _

theorem mat_emb_sub_one {E : Type} [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (v : HeightOneSpectrum (𝓞 F)) (x : GlobalTheory.AdelicU.GLoc σ J v) (i j : Fin n) :
    ((GlobalTheory.AdelicU.matHom _ σ J (GlobalTheory.AdelicU.emb σ J v x)).val - 1) i j =
      tensAt E v (((GlobalTheory.AdelicU.matHom _ σ J x).val - 1) i j) := by
  let A : Af F ⊗[F] E →ₙ+* AF F ⊗[F] E := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (R' := AF F) (LinearMap.inr F (Ainf F) (Af F))
    (fun _ _ => Prod.ext (mul_zero _).symm rfl)
  let B : Fv F v ⊗[F] E →ₙ+* Af F ⊗[F] E :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v)
  have h (y) : A (B y) = tensAt E v y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => rfl
  change (1 - A 1) * (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j +
    A ((1 - B 1) * (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j + B ((GlobalTheory.AdelicU.matHom _ σ J x).val i j)) -
      (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j = _
  rw [map_add, h, Matrix.sub_apply, map_sub]
  by_cases e : i = j
  · subst e
    simp only [Matrix.one_apply_eq, mul_one, map_sub, h]
    ring
  · simp only [Matrix.one_apply_ne e, mul_zero, map_zero, zero_add, sub_zero]

end Inst

section Bases

variable {k ι Y : Type} [Field k] [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]

def vec (β : LatFrame k ι Y) (i : ι) : Y → k := fun y => β.bas.val y (β.ord i)

def cols (β : LatFrame k ι Y) : Matrix Y ι k := β.bas.val.submatrix id β.ord

def what₂ (β : LatFrame k ι Y) : Matrix ι Y k := (β.bas⁻¹).val.submatrix β.ord id

omit [Fintype ι] [DecidableEq ι] in
theorem cols_apply (β : LatFrame k ι Y) (y : Y) (i : ι) : cols β y i = vec β i y := rfl

omit [Fintype ι] in
theorem rows_mul_cols (β : LatFrame k ι Y) : what₂ β * cols β = 1 := by
  rw [what₂, cols, ← submatrix_mul _ _ _ _ _ Function.bijective_id, Units.inv_mul, submatrix_one_equiv]

omit [DecidableEq ι] in
theorem cols_mul_rows (β : LatFrame k ι Y) : cols β * what₂ β = 1 := by
  rw [what₂, cols, ← submatrix_mul _ _ _ _ _ β.ord.bijective, Units.mul_inv, submatrix_id_id]

theorem conj_val (β : LatFrame k ι Y) (g : GL ι k) : (β.conj g).val = cols β * g.val * what₂ β := by
  have h : g.val = (reGL β.ord g).val.submatrix β.ord β.ord := by
    rw [GlobalTheory.StepData.reGL_val, submatrix_submatrix]; simp
  rw [LatFrame.conj_apply, Units.val_mul, Units.val_mul, h, what₂, cols, ← submatrix_mul _ _ _ _ _ β.ord.bijective,
    ← submatrix_mul _ _ _ _ _ β.ord.bijective, submatrix_id_id]

theorem conj_mul_cols (β : LatFrame k ι Y) (g : GL ι k) : (β.conj g).val * cols β = cols β * g.val := by
  rw [conj_val, Matrix.mul_assoc, rows_mul_cols, Matrix.mul_one]

theorem conj_mulVec_vec (β : LatFrame k ι Y) (g : GL ι k) (j : ι) :
    (β.conj g).val *ᵥ vec β j = ∑ r, g.val r j • vec β r := by
  funext y
  have h := congrFun (congrFun (conj_mul_cols β g) y) j
  rw [Finset.sum_apply]
  refine h.trans (Finset.sum_congr rfl fun r _ => mul_comm _ _)

omit [DecidableEq ι] in

theorem exists_frame (hc : Fintype.card ι = Fintype.card Y) (M : Matrix Y ι k) (hM : ∀ u, M *ᵥ u = 0 → u = 0) :
    ∃ β : LatFrame k ι Y, cols β = M := by
  let e := Fintype.equivOfCardEq hc
  have h : IsUnit (M.submatrix id e.symm) := by
    refine Matrix.mulVec_injective_iff_isUnit.1 ((injective_iff_map_eq_zero (Matrix.mulVecLin _)).2 fun u hu => ?_)
    rw [mulVecLin_apply, submatrix_mulVec_equiv] at hu
    have := hM _ hu
    funext y
    simpa using congrFun this (e.symm y)
  exact ⟨⟨e, h.unit⟩, by ext y i; simp [cols]⟩

theorem continuous_conj [TopologicalSpace k] [IsTopologicalRing k] (β : LatFrame k ι Y) : Continuous β.conj :=
  (continuous_const.mul (Units.continuous_map (f := (Matrix.reindexRingEquiv k β.ord).toMonoidHom)
    (continuous_id.matrix_submatrix _ _))).mul continuous_const

end Bases

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

def piW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D →+* Fv D.host.F v :=
  (splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (compFin D.host.F D.host.E v)

theorem chart_piW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : GlobalTheory.SplitHecke.Chart (idem τ) v (piW τ) :=
  GlobalTheory.EmbChart.chart_idem τ

theorem piW_incA (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : D.host.E) : piW τ (incA D x) = τ x := by
  change splitProj τ (GlobalTheory.AdelicU.evFin D.host.F v 1 ⊗ₜ x) = _
  rw [map_one, GlobalTheory.AdelicU.splitProj_tmul, one_mul]

def weilChar (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    AddChar (Fv D.host.F v) Circle := locChar ψ hψ (τ D.host.xi0)

theorem hermND (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  ⟨fun i j => congrFun (congrFun (gram_conjTranspose V) i) j, gram_det_ne V⟩

section Loc

variable (V : HSp D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {ι : Type} [Fintype ι] [DecidableEq ι]
  (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

def locPt : GL ι (Fv D.host.F v) ≃* GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v :=
  β.conj.trans (splitEquiv (isCMExt_host D) (hermND V) τ).symm.toMulEquiv

def locGL : GL ι (Fv D.host.F v) →* GA D V :=
  (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v).comp (locPt V τ β).toMonoidHom

theorem proj_locGL (g : GL ι (Fv D.host.F v)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (locGL V τ β g) = locPt V τ β g := GlobalTheory.AdelicU.proj_emb_self _ _ _ _

theorem proj_locGL_ne {u : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v) (g : GL ι (Fv D.host.F v)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u (locGL V τ β g) = 1 := GlobalTheory.AdelicU.proj_emb_ne _ _ h _

theorem locGL_mem_GfC (g : GL ι (Fv D.host.F v)) : locGL V τ β g ∈ GfC V :=
  GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ _ _)

theorem map_piW (g : GA D V) :
    (mt V g).map (piW τ) = (splitHom D.sp.cm.sig V.gram τ (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).val := rfl

theorem map_piW_locGL (g : GL ι (Fv D.host.F v)) : (mt V (locGL V τ β g)).map (piW τ) = (β.conj g).val := by
  rw [map_piW, proj_locGL]
  exact congrArg Units.val (GlobalTheory.AdelicU.splitHom_splitLift _ _ _ _)

theorem continuous_locPt : Continuous (locPt V τ β) :=
  (splitEquiv (isCMExt_host D) (hermND V) τ).symm.continuous.comp (continuous_conj β)

theorem continuous_locGL : Continuous (locGL V τ β) :=
  (GlobalTheory.AdelicU.continuous_emb _ _ v).comp (continuous_locPt V τ β)

theorem commute_locGL (g : GL ι (Fv D.host.F v)) {h : GA D V} (hh : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v h = 1) :
    Commute (locGL V τ β g) h := GlobalTheory.AdelicU.commute_emb _ _ _ hh

theorem commute_locGL_locGL {u : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ u) (τ' : D.host.E →ₐ[D.host.F] Fv D.host.F u)
    {ι' : Type} [Fintype ι'] [DecidableEq ι'] (β' : LatFrame (Fv D.host.F u) ι' (Fin V.rank))
    (g : GL ι (Fv D.host.F v)) (g' : GL ι' (Fv D.host.F u)) : Commute (locGL V τ β g) (locGL V τ' β' g') :=
  commute_locGL V τ β g (proj_locGL_ne V τ' β' h g')

theorem mt_locGL_sub_one (g : GL ι (Fv D.host.F v)) (i j : Fin V.rank) :
    (mt V (locGL V τ β g) - 1) i j =
      tensAt D.host.E v (((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (locPt V τ β g)).val - 1) i j) :=
  mat_emb_sub_one D.sp.cm.sig V.gram v _ i j

end Loc

section Rep

variable (V : HSp D)

def levelFun : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, f (g * k) = f g}
  zero_mem' := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  add_mem' := fun ⟨U, hU, h⟩ ⟨U', hU', h'⟩ => ⟨U ⊓ U', hU.inter hU', fun k hk hf g => by
    rw [Pi.add_apply, Pi.add_apply, h k hk.1 hf, h' k hk.2 hf]⟩
  smul_mem' := fun c _ ⟨U, hU, h⟩ => ⟨U, hU, fun k hk hf g => by rw [Pi.smul_apply, Pi.smul_apply, h k hk hf]⟩

def IsFinStable (U : Submodule ℂ (GA D V → ℂ)) : Prop := ∀ x ∈ GfC V, ∀ f ∈ U, rTrans x f ∈ U

theorem rTrans_mem_levelFun (x : GA D V) {f : GA D V → ℂ} (hf : f ∈ levelFun V) : rTrans x f ∈ levelFun V := by
  obtain ⟨U, hU, h⟩ := hf
  refine ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, hU.preimage ((continuous_const.mul continuous_id).mul continuous_const),
    fun k hk hf g => ?_⟩
  have h1 : x⁻¹ * k * x⁻¹⁻¹ ∈ GfC V := (MonoidHom.normal_ker _).conj_mem k hf x⁻¹
  have h2 := h _ hk h1 (g * x)
  change f (g * x * (x⁻¹ * k * x⁻¹⁻¹)) = _ at h2
  rw [rTrans, rTrans, ← h2]
  congr 1
  group

theorem isFinStable_levelFun : IsFinStable V (levelFun V) := fun x _ _ hf => rTrans_mem_levelFun V x hf

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {ι : Type} [Fintype ι] [DecidableEq ι]
  (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

def locReg : Representation ℂ (GL ι (Fv D.host.F v)) (GA D V → ℂ) :=
  (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ).comp (locGL V τ β)


def locRepOn (U : Submodule ℂ (GA D V → ℂ)) (hU : IsFinStable V U) : Representation ℂ (GL ι (Fv D.host.F v)) U :=
  GlobalTheory.PRep.sub (locReg V τ β) U fun g f hf => hU _ (locGL_mem_GfC V τ β g) f hf


def locRep : Representation ℂ (GL ι (Fv D.host.F v)) (levelFun V) := locRepOn V τ β _ (isFinStable_levelFun V)

theorem isOpen_stab {f : GA D V → ℂ} (hf : f ∈ levelFun V) : IsOpen {g | locReg V τ β g f = f} := by
  obtain ⟨U, hU, h⟩ := hf
  refine isOpen_iff_mem_nhds.2 fun g hg => ?_
  have h1 : IsOpen {x | locGL V τ β (g⁻¹ * x) ∈ U} :=
    hU.preimage ((continuous_locGL V τ β).comp (continuous_const.mul continuous_id))
  refine Filter.mem_of_superset (h1.mem_nhds (by simp)) fun x hx => ?_
  have h2 : locReg V τ β (g⁻¹ * x) f = f := funext fun y => h _ hx (locGL_mem_GfC V τ β _) y
  change locReg V τ β x f = f
  rw [← mul_inv_cancel_left g x, map_mul, Module.End.mul_apply, h2, hg]


end Rep

section Position

open GlobalTheory.RootEx

variable {k : Type} [Field k] [MeasurableSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
  (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)

def downIter (q d : ℕ) : (A → ℂ) → A → ℂ :=
  Nat.rec (motive := fun _ => (A → ℂ) → A → ℂ) (fun l => l) (fun d F l => F (exDown ν (q + d) σ l)) d


theorem downIter_succ (q d : ℕ) (l : A → ℂ) : downIter ν σ q (d + 1) l = downIter ν σ q d (exDown ν (q + d) σ l) := rfl

def upIter (p d : ℕ) (l : A → ℂ) : A → ℂ :=
  Nat.rec (motive := fun _ => A → ℂ) l (fun d l' => exUp ν (p + d) σ l') d


theorem upIter_succ (p d : ℕ) (l : A → ℂ) : upIter ν σ p (d + 1) l = exUp ν (p + d) σ (upIter ν σ p d l) := rfl

def exTo (p q : ℕ) (l : A → ℂ) : A → ℂ := upIter ν σ p (q - p) (downIter ν σ q (p - q) l)




theorem exTo_comp (σ' : Representation ℂ (GL (n ⊕ Fin c) k) A') (f : A' → A) (hf : ∀ g x, f (σ' g x) = σ g (f x))
    (z : ℂ) (p q : ℕ) (l : A → ℂ) : exTo ν σ' p q (fun x => z * l (f x)) = fun x => z * exTo ν σ p q l (f x) := by
  have hd (d : ℕ) : ∀ l : A → ℂ,
      downIter ν σ' q d (fun x => z * l (f x)) = fun x => z * downIter ν σ q d l (f x) := by
    induction d with
    | zero => exact fun _ => rfl
    | succ d ih =>
      intro l
      rw [downIter_succ, downIter_succ, ← ih]
      congr 1; funext x
      simp only [exDown, hf, integral_const_mul]
  have hu (d : ℕ) (l : A → ℂ) : upIter ν σ' p d (fun x => z * l (f x)) = fun x => z * upIter ν σ p d l (f x) := by
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [upIter_succ, upIter_succ, ih]
      funext x
      simp only [exUp, hf, integral_const_mul]
  rw [exTo, exTo, hd, hu]

theorem exTo_law (σ' : Representation ℂ (GL (n ⊕ Fin c) k) A') {T : A' → A} (hT : ∀ g x, T (σ' g x) = σ g (T x))
    {l : A → ℂ} {l' : A' → ℂ} {z : ℂ} (h : ∀ x, l (T x) = z * l' x) (p q : ℕ) (x : A') :
    exTo ν σ p q l (T x) = z * exTo ν σ' p q l' x := by
  have h1 := congrFun (exTo_comp ν σ σ' T hT 1 p q l) x
  have h2 := congrFun (exTo_comp ν σ' σ' id (fun _ _ => rfl) z p q l') x
  simp only [one_mul, h, id] at h1 h2
  rw [← h1, h2]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [ν.IsAddHaarMeasure]
  {ψ : AddChar k Circle} {σ}


end Position

section Positions

open GlobalTheory.RootEx

variable {I : Type} {k : I → Type} [∀ i, Field (k i)] [∀ i, MeasurableSpace (k i)] {n : Type} [Fintype n] [DecidableEq n]
  {c : ℕ} {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
  (ν : ∀ i, Measure (k i)) (σ : ∀ i, Representation ℂ (GL (n ⊕ Fin c) (k i)) A)

def exList (p q : I → ℕ) (L : List I) (l : A → ℂ) : A → ℂ :=
  L.foldr (fun i l => exTo (ν i) (σ i) (p i) (q i) l) l

theorem exList_law (σ' : ∀ i, Representation ℂ (GL (n ⊕ Fin c) (k i)) A') {T : A' → A}
    (hT : ∀ i g x, T (σ' i g x) = σ i g (T x)) {l : A → ℂ} {l' : A' → ℂ} {z : ℂ} (h : ∀ x, l (T x) = z * l' x)
    (p q : I → ℕ) (L : List I) (x : A') : exList ν σ p q L l (T x) = z * exList ν σ' p q L l' x := by
  induction L generalizing x with
  | nil => exact h x
  | cons i L ih => exact exTo_law (ν i) (σ i) (σ' i) (hT i) ih _ _ x


variable [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
  [∀ i, BorelSpace (k i)] [∀ i, (ν i).IsAddHaarMeasure] {ψ : ∀ i, AddChar (k i) Circle} {σ}


end Positions

end GlobalTheory.LocFrame

end
