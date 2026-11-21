import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.LmLeStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso

noncomputable section

namespace GlobalTheory.CompanionTheory.DisoHm

section Lift
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'}

def liftM (m : CH.Mor F F' σ) {P : ObjectProperty C} (hP : ∀ T, P (m.G.obj T)) : CH.Mor (P.ι ⋙ F) F' σ where
  G := P.lift m.G hP
  τ := m.τ
  nat φ x := m.nat φ x
end Lift

section Scal
variable {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def thPc : PDF Λ (Thick L) where
  A := B.OA L c
  J := ⟨fun T => T.J, fun φ _ hx => φ.hle hx⟩
  dp {T} k x := T.δ.dpow k x
  dp_zero {T} _ hx := T.δ.dpow_zero hx
  dp_one {T} _ hx := T.δ.dpow_one hx
  dp_zero_right {T} _ hk := T.δ.dpow_eval_zero hk
  dp_add {T} k _ _ hx hy := T.δ.dpow_add hx hy
  dp_map φ k x hx := (φ.dp.2 x hx).symm

variable {L}

abbrev sPc (Q : ObjectProperty (Thick L)) : PDF Λ Q.FullSubcategory := (thPc L c).res Q.ι

def polyC {Q : ObjectProperty (Thick L)} (P : Poly (sP Q)) : Poly (sPc c Q) where
  P := P.P
  j := P.j
  X := P.X
  X_mem := P.X_mem
  univ := P.univ
  span := P.span

def frameC {Q : ObjectProperty (Thick L)} {d : ℕ} (E : Frame (sP Q) d) : Frame (sPc c Q) d where
  D := E.D
  ne := E.ne
  τ := E.τ
  mem := E.mem
  add := E.add
  nat := E.nat
  bij := E.bij

theorem polyC_crit {Q : ObjectProperty (Thick L)} (P : Poly (sP Q)) (r : ℤ)
    (h : P.Crit (fun _ => IdF.bot _) r) : (polyC c P).Crit (fun _ => IdF.bot _) r := h

end Scal

section G
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lm_eq_span (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (T : Q.FullSubcategory) :
    lm (l := l) T.obj m = (IdF.span (sP Q).A ((l : O) ^ m)).S T := by
  change Ideal.span {(l : T.obj.B) ^ m} = Ideal.span {T.obj.i ((l : O) ^ m)}
  rw [map_pow, map_natCast]

def gρ (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (T : Q.FullSubcategory) :
    (sPc (Ideal.Quotient.mk _) P).A.obj ((P.lift (GF h Q m hQ) hP).obj T) →ₐ[O]
      (sP Q).A.obj T ⧸ (IdF.span (sP Q).A ((l : O) ^ m)).S T :=
  { Ideal.Quotient.factor (lm_eq_span Q m T).le with
    commutes' := fun a => rfl }

theorem gρ_mk (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (T : Q.FullSubcategory) (a : T.obj.B) :
    gρ h Q m hQ P hP T (Ideal.Quotient.mk (lm (l := l) T.obj m) a) = Ideal.Quotient.mk _ a := rfl

theorem gρ_inj (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (T : Q.FullSubcategory) :
    Function.Injective (gρ h Q m hQ P hP T) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
  have e : Ideal.Quotient.mk ((IdF.span (sP Q).A ((l : O) ^ m)).S T) (show T.obj.B from a) = Ideal.Quotient.mk _ (show T.obj.B from b) := hxy
  exact Ideal.Quotient.eq.2 ((lm_eq_span Q m T).ge (Ideal.Quotient.eq.1 e))

def gQ (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) :
    QMor (sPc (Ideal.Quotient.mk _) P) (sP Q) (IdF.span (sP Q).A ((l : O) ^ m)) where
  G := P.lift (GF h Q m hQ) hP
  ρ := gρ h Q m hQ P hP
  inj := gρ_inj h Q m hQ P hP
  nat {T T'} φ x y hxy := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
    have e : Ideal.Quotient.mk ((IdF.span (sP Q).A ((l : O) ^ m)).S T) (show T.obj.B from a) = Ideal.Quotient.mk _ y := hxy
    have e' := (IdF.span (sP Q).A ((l : O) ^ m)).map_mem φ (Ideal.Quotient.eq.1 e)
    rw [map_sub] at e'
    exact Ideal.Quotient.eq.2 e'
  dp T k x y hx hy hxy := by
    have hT := hQ _ T.property
    have e : x = Ideal.Quotient.mk (lm (l := l) T.obj m) (show T.obj.B from y) := gρ_inj h Q m hQ P hP T hxy
    subst e
    have hy' : (show T.obj.B from y) ∈ T.obj.J := hy
    have := (GD_spec T.obj m hT).2 k (show T.obj.B from y) (T.obj.δ.dpow k y) (Ideal.mem_sup_left hy')
      (T.obj.δ.factorial_mul_dpow_eq_pow hy')
    exact congrArg (gρ h Q m hQ P hP T) this

def gP (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) :
    CH.Mor (P.ι ⋙ OMm h q m) (sq (IdF.top (sP Q).A) (stdI Q none ((l : O) ^ m))) (RingHom.id O) :=
  liftM (gMor h Q m hQ) hP

end G

section Gen
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem IdF.ext' {a b : IdF A} (h : ∀ T, a.S T = b.S T) : a = b := by
  cases a
  cases b
  congr
  exact funext h

theorem idM_bij {R' : Type} [CommRing R'] {σ : R →+* R'} {F : C ⥤ ModuleCat.{0} R} {F' : C ⥤ ModuleCat.{0} R'}
    (τ : ∀ T, F.obj T →ₛₗ[σ] F'.obj T)
    (nat : ∀ {T T' : C} (φ : T ⟶ T') (x : F.obj T), τ T' ((F.map φ).hom x) = (F'.map φ).hom (τ T x))
    (h : ∀ T, Function.Bijective (τ T)) (j : ℕ) :
    Function.Bijective ((⟨𝟭 C, τ, nat⟩ : CH.Mor F F' σ).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij _ (fun n => ⟨fun x y hxy => ?_, fun y => ?_⟩) j
  · funext s
    refine (h _).1 ?_
    have := congrFun hxy s
    exact this
  · exact ⟨fun s => Function.surjInv (h _).2 (y s), funext fun s => Function.surjInv_eq (h _).2 (y s)⟩

theorem sqLe_bij {a b a' b' : IdF A} (ha : ∀ T, a.S T = a'.S T) (hb : ∀ T, b.S T = b'.S T) (j : ℕ) :
    Function.Bijective ((sqLe (a := a) (b := b) (a' := a') (b' := b') (fun T => (ha T).le) (fun T => (hb T).le)).pull j) := by
  obtain rfl : a = a' := IdF.ext' ha
  obtain rfl : b = b' := IdF.ext' hb
  refine idM_bij (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ
    (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).nat (fun T => ?_) j
  have e : (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ T = LinearMap.id := by
    ext ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [e]
  exact Function.bijective_id
end Gen

section Lk
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem gQ_o (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (b : IdF (sP Q).A)
    (hb : ∀ T, (IdF.span (sP Q).A ((l : O) ^ m)).S T ≤ b.S T)
    (hb' : ∀ T, (stdI Q none ((l : O) ^ m)).S T ≤ b.S T) (j : ℕ) (x : CH.H (P.ι ⋙ OMm h q m) j) :
    ((gQ h Q m hQ P hP).o b hb).pull j x =
      (sqLe (a := IdF.top (sP Q).A) (a' := IdF.top (sP Q).A) (fun _ => le_rfl) hb').pull j ((gP h Q m hQ P hP).pull j x) := by
  refine (CrystallineSemistableComparison.P.prism (σ := RingHom.id O) ((gQ h Q m hQ P hP).o b hb)
    ((gP h Q m hQ P hP).comp (sqLe (a := IdF.top (sP Q).A) (a' := IdF.top (sP Q).A) (fun _ => le_rfl) hb')) (𝟙 _)
    (fun T y => ?_) j x).trans ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) _ _ j x).1)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
  rfl

end Lk
end GlobalTheory.CompanionTheory.DisoHm

namespace GlobalTheory.CompanionTheory.DisoHm
section Cover
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R}

def smulM (m : CH.Mor F F' (RingHom.id R)) (n : R) : CH.Mor F F' (RingHom.id R) where
  G := m.G
  τ T := n • m.τ T
  nat φ x := by
    change n • m.τ _ _ = (F'.map φ).hom (n • m.τ _ x)
    rw [m.nat, map_smul]

theorem smulM_pull (m : CH.Mor F F' (RingHom.id R)) (n : R) (j : ℕ) (x : CH.H F j) :
    (smulM m n).pull j x = n • m.pull j x := by
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  rfl

theorem tens_iff {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') :
    Tens R (N := fun _ : Unit => R) (M := fun _ => M) (M' := M') (fun _ n x => n • f x) ↔ Function.Bijective f := by
  let e : (∀ _ : Unit, R ⊗[R] M) ≃+ M :=
    (AddEquiv.piUnique (fun _ : Unit => R ⊗[R] M)).trans (TensorProduct.lid R M).toAddEquiv
  have he : ∀ n x, e (Pi.single () (n ⊗ₜ x)) = n • x := fun n x => by simp [e]
  constructor
  · rintro ⟨g, hg⟩
    have : ∀ x, f x = g (e.symm x) := fun x => by
      have h2 : g (Pi.single () ((1 : R) ⊗ₜ x)) = f x := (hg () 1 x).trans (one_smul _ _)
      have h3 : e.symm x = Pi.single () ((1 : R) ⊗ₜ x) := by
        refine (AddEquiv.symm_apply_eq e).2 ?_
        rw [he, one_smul]
      rw [h3, h2]
    have e2 : (f : M → M') = (e.symm.trans g) := funext this
    rw [e2]
    exact (e.symm.trans g).bijective
  · intro hf
    refine ⟨e.trans (AddEquiv.ofBijective f.toAddMonoidHom hf), fun _ n x => ?_⟩
    change f (e _) = _
    rw [he, map_smul]

theorem cover_bij (m : CH.Mor F F' (RingHom.id R)) {A : Type} [Fintype A] (U : A → ObjectProperty C)
    (U' : A → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hU' : ∀ α, Cosieve (U' α)) (hc : ∀ T, ∃ α, U α T)
    (hc' : ∀ T, ∃ α, U' α T) (h : ∀ α T, U' α T → U α (m.G.obj T))
    (H : ∀ S : Finset A, S.Nonempty → ∀ j, Function.Bijective
      ((morU m (U := capS U S) (U' := capS U' S) fun T hT α hα => h α T (hT α hα)).pull j)) (j : ℕ) :
    Function.Bijective (m.pull j) := by
  have key := GlobalTheory.CompanionTheory.CosieveBC.base_change_of_cover (σ := RingHom.id R) m.G (ι := Unit) (fun _ => R) (fun _ => F) F'
    (fun _ n T => (smulM m n).τ T) (fun _ n _ _ φ x => (smulM m n).nat φ x)
    (fun _ n n' T x => by simp [smulM, add_smul]) (fun _ r n T x => by simp [smulM, mul_smul])
    U U' hU hU' hc hc' h (fun S hS j => ?_) j
  · obtain ⟨g, hg⟩ := key
    exact (tens_iff (m.pull j)).1 ⟨g, fun i n x => (hg i n x).trans (smulM_pull m n j x)⟩
  · obtain ⟨g, hg⟩ := (tens_iff ((morU m (U := capS U S) (U' := capS U' S) fun T hT α hα => h α T (hT α hα)).pull j)).2 (H S hS j)
    refine ⟨g, fun i n x => (hg i n x).trans ?_⟩
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
end Cover
end GlobalTheory.CompanionTheory.DisoHm

namespace GlobalTheory.CompanionTheory.DisoHm
section Ch
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem pt_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) :
    pt (GObj h T m hT) = Spec.map (CommRingCat.ofHom (thG (l := l) T m)) ≫ pt T := rfl

theorem inU_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) {V : X.Opens} (hV : InU V T) :
    InU V (GObj h T m hT) := by
  unfold InU
  rw [pt_G]
  intro x _
  exact hV (show (Spec.map (CommRingCat.ofHom (thG (l := l) T m))) x ∈ ⊤ from trivial)

theorem ev_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) {V : X.Opens} (hV : InU V T)
    (hV' : InU V (GObj h T m hT)) (f : Γ(X, V)) :
    ev (GObj h T m hT) hV' f = thG (l := l) T m (ev T hV f) :=
  GlobalTheory.LogCris.evalAt_map _ (pt T) hV hV' f

theorem ev_hom {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {κ : O →+* R ⧸ I} {V : X.Opens}
    {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : InU V T) (h' : InU V T') (f : Γ(X, V)) :
    ev T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ V), GlobalTheory.Cris.evalAt y V hh f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
    intro y hy hh
    subst hy
    exact GlobalTheory.LogCris.evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) h hh f
  exact key _ (Site.pt_hom φ) h'

theorem exists_sig (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hg : cL.Good)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d)
    (ht : ∀ i, ev cO.D cO.inV (c.t i) = Ideal.Quotient.mk _ (cO.t i))
    (hT : Good (l := l) cO.D m) :
    ∃ σ : cL.D ⟶ GObj h cO.D m hT, ∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i) := by
  have hV := inU_G h cO.D m hT cO.inV
  obtain ⟨σ₀⟩ := hg.1 _ hV
  have hy : ∀ i, ((show (GObj h cO.D m hT).B from Ideal.Quotient.mk (lm (l := l) cO.D m) (cO.t i)) - σ₀.φ (cL.t i)) ∈
      (GObj h cO.D m hT).J := by
    intro i
    refine Ideal.Quotient.eq.1 ?_
    have a1 := ev_G h cO.D m hT cO.inV hV (c.t i)
    have a2 := ev_hom σ₀ cL.inV hV (c.t i)
    rw [ht i] at a1
    rw [hcL i] at a2
    exact a1.symm.trans a2
  obtain ⟨σ, h1, -⟩ := hg.2 _ σ₀ _ hy
  exact ⟨σ, fun i => by simpa using h1 i⟩

end Ch
end GlobalTheory.CompanionTheory.DisoHm
end
end

section
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm

noncomputable section
namespace GlobalTheory.CompanionTheory.DisoHm
section Cmp
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem ev_base {W : X.Opens} (T : Thick (nlFun γ p X q κ)) (h : InU W T) (a : O) (r : R)
    (hr : κ a = Ideal.Quotient.mk I r) : ev T h (strV q W a) = Ideal.Quotient.mk T.J (T.i r) := by
  have e := evalAt_base q κ (show PtOver X q κ (T.B ⧸ T.J) from T.y).1.1 (pt T)
    (show PtOver X q κ (T.B ⧸ T.J) from T.y).2 h a
  refine e.trans ?_
  rw [hr]
  exact T.w r

theorem quot_eq_id {W : X.Opens} {d : ℕ} (c : Chart γ p q κ W d) (hW : IsAffineOpen W)
    (θ : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J)
    (h1 : ∀ r, θ (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r))
    (h2 : ∀ f, θ (ev c.D c.inV f) = ev c.D c.inV f) : θ = RingHom.id _ := by
  have key : ∀ θ' : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J,
      (∀ r, θ' (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r)) →
      (∀ f, θ' (ev c.D c.inV f) = ev c.D c.inV f) →
      (ptFun X q κ).map (CommRingCat.ofHom θ') c.D.y = c.D.y := by
    intro θ' a b
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine RingHom.ext fun z => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      have w := c.D.w r
      change θ' ((show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)) =
        (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)
      have w' : (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ (c.D.i r) := w
      rw [w']
      exact a r
    · change Spec.map (CommRingCat.ofHom θ') ≫ pt c.D = pt c.D
      have e : Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec = pt c.D :=
        GlobalTheory.CompanionTheory.ChartAlg.eq_specMap hW (pt c.D) c.inV
      have e2 : θ'.comp (ev c.D c.inV) = ev c.D c.inV := RingHom.ext b
      calc Spec.map (CommRingCat.ofHom θ') ≫ pt c.D
          = Spec.map (CommRingCat.ofHom θ') ≫ Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec := by rw [e]
        _ = Spec.map (CommRingCat.ofHom (θ'.comp (ev c.D c.inV))) ≫ hW.fromSpec := by
            rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        _ = pt c.D := by rw [e2, e]
  obtain ⟨g₀, -, hu⟩ := c.rep (CommRingCat.of (c.D.B ⧸ c.D.J)) c.D.y c.inV
  exact (hu _ (key θ h1 h2)).trans (hu _ (key _ (fun _ => rfl) (fun _ => rfl))).symm

end Cmp

theorem cmp_bij : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d),
    letI := (strV q W).toAlgebra
    ∀ (e : O ⊗[O] Γ(X, W) ≃+* cO.D.B), (∀ r, e (r ⊗ₜ 1) = cO.D.i r) → (∀ i, e (1 ⊗ₜ c.t i) = cO.t i) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))) →
      ∀ (hT : Good (l := l) cO.D m) (σ : cL.D ⟶ GObj h cO.D m hT),
        (∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i)) → Function.Bijective σ.φ := by
  intro l _ O _ X q h W d c m cL hcL cO
  letI := (strV q W).toAlgebra
  intro e he het hev hT σ hσ
  let E : Γ(X, W) ≃+* cO.D.B := (Algebra.TensorProduct.lid O Γ(X, W)).symm.toRingEquiv.trans e
  have hE : ∀ f, E f = e (1 ⊗ₜ f) := fun f => rfl
  have hEs : ∀ a, E (strV q W a) = cO.D.i a := fun a => by
    rw [hE, ← he]
    congr 1
    change (1 : O) ⊗ₜ[O] (algebraMap O Γ(X, W) a) = a ⊗ₜ 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hEt : ∀ i, E (c.t i) = cO.t i := het
  have hevE : ∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (E f) := hev
  let ψ : MvPolynomial (Fin d) O →+* cO.D.B := MvPolynomial.eval₂Hom cO.D.i cO.t
  have hψ : ψ.Etale := cO.etale
  let g : cO.D.B →+* cL.D.B ⧸ cL.D.J := (ev cL.D cL.inV).comp (E.symm : cO.D.B →+* Γ(X, W))
  let f₁ : MvPolynomial (Fin d) O →+* cL.D.B :=
    MvPolynomial.eval₂Hom (cL.D.i.comp (Ideal.Quotient.mk _)) cL.t
  have hg1 : ∀ f, g (E f) = ev cL.D cL.inV f := fun f => by
    change ev cL.D cL.inV (E.symm (E f)) = _
    rw [RingEquiv.symm_apply_apply]
  have hc : g.comp ψ = (Ideal.Quotient.mk cL.D.J).comp f₁ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · have e1 : ψ (MvPolynomial.C a) = E (strV q W a) := by
        rw [hEs]; simp [ψ]
      have e2 : f₁ (MvPolynomial.C a) = cL.D.i (Ideal.Quotient.mk _ a) := by simp [f₁]
      change g (ψ (MvPolynomial.C a)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.C a))
      rw [e1, e2, hg1]
      exact ev_base cL.D cL.inV a _ rfl
    · have e1 : ψ (MvPolynomial.X i) = E (c.t i) := by
        rw [hEt]; simp [ψ]
      have e2 : f₁ (MvPolynomial.X i) = cL.t i := by simp [f₁]
      change g (ψ (MvPolynomial.X i)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.X i))
      rw [e1, e2, hg1]
      exact hcL i
  obtain ⟨H, ⟨hH1, hH2⟩, -⟩ := GlobalTheory.T.etale_lifting_of_nil_ideal cL.D.J (GlobalTheory.CompanionTheory.ChartMaps.nil_J cL.D) _ _ ψ hψ f₁ g hc
  have hHi : ∀ a, H (cO.D.i a) = cL.D.i (Ideal.Quotient.mk _ a) := fun a => by
    have := RingHom.congr_fun hH1 (MvPolynomial.C a)
    simpa [ψ, f₁] using this
  have hHt : ∀ i, H (cO.t i) = cL.t i := fun i => by
    have := RingHom.congr_fun hH1 (MvPolynomial.X i)
    simpa [ψ, f₁] using this
  have hHe : ∀ f, Ideal.Quotient.mk cL.D.J (H (E f)) = ev cL.D cL.inV f := fun f => by
    rw [← hg1, ← hH2]
    rfl
  have hk : ∀ a ∈ lm (l := l) cO.D m, H a = 0 := by
    have hle : lm (l := l) cO.D m ≤ RingHom.ker H := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change H ((l : cO.D.B) ^ m) = 0
      have e1 : (l : cO.D.B) ^ m = cO.D.i ((l : O) ^ m) := by
        rw [map_pow, map_natCast]
      rw [e1, hHi, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
    exact fun a ha => hle ha
  let Hb : GB (l := l) cO.D m →+* cL.D.B := Ideal.Quotient.lift _ H hk
  have hHb : ∀ x, Hb (Ideal.Quotient.mk _ x) = H x := fun x => Ideal.Quotient.lift_mk _ H hk
  let mkG : cO.D.B →+* (GObj h cO.D m hT).B := Ideal.Quotient.mk (lm (l := l) cO.D m)
  have hV := inU_G h cO.D m hT cO.inV
  have hs : σ.φ.comp H = mkG := by
    have uniq := GlobalTheory.T.etale_lifting_of_nil_ideal (GObj h cO.D m hT).J (GlobalTheory.CompanionTheory.ChartMaps.nil_J (GObj h cO.D m hT)) _ _ ψ hψ
      (mkG.comp ψ) ((Ideal.Quotient.mk (GObj h cO.D m hT).J).comp mkG) rfl
    refine uniq.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · have e1 : ψ (MvPolynomial.C a) = cO.D.i a := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.C a))) = mkG (ψ (MvPolynomial.C a))
        rw [e1, hHi, σ.comm]
        rfl
      · have e1 : ψ (MvPolynomial.X i) = cO.t i := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.X i))) = mkG (ψ (MvPolynomial.X i))
        rw [e1, hHt, hσ]
        rfl
    · refine RingHom.ext fun x => ?_
      obtain ⟨f, rfl⟩ := E.surjective x
      have a1 := ev_G h cO.D m hT cO.inV hV f
      have a2 := ev_hom σ cL.inV hV f
      rw [hevE] at a1
      rw [← hHe] at a2
      exact a2.symm.trans a1
  have hs' : ∀ x, σ.φ (H x) = mkG x := fun x => RingHom.congr_fun hs x
  let ρ : cL.D.B →+* cL.D.B := Hb.comp σ.φ
  have hρH : ∀ x, ρ (H x) = H x := fun x => by
    change Hb (σ.φ (H x)) = H x
    rw [hs']
    exact hHb x
  have hρi : ∀ r, ρ (cL.D.i r) = cL.D.i r := fun r => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← hHi, hρH]
  have hρt : ∀ i, ρ (cL.t i) = cL.t i := fun i => by
    rw [← hHt, hρH]
  have hle : cL.D.J ≤ cL.D.J.comap ρ := by
    intro x hx
    have : cL.D.J ≤ cL.D.J.comap ρ := by
      conv_lhs => rw [cL.J_eq]
      refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
      rw [Ideal.mem_comap, Ideal.mem_comap, hρi, cL.J_eq]
      exact Ideal.mem_map_of_mem _ hr
    exact this hx
  have hθ : Ideal.quotientMap cL.D.J ρ hle = RingHom.id _ := by
    refine quot_eq_id cL c.affine _ (fun r => ?_) (fun f => ?_)
    · rw [Ideal.quotientMap_mk, hρi]
    · rw [← hHe, Ideal.quotientMap_mk, hρH]
  have hid : ρ = RingHom.id _ := by
    refine (GlobalTheory.CompanionTheory.ChartMaps.exists_unique_lift cL cL.D (RingHom.id _) (fun _ => rfl) cL.t (fun _ => rfl)).unique
      ⟨hρi, hρt, RingHom.ext fun x => ?_⟩ ⟨fun _ => rfl, fun _ => rfl, rfl⟩
    have := RingHom.congr_fun hθ (Ideal.Quotient.mk _ x)
    rw [Ideal.quotientMap_mk] at this
    exact this
  refine Function.bijective_iff_has_inverse.2 ⟨Hb, fun x => RingHom.congr_fun hid x, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) cO.D m from y)
  change σ.φ (Hb (Ideal.Quotient.mk _ x)) = _
  rw [hHb, hs']
  rfl

end GlobalTheory.CompanionTheory.DisoHm
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lift_tensor_compat : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d),
    letI := (strV q W).toAlgebra
    ∀ (e : O ⊗[O] Γ(X, W) ≃+* cO.D.B), (∀ r, e (r ⊗ₜ 1) = cO.D.i r) → (∀ i, e (1 ⊗ₜ c.t i) = cO.t i) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))) →
      ∀ (hT : Good (l := l) cO.D m) (σ : cL.D ⟶ GObj h cO.D m hT),
        (∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i)) → Function.Bijective σ.φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DisoHm.cmp_bij
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm

noncomputable section

namespace GlobalTheory.CompanionTheory.DisoHm

theorem dividedPowerFiltration_bot {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (hJ : J = ⊥) {r : ℕ} (hr : 1 ≤ r) :
    pdP δ r = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨L, hL, hr', rfl⟩
  have : ∃ q ∈ L, q.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (L.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact hc q hq)
    omega
  obtain ⟨q, hq, hq0⟩ := this
  have hz : δ.dpow q.1 q.2 = 0 := by
    have h2 : q.2 = 0 := by
      have := hL q hq
      rw [hJ] at this
      exact this
    rw [h2]
    exact δ.dpow_eval_zero hq0
  have : (L.map fun q => δ.dpow q.1 q.2).prod = 0 := List.prod_eq_zero (List.mem_map.2 ⟨q, hq, hz⟩)
  rw [this]
  exact zero_mem _

section Loc
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem tfBase_ol (h : OL l O) {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot O) l s where
  nil := dividedPowerFiltration_bot _ rfl hs
  tf r x hx := by
    cases r with
    | zero =>
      have h1 : (1 : O) ∈ pdP (dividedPowersBot O) 0 := Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
      simpa using Ideal.mul_mem_left _ x h1
    | succ r =>
      rw [dividedPowerFiltration_bot _ rfl (by omega)] at hx ⊢
      have hl : (l : O) ∈ nonZeroDivisors O := h.tf l (Fact.out : l.Prime).ne_zero
      exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hl).1 hx
  dv n hn := by
    obtain ⟨v, u, hlu, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l (Fact.out : l.Prime).ne_one
    obtain ⟨w, hw⟩ := (h.unit u hlu).exists_right_inv
    refine ⟨v, w, ?_⟩
    rw [e]
    push_cast
    rw [mul_assoc, hw, mul_one]

theorem o_bij (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (b : IdF (sP Q).A)
    (hb : ∀ T, (IdF.span (sP Q).A ((l : O) ^ m)).S T ≤ b.S T) (T : Q.FullSubcategory)
    (hle : b.S T ≤ (IdF.span (sP Q).A ((l : O) ^ m)).S T) :
    Function.Bijective (((gQ h Q m hQ P hP).o b hb).τ T) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
    have e : Ideal.Quotient.mk (b.S T) (show (sP Q).A.obj T from a) = Ideal.Quotient.mk (b.S T) (show (sP Q).A.obj T from c) :=
      congrArg Subtype.val hxy
    exact Ideal.Quotient.eq.2 ((lm_eq_span Q m T).ge (hle (Ideal.Quotient.eq.1 e)))
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk (lm (l := l) T.obj m) a, Subtype.ext rfl⟩

theorem local_bij (hLoc : DH.LocCmpq) (hPA : DH.PolyAll) (hPT : KH.PolyTf) (hCA : DH.ChartAlg) (hCP : DH.ChartP)
    (hCG : DH.ChartGood) (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (hd : d < s) (m : ℕ)
    (hQ : ∀ T, TO q l s {W} T → Good (l := l) T m)
    (hP : ∀ T, St (⊤ : ObjectProperty (Thick (Lm h q m))) {W} ((GF h (TO q l s {W}) m hQ).obj T)) (j : ℕ) :
    Function.Bijective ((gP h (TO q l s {W}) m hQ (St ⊤ {W}) hP).pull j) := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hnil : IsNilpotent ((l : ℕ) : Om l O m) := ⟨m, by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : O) ^ m})), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _⟩
  obtain ⟨PL, hPL⟩ := hPA (pdm h m) l hl0 q (κm l O m) ⊤ (Or.inl rfl) {W}
  obtain ⟨PO, hPO⟩ := hPT (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  obtain ⟨cL, -, hcL⟩ := hCP (pdm h m) l hl0 hnil q (κm l O m) c
  obtain ⟨cO, e, hTF, hi, ht, hev⟩ := hCA (dividedPowersBot O) l s (tfBase_ol h (by omega)) q (Ideal.Quotient.mk ⊥)
    (fun _ => rfl) c
  have hgL := hCG cL
  have hgO := hCG cO
  have hDQ : TO q l s {W} cO.D := ⟨hTF, W, rfl, cO.inV⟩
  have hDP : St (⊤ : ObjectProperty (Thick (Lm h q m))) {W} cL.D := ⟨trivial, W, rfl, cL.inV⟩
  have hT : Good (l := l) cO.D m := hQ _ hDQ
  have hevt : ∀ i, ev cO.D cO.inV (c.t i) = Ideal.Quotient.mk _ (cO.t i) := fun i => by rw [hev, ht]
  obtain ⟨σ, hσ⟩ := exists_sig h c m cL hgL hcL cO hevt hT
  have hσb := GlobalTheory.T.chart_lift_tensor_compat h c m cL hcL cO e hi ht hev hT σ hσ
  let E := frameC (Ideal.Quotient.mk (Ideal.span {(l : O) ^ m}))
    (cL.frame hgL (St (⊤ : ObjectProperty (Thick (Lm h q m))) {W}) (fun T hT => by
      obtain ⟨-, V, rfl, hV⟩ := hT
      exact hV) hDP)
  let E' := cO.frame hgO (TO q l s {W}) (fun T hT => by
      obtain ⟨-, V, rfl, hV⟩ := hT
      exact hV) hDQ
  let M := gQ h (TO q l s {W}) m hQ (St ⊤ {W}) hP
  let e' : E.D ⟶ M.G.obj E'.D := ObjectProperty.homMk σ
  have he : M.Fr E E' e' := by
    intro i T s₁ s₂
    change gρ h (TO q l s {W}) m hQ (St ⊤ {W}) hP T (gφ s₂.hom m (σ.φ (cL.t i)) - gφ s₁.hom m (σ.φ (cL.t i))) =
      Ideal.Quotient.mk _ (s₂.hom.φ (cO.t i) - s₁.hom.φ (cO.t i))
    rw [hσ]
    rfl
  let b : ℤ → IdF (sP (TO q l s {W})).A := fun r => stdI (TO q l s {W}) (some r) ((l : O) ^ m)
  have hb : ∀ (r : ℤ) T, (IdF.span (sP (TO q l s {W})).A ((l : O) ^ m)).S T ≤ (b r).S T := fun r T => le_sup_right
  have key := hLoc M (polyC _ PL) PO E E' e' he b hb s (polyC_crit _ PL 0 (hPL 0).2.1)
    (fun r hr => (hPO r hr).2 _) (fun r' h1 h2 => by
      have hr1 : 1 ≤ r' := by omega
      have hle : (b r').S E'.D ≤ (IdF.span (sP (TO q l s {W})).A ((l : O) ^ m)).S E'.D := by
        refine sup_le ?_ le_rfl
        have : cO.D.pdPow r'.toNat = ⊥ := dividedPowerFiltration_bot _ (by rw [cO.J_eq]; exact Ideal.map_bot) (by omega)
        exact this.le.trans bot_le
      exact (o_bij h _ m hQ _ hP (b r') (hb r') E'.D hle).comp hσb) j
  have hb' : ∀ T, (stdI (TO q l s {W}) none ((l : O) ^ m)).S T = (b s).S T := by
    intro T
    have : T.obj.pdPow (s : ℤ).toNat = ⊥ := by
      have := T.property.1.1
      simpa using this
    change (⊥ : Ideal T.obj.B) ⊔ _ = T.obj.pdPow (s : ℤ).toNat ⊔ _
    rw [this]
  have hB := sqLe_bij (a := IdF.top (sP (TO q l s {W})).A) (a' := IdF.top (sP (TO q l s {W})).A) (fun _ => rfl) hb' j
  refine (Function.Bijective.of_comp_iff' hB _).1 ?_
  have e2 : ⇑((sqLe (a := IdF.top (sP (TO q l s {W})).A) (a' := IdF.top (sP (TO q l s {W})).A) (fun _ => le_rfl)
      (fun T => (hb' T).le)).pull j) ∘ ⇑((gP h (TO q l s {W}) m hQ (St ⊤ {W}) hP).pull j) =
      ⇑((M.o (b s) (hb s)).pull j) :=
    funext fun x => (gQ_o h _ m hQ _ hP (b s) (hb s) (fun T => (hb' T).le) j x).symm
  rw [e2]
  exact key
end Loc

section Nest
variable {D : Type 1} [Category.{0} D]

abbrev nestF {P P₂ : ObjectProperty D} {Pn : ObjectProperty P.FullSubcategory}
    (h₁ : ∀ T, P₂ T → ∃ hp : P T, Pn ⟨T, hp⟩) : P₂.FullSubcategory ⥤ Pn.FullSubcategory :=
  Pn.lift (P.lift P₂.ι fun T => (h₁ _ T.property).1) fun T => (h₁ _ T.property).2

def nestAdj {P P₂ : ObjectProperty D} {Pn : ObjectProperty P.FullSubcategory}
    (h₁ : ∀ T, P₂ T → ∃ hp : P T, Pn ⟨T, hp⟩) (h₂ : ∀ T : Pn.FullSubcategory, P₂ T.obj.obj) :
    nestF h₁ ⊣ (P₂.lift (Pn.ι ⋙ P.ι) h₂) :=
  (CategoryTheory.Equivalence.mk (nestF h₁)
    (P₂.lift (Pn.ι ⋙ P.ι) h₂) (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))).toAdjunction

end Nest

theorem mem_biInf {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (x : X) :
    x ∈ (⨅ α ∈ S, U α) ↔ ∀ α ∈ S, x ∈ U α := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.iInf_insert]
    simp [ih]

section St
variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU ⊤ T := fun _ _ => trivial

theorem st_inf (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (U : Cov q) (S : Finset U.ι) (hS : S.Nonempty)
    (T : Thick (nlFun γ p X q κ)) :
    St Q {⨅ α ∈ S, U.U α} T ↔ St Q (Set.range U.U) T ∧ ∀ α ∈ S, InU (U.U α) T := by
  constructor
  · rintro ⟨h1, V, rfl, hV⟩
    have h2 : ∀ α ∈ S, InU (U.U α) T := fun α hα x hx =>
      ((mem_biInf U.U S _).1 (hV hx)) α hα
    obtain ⟨α, hα⟩ := hS
    exact ⟨⟨h1, U.U α, ⟨α, rfl⟩, h2 α hα⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, _, rfl, fun x hx => (mem_biInf U.U S _).2 fun α hα => h2 α hα hx⟩

end St

section Top
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

def scM (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) (Q : ObjectProperty (Thick (Lm h q m))) :
    CH.Mor (Q.ι ⋙ OMm h q m) (CH.modF (sP Q).A) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ m})) where
  G := 𝟭 _
  τ T := { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem scM_bij (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) (Q : ObjectProperty (Thick (Lm h q m))) (j : ℕ) :
    Function.Bijective ((scM h q m Q).pull j) :=
  idM_bij (scM h q m Q).τ (scM h q m Q).nat (fun _ => Function.bijective_id) j

theorem top_L (hZ : DH.Zar2) (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱).ι).pull j) := by
  have hle : St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱 ≤ ⊤ := fun _ _ => trivial
  have z := (hZ (Q₀ := ⊤) (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inl rfl⟩) 𝒱 ⊤ hle
    (fun T _ => ⟨trivial, _, rfl, by rw [hU]; exact inU_top T⟩) (fun _ _ _ _ _ => trivial) j).2.2
  have r1 : Function.Bijective ((CH.Mor.restrict (OMm h q m) (⊤ : ObjectProperty (Thick (Lm h q m))).ι).pull j) :=
    CrystallineSemistableComparison.P.mapH_bij _ (GlobalTheory.CompanionTheory.CosieveBC.restrict_bij _ (fun _ => trivial)) j
  have c1 := scM_bij h q m ⊤ j
  have c2 := scM_bij h q m (St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱) j
  refine (Function.Bijective.of_comp_iff' c2 _).1 ?_
  have e : ⇑((scM h q m (St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱)).pull j) ∘
      ⇑((CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱).ι).pull j) =
      ⇑((incl hle).o.pull j) ∘ ⇑((scM h q m ⊤).pull j) ∘ ⇑((CH.Mor.restrict (OMm h q m) (⊤ : ObjectProperty (Thick (Lm h q m))).ι).pull j) := by
    funext x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  rw [e]
  exact z.comp (c1.comp r1)

def resO {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (hle : Q' ≤ Q) (c : b.R) :
    CH.Mor (sq (IdF.top (sP Q).A) (stdI Q none c)) (sq (IdF.top (sP Q').A) (stdI Q' none c)) (RingHom.id _) :=
  (incl hle).sq (fun _ _ _ => trivial) (incl_std hle none c)

theorem std0 {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (T : Q.FullSubcategory) :
    (IdF.top (sP Q).A).S T = (stdI Q (some 0) 0).S T := by
  have : (sFil Q 0).S T = ⊤ := T.obj.pdPow_zero
  exact (top_le_iff.1 (this.ge.trans le_sup_left)).symm

theorem top_O (hZ : DH.Zar2) (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤) (hle : TO q l s 𝒱 ≤ TO q l s {⊤})
    (c : O) (j : ℕ) : Function.Bijective ((resO hle c).pull j) := by
  have z := (hZ (Q₀ := TF l s) (Or.inl ⟨rfl, l, s, rfl⟩) 𝒱 (TO q l s {⊤}) hle
    (fun T hT => ⟨hT.1, _, rfl, by rw [hU]; exact inU_top T⟩)
    (fun _ T' _ _ hT' => ⟨hT', ⊤, rfl, inU_top T'⟩) j).2.1 (some 0) none 0 c
  have t0 := sqLe_bij (b := stdI (TO q l s {⊤}) none c) (b' := stdI (TO q l s {⊤}) none c) (std0 (TO q l s {⊤})) (fun _ => rfl) j
  have t1 := sqLe_bij (b := stdI (TO q l s 𝒱) none c) (b' := stdI (TO q l s 𝒱) none c) (std0 (TO q l s 𝒱)) (fun _ => rfl) j
  refine (Function.Bijective.of_comp_iff' t1 _).1 ?_
  have e : ⇑((sqLe (a := IdF.top (sP (TO q l s 𝒱)).A) (b := stdI (TO q l s 𝒱) none c) (a' := stdI (TO q l s 𝒱) (some 0) 0) (b' := stdI (TO q l s 𝒱) none c) (fun T => (std0 (TO q l s 𝒱) T).le) (fun _ => le_rfl)).pull j) ∘
      ⇑((resO hle c).pull j) = ⇑(((incl hle).sq (incl_std hle (some 0) 0) (incl_std hle none c)).pull j) ∘
      ⇑((sqLe (a := IdF.top (sP (TO q l s {⊤})).A) (b := stdI (TO q l s {⊤}) none c) (a' := stdI (TO q l s {⊤}) (some 0) 0) (b' := stdI (TO q l s {⊤}) none c) (fun T => (std0 (TO q l s {⊤}) T).le) (fun _ => le_rfl)).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) (resO hle c) (sqLe (a := IdF.top (sP (TO q l s 𝒱)).A) (b := stdI (TO q l s 𝒱) none c) (a' := stdI (TO q l s 𝒱) (some 0) 0) (b' := stdI (TO q l s 𝒱) none c) (fun T => (std0 (TO q l s 𝒱) T).le) (fun _ => le_rfl)) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) (sqLe (a := IdF.top (sP (TO q l s {⊤})).A) (b := stdI (TO q l s {⊤}) none c) (a' := stdI (TO q l s {⊤}) (some 0) 0) (b' := stdI (TO q l s {⊤}) none c) (fun T => (std0 (TO q l s {⊤}) T).le) (fun _ => le_rfl)) ((incl hle).sq (incl_std hle (some 0) 0) (incl_std hle none c)) j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id O) _ _ (𝟙 _) (fun T y => ?_) j x
    obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  rw [e]
  exact z.comp t0

end Top

section Glue
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

set_option maxHeartbeats 1000000 in
theorem glue (h : OL l O) (U : Cov q) (s m : ℕ) (hQ : ∀ (𝒱 : Set X.Opens) T, TO q l s 𝒱 T → Good (l := l) T m)
    (hP : ∀ (𝒱 : Set X.Opens) T, St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱 ((GF h (TO q l s 𝒱) m (hQ 𝒱)).obj T))
    (hloc : ∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective
      ((gP h (TO q l s {⨅ α ∈ S, U.U α}) m (hQ _) (St ⊤ {⨅ α ∈ S, U.U α}) (hP _)).pull j)) (j : ℕ) :
    Function.Bijective ((gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _)).pull j) := by
  refine cover_bij (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _))
    (fun α T => InU (U.U α) T.obj) (fun α T => InU (U.U α) T.obj) (fun α T T' φ hT => Site.inU_hom φ.hom hT)
    (fun α T T' φ hT => Site.inU_hom φ.hom hT) (fun T => ?_) (fun T => ?_) (fun α T hT => inU_G h T.obj m _ hT)
    (fun S hS j => ?_) j
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  have h₁L : ∀ T, St (⊤ : ObjectProperty (Thick (Lm h q m))) {⨅ α ∈ S, U.U α} T →
      ∃ hp : St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U) T,
        capS (fun α (T : (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have h₁O : ∀ T, TO q l s {⨅ α ∈ S, U.U α} T → ∃ hp : TO q l s (Set.range U.U) T,
        capS (fun α (T : (TO q l s (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have aL := nestAdj h₁L (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  have aO := nestAdj h₁O (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  let rL : CH.Mor ((capS (fun α (T : (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).ι ⋙ OMm h q m)
      ((St (⊤ : ObjectProperty (Thick (Lm h q m))) {⨅ α ∈ S, U.U α}).ι ⋙ OMm h q m) (RingHom.id O) :=
    CH.Mor.restrict _ (nestF h₁L)
  let rO : CH.Mor ((capS (fun α (T : (TO q l s (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      sq (IdF.top (sP (TO q l s (Set.range U.U))).A) (stdI (TO q l s (Set.range U.U)) none ((l : O) ^ m)))
      (sq (IdF.top (sP (TO q l s {⨅ α ∈ S, U.U α})).A) (stdI (TO q l s {⨅ α ∈ S, U.U α}) none ((l : O) ^ m))) (RingHom.id O) :=
    CH.Mor.restrict _ (nestF h₁O)
  have bL : Function.Bijective (rL.pull j) := CrystallineSemistableComparison.P.adj _ _ _ aL j
  have bO : Function.Bijective (rO.pull j) := CrystallineSemistableComparison.P.adj _ _ _ aO j
  refine (Function.Bijective.of_comp_iff' bO _).1 ?_
  have e : ∀ x, rO.pull j ((morU (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => inU_G h T.obj m _ (hT α hα)).pull j x) =
      (gP h (TO q l s {⨅ α ∈ S, U.U α}) m (hQ _) (St ⊤ {⨅ α ∈ S, U.U α}) (hP _)).pull j (rL.pull j x) := by
    intro x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) _ rO j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) rL _ j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id O) _ _ (𝟙 _) (fun T y => ?_) j x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  have e2 := funext e
  refine (show Function.Bijective (fun x => rO.pull j ((morU (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => inU_G h T.obj m _ (hT α hα)).pull j x)) from ?_)
  rw [e2]
  exact (hloc S hS j).comp bL

end Glue

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (h : OL l O) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (U : Cov q) (s : ℕ) (hs : ∀ α, U.d α < s) (m : ℕ) (hG : ∀ T, TO q l s {⊤} T → Good (l := l) T m) (j : ℕ), DH.LocCmpq → DH.Zar2 → DH.PolyAll → KH.PolyTf → DH.ChartAlg → DH.ChartP → DH.ChartGood → DH.ChartGrConst → DH.IsFilS → KH.GlobBcSt → Function.Bijective ((gMor h (TO q l s {⊤}) m hG).pull j) := by
  intro l _ O _ h X q U s hs m hG j hLoc hZ hPA hPT hCA hCP hCG _ _ _
  have hUs : sSup (Set.range U.U) = ⊤ := by
    rw [sSup_range]
    exact U.cover
  have htop : ∀ 𝒱 : Set X.Opens, TO q l s 𝒱 ≤ TO q l s {⊤} := fun 𝒱 T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩
  have hQ : ∀ (𝒱 : Set X.Opens) T, TO q l s 𝒱 T → Good (l := l) T m := fun 𝒱 T hT => hG T (htop 𝒱 T hT)
  have hP : ∀ (𝒱 : Set X.Opens) T, St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱 ((GF h (TO q l s 𝒱) m (hQ 𝒱)).obj T) := fun 𝒱 T => by
    obtain ⟨-, V, hV, hin⟩ := T.property
    exact ⟨trivial, V, hV, inU_G h T.obj m _ hin⟩
  have g := glue h U s m hQ hP (fun S hS j => by
    obtain ⟨α, hα⟩ := hS
    obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S, U.U α) ≤ U.U α) (U.inter S ⟨α, hα⟩)
    exact local_bij hLoc hPA hPT hCA hCP hCG h c' s (hs α) m _ _ j) j
  have tL := top_L hZ h q m _ hUs j
  have tO := top_O hZ q l s _ hUs (htop _) ((l : O) ^ m) j
  refine (Function.Bijective.of_comp_iff' tO _).1 ?_
  have e : ⇑((resO (htop (Set.range U.U)) ((l : O) ^ m)).pull j) ∘ ⇑((gMor h (TO q l s {⊤}) m hG).pull j) =
      ⇑((gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _)).pull j) ∘
      ⇑((CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).ι).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) (gMor h (TO q l s {⊤}) m hG) (resO (htop (Set.range U.U)) ((l : O) ^ m)) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) (CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).ι)
        (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _)) j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id O) (CH.Mor.comp (σ'' := RingHom.id O) (gMor h (TO q l s {⊤}) m hG) (resO (htop (Set.range U.U)) ((l : O) ^ m)))
      (CH.Mor.comp (σ'' := RingHom.id O) (CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).ι)
        (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _))) (𝟙 _) (fun T y => ?_) j x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  rw [e]
  exact g.comp tL

end GlobalTheory.CompanionTheory.DisoHm
end
end
