import Development.EtaleCohomology.TateTwists.EtaleShortComplexExactIffLocallySurjectiveOnKern

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem stair_loc_bind (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hSP⟩ := hP
  refine ⟨Sieve.bind S.arrows (fun V g hg => Classical.choose (h V g (hSP V g hg))), ?_, ?_⟩
  · exact (Scheme.etaleTopology).bind_covering hS (fun V g hg => (Classical.choose_spec (h V g (hSP V g hg))).1)
  · rintro W f ⟨V, k, g, hg, hk, rfl⟩
    exact (Classical.choose_spec (h V g (hSP V g hg))).2 W k hk

theorem stair_loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem stair_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.map φ (Sec.res g y) = Sec.res g (Sec.map φ y) := by
  have := congrArg (fun m => (ModuleCat.Hom.hom m) y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem stair_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y := by
  simp [Sec.res]

def EtaleTensorCyclesLocallyLiftOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    ∀ (w : ℤ) (U : Scheme.{0}) (x : Tens C J U w), Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ z : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z = Sec.res g (τ.lift U w x)

theorem etale_tensor_complex_locally_exact_of_lifted_sections (hL : EtaleTensorCyclesLocallyLiftOfFlatBounded) : EtaleTensorComplexLocallyExactOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC w U y hy
  refine stair_loc_bind U _ _ (hτ.1 U w y) ?_
  rintro V g ⟨x, hx⟩
  have hcyc : Sec.map (T.sc w).g (τ.lift V w x) = 0 := by
    have h1 := stair_map_res (T.sc w).g g y
    have h2 : Sec.map (T.sc w).g (τ.lift V w x) = Sec.map (T.sc w).g (Sec.res g y) := congrArg _ hx
    refine h2.trans (h1.trans ?_)
    rw [hy]
    simp
  refine stair_loc_mono V _ _ (hL R a b τ hτ hJ hC w V x hcyc) ?_
  rintro W k ⟨z, hz⟩
  refine ⟨z, ?_⟩
  exact hz.trans ((congrArg (Sec.res k) hx).trans (stair_res_res k g y))

end LateralTheory.EtaleFoundations
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleFoundations

theorem stair_tens_top {R : Type} [CommRing R] {C J : Cx R} {U : Scheme.{0}} {w : ℤ} (x : Tens C J U w) :
    ∃ s : ℤ, ∀ p, s < p.1.1 → x p = 0 := by
  classical
  refine ⟨((DFinsupp.support x).sup fun p => p.1.1.toNat : ℕ), fun p hp => ?_⟩
  by_contra h
  have hm : p ∈ DFinsupp.support x := (DFinsupp.mem_support_iff).2 h
  have h1 : p.1.1.toNat ≤ (DFinsupp.support x).sup fun p => p.1.1.toNat := Finset.le_sup (f := fun p => p.1.1.toNat) hm
  have h2 : p.1.1 ≤ (p.1.1.toNat : ℤ) := Int.self_le_toNat _
  have h3 : ((p.1.1.toNat : ℕ) : ℤ) ≤ (((DFinsupp.support x).sup fun p => p.1.1.toNat : ℕ) : ℤ) := by exact_mod_cast h1
  omega

theorem stair_loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem stair_sec_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) (U : Scheme.{0}) (y : Sec F U) : y = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have := congrArg (fun m : F ⟶ F => (m.hom.app (op U)).hom y) h
  simpa using this

theorem stair_tens_low {R : Type} [CommRing R] {C J : Cx R} (a : ℤ) [C.IsStrictlyGE a] {U : Scheme.{0}} {w : ℤ}
    (x : Tens C J U w) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (hp : p.1.1 < a) : x p = 0 := by
  have hz := C.isZero_of_isStrictlyGE a p.1.1 hp
  have key : ∀ y : Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U, y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rfl
    | tmul u v => rw [stair_sec_zero hz U u, TensorProduct.zero_tmul]
    | add u v hu hv => rw [hu, hv, add_zero]
  exact key _

theorem stair_fg_zero {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {V : Scheme.{0}} (z : Sec (T.sc w).X₁ V) :
    Sec.map (T.sc w).g (Sec.map (T.sc w).f z) = 0 := by
  have h1 : Sec.map (T.sc w).g (Sec.map (T.sc w).f z) = ((((T.sc w).f ≫ (T.sc w).g).hom.app (op V)).hom z) := rfl
  rw [h1, (T.sc w).zero]
  rfl

def stair_row (R : Type) [CommRing R] (C J : Cx R) : Prop :=
  ∀ (s t : ℤ) (V : Scheme.{0}) (x : Sec (C.X s) V ⊗[ULift.{1} R] Sec (J.X t) V),
    TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id x = 0 →
    Loc V fun W k => ∃ z : Sec (C.X (s - 1)) W ⊗[ULift.{1} R] Sec (J.X t) W,
      TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id z =
        TensorProduct.map ((C.X s).obj.map k.op).hom ((J.X t).obj.map k.op).hom x

def EtaleTensorWithFlatPreservesLocalExactness : Prop :=
  ∀ (R : Type) [CommRing R] {C J : Cx R}, (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    stair_row R C J

def EtaleTensorCycleLocallyLowersTopDegree : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (τ : Pair C J T), τ.IsTensor → stair_row R C J →
    ∀ (w s : ℤ) (U : Scheme.{0}) (x : Tens C J U w), (∀ p, s < p.1.1 → x p = 0) →
      Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ x' : Tens C J V w, (∀ p, s - 1 < p.1.1 → x' p = 0) ∧
        ∃ z : Sec (T.sc w).X₁ V, τ.lift V w x' = Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)

theorem etale_tensor_cycles_locally_lift_of_row_exact_and_descent (hA : EtaleTensorWithFlatPreservesLocalExactness)
    (hS : EtaleTensorCycleLocallyLowersTopDegree) : EtaleTensorCyclesLocallyLiftOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC
  have hrow := hA R hJ hC
  have key : ∀ n : ℕ, ∀ (w : ℤ) (U : Scheme.{0}) (x : Tens C J U w), (∀ p, a - 1 + n < p.1.1 → x p = 0) →
      Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ z : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z = Sec.res g (τ.lift U w x) := by
    intro n
    induction n with
    | zero =>
      intro w U x hx _
      have h0 : x = 0 := by
        ext p
        by_cases hp : p.1.1 < a
        · simpa using stair_tens_low a x p hp
        · simpa using hx p (by push_cast; omega)
      refine stair_loc_top _ _ fun V g => ⟨0, ?_⟩
      simp [h0] <;> rfl
    | succ n ih =>
      intro w U x hx hc
      refine stair_loc_bind U _ _ (hS R τ hτ hrow w (a - 1 + (n + 1 : ℕ)) U x hx hc) ?_
      rintro V g ⟨x', hx', z, hz⟩
      have hc' : Sec.map (T.sc w).g (τ.lift V w x') = 0 := by
        rw [hz]
        have e1 : Sec.map (T.sc w).g (Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)) =
            Sec.map (T.sc w).g (Sec.res g (τ.lift U w x)) - Sec.map (T.sc w).g (Sec.map (T.sc w).f z) := by
          exact map_sub _ _ _
        rw [e1, stair_fg_zero, sub_zero]
        exact (stair_map_res (T.sc w).g g (τ.lift U w x)).trans ((congrArg (Sec.res g) hc).trans (map_zero _))
      refine stair_loc_mono V _ _ (ih w V x' (fun p hp => hx' p (by push_cast at hp ⊢; omega)) hc') ?_
      rintro W k ⟨z', hz'⟩
      refine ⟨z' + Sec.res k z, ?_⟩
      have e2 : Sec.map (T.sc w).f (z' + Sec.res k z) = Sec.map (T.sc w).f z' + Sec.map (T.sc w).f (Sec.res k z) := by
        simp only [Sec.map, map_add]
      have e3 : Sec.res k (Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)) =
          Sec.res k (Sec.res g (τ.lift U w x)) - Sec.res k (show Sec (T.X w) V from Sec.map (T.sc w).f z) := by
        exact map_sub _ _ _
      rw [e2, hz', hz, e3, stair_map_res, stair_res_res]
      exact sub_add_cancel _ _
  intro w U x hx
  obtain ⟨s, hs⟩ := stair_tens_top x
  exact key (s - (a - 1)).toNat w U x (fun p hp => hs p (by omega)) hx

end LateralTheory.EtaleFoundations
end
