import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalGlobalStatement
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMap
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.OSplitBig

def sysPol (D : D7) (c : PlE D.host → ℕ → ℂ) (w : PlE D.host) : ℂ[X] :=
  X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
    C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c w k) * X ^ (D.R.nV - k)

def frobSet (D : D7) (F : Finset (PlE D.host)) : Set (G D.host.E D.nd.Om) :=
  {σ | ∃ w : PlE D.host, w ∉ F ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ}

theorem dense_frobSet (D : D7) (h : GlobalTheory.RowTie.ChebSplit D.nd) (F : Finset (PlE D.host)) :
    Dense (frobSet D F) := h F

theorem heckePol_map (D : D7) (L : LocAll (lay0 D)) (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i) (v : PlE D.host)
    (hv : SplitOut (withLoc L).nd i v) :
    (heckePol (withLoc L).nd i x v).map (iotaOC (withLoc L) i) =
      sysPol D (GlobalTheory.CoefDuty.ptSys (withLoc L) i x) v := by
  have hS := hv
  obtain ⟨hsp, hl, hSi, hQ⟩ := hv
  have hgen : ∀ k ∈ Finset.Icc 1 D.R.nV,
      GenAt (withLoc L) ((withLoc L).nd.l i) ((withLoc L).nd.Q i) v k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    refine ⟨hsp, hl, ?_, hQ, hk1, hk2⟩
    intro hmem
    exact hSi (((withLoc L).nd.S_def i v).2 hmem)
  simp only [heckePol, sysPol, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [GlobalTheory.CoefDuty.ptSys, if_pos (hgen k hk), map_mul, map_pow, map_neg, map_one, map_natCast]
  rfl

end GlobalTheory.OSplitBig

end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PlacesExc

theorem finite_exceptional : ∀ (D : D7) (l : ℕ), l.Prime → ∃ F : Finset (PlE D.host), ∀ v, v ∉ F → v ∉ placesOver D.host.E l ∧ v ∉ placesS D l := by
  intro D l hl
  have h1 : (placesOver D.host.E l).Finite := Formalism.L2.Fam.NPC.placesOver_fin D.host l hl
  have h2 : (placesS D l).Finite := Formalism.L2.Fam.NPC.exceptional_places_finite D.host l
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset] at hv
  exact ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h)⟩

end GlobalTheory.PlacesExc
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_exceptional_places_over_prime : ∀ (D : D7) (l : ℕ), l.Prime → ∃ F : Finset (PlE D.host), ∀ v, v ∉ F → v ∉ placesOver D.host.E l ∧ v ∉ placesS D l := by
  atlas_forward_decl GlobalTheory.PlacesExc.finite_exceptional
end

section
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem matrix_system_nonzero_solution_descends {k L Γ : Type} [Field k] [Field L] (f : k →+* L)
    {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k)
    (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L) :
    C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 →
      ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  intro hC hAB hQ
  letI := f.toAlgebra
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hC (Matrix.ext h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k L, φ (C i₀ j₀) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hij ((Module.forall_dual_apply_eq_zero_iff k (C i₀ j₀)).mp h)
  have key : ∀ (x : k) (y : L), φ (f x * y) = x * φ y := by
    intro x y
    have h1 : f x * y = x • y := (Algebra.smul_def x y).symm
    rw [h1, map_smul, smul_eq_mul]
  have key' : ∀ (x : k) (y : L), φ (y * f x) = φ y * x := by
    intro x y
    rw [mul_comm y, key, mul_comm]
  refine ⟨C.map φ, ?_, ?_, ?_⟩
  · intro h
    apply hφ
    have := congrFun (congrFun h i₀) j₀
    simpa using this
  · intro g
    ext i j
    have := congrArg φ (congrFun (congrFun (hAB g) i) j)
    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, key'] using this
  · ext i j
    have := congrArg φ (congrFun (congrFun hQ i) j)
    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, Matrix.zero_apply, map_zero]
      using this

end GlobalTheory
end

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_intertwiner_of_map : ∀ {k L Γ : Type} [Field k] [Field L] (f : k →+* L) {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k) (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L), C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 → ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  atlas_forward_decl GlobalTheory.matrix_system_nonzero_solution_descends
end

section
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.SplitCrit

variable {k L : Type} [Field k] [Field L]

abbrev ext (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) : Submodule L (Fin a → L) :=
  Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))

theorem map_mulVec_comp (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) (v : Fin n → k) :
    (M.map f).mulVec (f ∘ v) = f ∘ M.mulVec v := by
  funext i; exact (RingHom.map_mulVec f M v i).symm

theorem ext_le_comap (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k)
    (U : Submodule k (Fin n → k)) (U' : Submodule k (Fin m → k)) (h : ∀ v ∈ U, M.mulVec v ∈ U') :
    ext f U ≤ (ext f U').comap (M.map f).mulVecLin := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
  rw [map_mulVec_comp]
  exact Submodule.subset_span ⟨_, h v hv, rfl⟩

theorem ext_ne_bot (f : k →+* L) {a : ℕ} {W : Submodule k (Fin a → k)} (hW : W ≠ ⊥) : ext f W ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro h
  have : f ∘ v ∈ ext f W := Submodule.subset_span ⟨v, hv, rfl⟩
  rw [h, Submodule.mem_bot] at this
  apply hv0; funext i
  have := congrFun this i
  simpa using this

theorem finrank_ext_le (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) :
    Module.finrank L (ext f W) ≤ Module.finrank k W := by
  let e := Module.finBasis k W
  have hle : ext f W ≤ Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v = ∑ i, (e.repr ⟨v, hv⟩ i) • (e i : Fin a → k) := by
      have := congrArg Subtype.val (e.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have : f ∘ v = ∑ i, f (e.repr ⟨v, hv⟩ i) • (f ∘ (e i : Fin a → k)) := by
      conv_lhs => rw [hv']
      funext j
      simp [Finset.sum_apply, map_sum]
    show f ∘ v ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc Module.finrank L (ext f W)
      ≤ Module.finrank L (Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank k W)) := finrank_range_le_card _
    _ = Module.finrank k W := Fintype.card_fin _

theorem range_ne_bot {K : Type} [Field K] {m n : ℕ} {X : Matrix (Fin m) (Fin n) K} (hX : X ≠ 0) :
    LinearMap.range X.mulVecLin ≠ ⊥ := by
  intro h
  apply hX
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have : X.mulVecLin (Pi.single i 1) ∈ LinearMap.range X.mulVecLin := LinearMap.mem_range_self _ _
  rw [h, Submodule.mem_bot, Matrix.mulVecLin_apply] at this
  rw [this, Matrix.zero_mulVec]

end GlobalTheory.SplitCrit

namespace GlobalTheory.SplitCrit

theorem splitRep_of_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  intro k Γ L _ _ _ _ f a ρ hmod W hW
  obtain ⟨hW0, hWi, hWmin⟩ := hW

  have hLi : IsInv (mapRep f ρ) (ext f W) := fun g v hv =>
    ext_le_comap f (ρ g : Matrix (Fin a) (Fin a) k) W W (hWi g) hv
  obtain ⟨V, hVle, hV⟩ := GlobalTheory.SemisimpleDecomp.exists_irr_le hLi (ext_ne_bot f hW0)
  obtain ⟨b, σ, C, hCinj, hCr, hCint⟩ := hmod V hV

  obtain ⟨W', hc⟩ := Submodule.exists_isCompl W
  let φ : (Fin a → k) →ₗ[k] (Fin a → k) := W'.subtype.comp (W'.projectionOnto W hc.symm)
  have hφ : ∀ v, φ v = 0 ↔ v ∈ W := by
    intro v
    have hk := Submodule.ker_projectionOnto hc.symm
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, ZeroMemClass.coe_eq_zero]
    rw [← LinearMap.mem_ker, hk]
  let Q := LinearMap.toMatrix' φ
  have hQ : ∀ v, Q.mulVec v = 0 ↔ v ∈ W := fun v => by
    simp only [Q, LinearMap.toMatrix'_mulVec]; exact hφ v

  have hQL : ext f W ≤ LinearMap.ker (Q.map f).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [map_mulVec_comp, (hQ v).2 hv]
    funext i; simp
  have hQC : Q.map f * C = 0 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    have : C.mulVec (Pi.single j 1) ∈ V := hCr ▸ LinearMap.mem_range_self C.mulVecLin _
    have := hQL (hVle this)
    simpa using this
  have hC0 : C ≠ 0 := by
    intro h; apply hV.1; rw [← hCr, h]
    ext x; simp
  have hint : ∀ g, ((ρ g : Matrix (Fin a) (Fin a) k)).map f * C = C * ((σ g : Matrix (Fin b) (Fin b) k)).map f :=
    fun g => hCint g
  obtain ⟨X, hX0, hXint, hQX⟩ := GlobalTheory.T.exists_ne_zero_intertwiner_of_map f (fun g => (ρ g : Matrix (Fin a) (Fin a) k))
    (fun g => (σ g : Matrix (Fin b) (Fin b) k)) Q C hC0 hint hQC

  have hXW : LinearMap.range X.mulVecLin ≤ W := by
    rintro _ ⟨w, rfl⟩
    rw [← hQ, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQX, Matrix.zero_mulVec]
  have hXi : IsInv ρ (LinearMap.range X.mulVecLin) := by
    rintro g _ ⟨w, rfl⟩
    refine ⟨(σ g : Matrix (Fin b) (Fin b) k).mulVec w, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hXint g]
  have hXeq : LinearMap.range X.mulVecLin = W :=
    (hWmin _ hXW hXi).resolve_left (range_ne_bot hX0)
  have hWb : Module.finrank k W ≤ b := by
    rw [← hXeq]
    exact (LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun k).le
  have hVb : Module.finrank L V = b := by
    rw [← hCr, LinearMap.finrank_range_of_inj hCinj, Module.finrank_fin_fun]
  have hVeq : V = ext f W :=
    Submodule.eq_of_le_of_finrank_le hVle ((finrank_ext_le f W).trans (hWb.trans hVb.ge))
  have hV' : IsIrrSub (mapRep f ρ) (ext f W) := hVeq ▸ hV
  exact GlobalTheory.T.absIrrSub_of_isIrrSub_span_map f ρ W hWi hV'

end GlobalTheory.SplitCrit
end

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbsolutelyIrreducibleSplitRep_of_constituent_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  atlas_forward_decl GlobalTheory.SplitCrit.splitRep_of_models
end

section
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.ConstituentImage

theorem exists_constituent_image : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ τ₀ : Γ →* GL (Fin a) L) (P : GL (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (P : Matrix (Fin a) (Fin a) L) = (P : Matrix (Fin a) (Fin a) L) * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) → IsSSRep τ → ∀ (Vs : Fin n → Submodule L (Fin a → L)), iSup Vs = ⊤ → (∀ j, IsIrrSub τ₀ (Vs j)) → ∀ V, IsIrrSub τ V → ∃ (j : Fin n) (M : Matrix (Fin a) (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * M = M * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) ∧ Submodule.map M.mulVecLin (Vs j) = V ∧ Disjoint (LinearMap.ker M.mulVecLin) (Vs j) := by
  intro Γ L _ _ a n τ τ₀ P hP hss Vs hVs hirr V hV
  obtain ⟨W', hW'i, hc⟩ := hss V hV.2.1
  set p : (Fin a → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ Submodule.linearProjOfIsCompl V W' hc with hpdef
  have hpV : ∀ x, p x ∈ V := fun x => (Submodule.linearProjOfIsCompl V W' hc x).2
  have hpid : ∀ x ∈ V, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩)
  have hp0 : ∀ x ∈ W', p x = 0 := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨x, hx⟩)
  have hcomm : ∀ g v, p ((τ g : Matrix (Fin a) (Fin a) L).mulVec v) = (τ g : Matrix (Fin a) (Fin a) L).mulVec (p v) := by
    intro g v
    set q := v - p v
    have hq : q ∈ W' := by
      rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc, map_sub]
      have := Submodule.linearProjOfIsCompl_apply_left hc ⟨p v, hpV v⟩
      rw [this, sub_eq_zero]; rfl
    have hv : v = p v + q := by simp [q]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_add, map_add, hpid _ (hV.2.1 g _ (hpV v)), hp0 _ (hW'i g _ hq), add_zero]
  set π : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' p with hπ
  have hπv : ∀ v, π.mulVec v = p v := fun v => by simp [hπ, LinearMap.toMatrix'_mulVec]
  have hπc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * π = π * (τ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hπv, hcomm]
  set M : Matrix (Fin a) (Fin a) L := π * (P : Matrix (Fin a) (Fin a) L) with hM
  have hMc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * M = M * (τ₀ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    rw [hM, ← Matrix.mul_assoc, hπc g, Matrix.mul_assoc, hP g, Matrix.mul_assoc]
  have hMv : ∀ g v, (τ g : Matrix (Fin a) (Fin a) L).mulVec (M.mulVec v) = M.mulVec ((τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v) := by
    intro g v
    rw [Matrix.mulVec_mulVec, hMc g, ← Matrix.mulVec_mulVec]
  have hMV : ∀ v, M.mulVec v ∈ V := fun v => by
    rw [hM, ← Matrix.mulVec_mulVec, hπv]; exact hpV _

  have hex : ∃ j, Submodule.map M.mulVecLin (Vs j) ≠ ⊥ := by
    by_contra hne
    push_neg at hne
    obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.1
    have hsup : Submodule.map M.mulVecLin ⊤ = ⊥ := by
      rw [← hVs, Submodule.map_iSup]; simp [hne]
    have hmem : M.mulVec (((P⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x) ∈ Submodule.map M.mulVecLin ⊤ :=
      ⟨_, Submodule.mem_top, rfl⟩
    rw [hsup, Submodule.mem_bot, hM, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := (P : Matrix (Fin a) (Fin a) L)),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, hπv, hpid x hxV] at hmem
    exact hx0 hmem
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, M, hMc, ?_, ?_⟩
  · have hinv : IsInv τ (Submodule.map M.mulVecLin (Vs j)) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨(τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v, (hirr j).2.1 g v hv, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact (hMv g v).symm
    have hle : Submodule.map M.mulVecLin (Vs j) ≤ V := by
      rintro _ ⟨v, _, rfl⟩; exact hMV v
    rcases hV.2.2 _ hle hinv with h | h
    · exact absurd h hj
    · exact h
  · have hinv : IsInv τ₀ (LinearMap.ker M.mulVecLin ⊓ Vs j) := by
      rintro g v ⟨hk, hv⟩
      refine ⟨?_, (hirr j).2.1 g v hv⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk ⊢
      rw [← hMv, hk, Matrix.mulVec_zero]
    rcases (hirr j).2.2 _ inf_le_right hinv with h | h
    · exact disjoint_iff.2 h
    · exfalso
      apply hj
      rw [eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      have hk : v ∈ LinearMap.ker M.mulVecLin := (h ▸ (inf_le_left : LinearMap.ker M.mulVecLin ⊓ Vs j ≤ _)) hv
      simpa using hk

end GlobalTheory.ConstituentImage
end

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_map_eq_of_irrSub : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ τ₀ : Γ →* GL (Fin a) L) (P : GL (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (P : Matrix (Fin a) (Fin a) L) = (P : Matrix (Fin a) (Fin a) L) * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) → IsSSRep τ → ∀ (Vs : Fin n → Submodule L (Fin a → L)), iSup Vs = ⊤ → (∀ j, IsIrrSub τ₀ (Vs j)) → ∀ V, IsIrrSub τ V → ∃ (j : Fin n) (M : Matrix (Fin a) (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * M = M * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) ∧ Submodule.map M.mulVecLin (Vs j) = V ∧ Disjoint (LinearMap.ker M.mulVecLin) (Vs j) := by
  atlas_forward_decl GlobalTheory.ConstituentImage.exists_constituent_image
end

section
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.StableSubMat

theorem exists_restrict {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (V : Submodule L (Fin a → L)) (hV : IsInv τ V) :
    ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L),
      D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧
      ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) =
          D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧
        ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
          E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  classical
  set b := Module.finrank L V
  let f : (Fin b → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ (Module.finBasis L V).equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp (Module.finBasis L V).equivFun.symm.injective
  have hfr : LinearMap.range f = V := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨g₀, hg₀⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  set E : Matrix (Fin a) (Fin b) L := LinearMap.toMatrix' f with hE
  set D : Matrix (Fin b) (Fin a) L := LinearMap.toMatrix' g₀ with hD
  have hEf : E.mulVecLin = f := by rw [hE]; exact Matrix.toLin'_toMatrix' f
  have hDf : D.mulVecLin = g₀ := by rw [hD]; exact Matrix.toLin'_toMatrix' g₀
  have hDE : D * E = 1 := by
    rw [hD, hE, ← LinearMap.toMatrix'_comp, hg₀, LinearMap.toMatrix'_id]
  have hrange : LinearMap.range E.mulVecLin = V := by rw [hEf, hfr]

  have hED : ∀ v ∈ V, (E * D).mulVec v = v := by
    intro v hv
    rw [← hfr] at hv
    obtain ⟨w, rfl⟩ := hv
    rw [← Matrix.mulVec_mulVec]
    have h1 : D.mulVec (f w) = g₀ (f w) := by rw [← hDf]; rfl
    have h2 : ∀ u, E.mulVec u = f u := fun u => by rw [← hEf]; rfl
    rw [h1, h2, ← LinearMap.comp_apply g₀ f, hg₀, LinearMap.id_apply]
  have key : ∀ g, E * D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
      ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E := by
    intro g
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mul_assoc (E * D), ← Matrix.mulVec_mulVec (M := E * D)]
    apply hED
    rw [← Matrix.mulVec_mulVec]
    apply hV
    rw [← hrange]
    exact ⟨x, rfl⟩
  let σm : Γ →* Matrix (Fin b) (Fin b) L :=
    { toFun := fun g => D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E
      map_one' := by simp [hDE]
      map_mul' := by
        intro g h
        simp only [map_mul, Units.val_mul]
        have k := key h
        simp only [Matrix.mul_assoc] at k ⊢
        rw [k] }
  refine ⟨b, E, D, σm.toHomUnits, hDE, hrange, fun g => ⟨?_, ?_⟩⟩
  · rw [MonoidHom.coe_toHomUnits]; rfl
  · rw [MonoidHom.coe_toHomUnits]
    change _ = E * (D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E)
    have k := key g
    simp only [Matrix.mul_assoc] at k ⊢
    exact k.symm

end GlobalTheory.StableSubMat
end

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep : ∀ {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (V : Submodule L (Fin a → L)), IsInv τ V → ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L), D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧ ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) = D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E = E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  atlas_forward_decl GlobalTheory.StableSubMat.exists_restrict
end

section
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

noncomputable section

namespace GlobalTheory.AdicCont

theorem norm_le_one_of_monic_root_ultra {K : Type} [NormedField K] [IsUltrametricDist K]
    (P : K[X]) (hm : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1) {y : K} (hy : P.eval y = 0) : ‖y‖ ≤ 1 := by
  by_contra h
  push_neg at h
  have hn : 0 < P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · exfalso
      have h1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm h0
      rw [h1, eval_one] at hy
      exact one_ne_zero hy
    · exact h0
  set n := P.natDegree with hndef
  have hsum := eval_eq_sum_range (p := P) y
  rw [Finset.sum_range_succ, ← hndef, hm.coeff_natDegree, one_mul, hy] at hsum
  have hyn : y ^ n = -∑ i ∈ Finset.range n, P.coeff i * y ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum.symm
  have hle : ‖∑ i ∈ Finset.range n, P.coeff i * y ^ i‖ ≤ ‖y‖ ^ (n - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.1 hi; omega
    calc ‖P.coeff i‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (n - 1) :=
          mul_le_mul (hc i) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = _ := one_mul _
  have h2 : ‖y‖ ^ n ≤ ‖y‖ ^ (n - 1) := by rw [← norm_pow, hyn, norm_neg]; exact hle
  have h3 : ‖y‖ ^ (n - 1) < ‖y‖ ^ n := pow_lt_pow_right₀ h (by omega)
  linarith

theorem continuous_adic (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    Continuous (fun x : O => iq (algebraMap O (FractionRing O) x)) := by
  set f : O →+* Qbar l := iq.comp (algebraMap O (FractionRing O)) with hf
  have hfz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hiq

  have h1 : ∀ x : O, ‖f x‖ ≤ 1 := by
    intro x
    obtain ⟨p, hpm, hpx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x
    let g : ℤ_[l] →+* Qbar l := f.comp (algebraMap ℤ_[l] O)
    refine norm_le_one_of_monic_root_ultra (p.map g) (hpm.map g) (fun i => ?_) ?_
    · rw [coeff_map]
      simp only [g, RingHom.comp_apply, hfz, PadicAlgCl.norm_extends]
      exact (p.coeff i).2
    · have := congrArg f hpx
      rw [hom_eval₂, map_zero] at this
      rw [eval_map]
      exact this

  have hlnorm : ‖f (l : O)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : O) ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hlnorm
    have : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hr : ‖f ϖ‖ < 1 := by
    have he : ϖ ^ e = ((u⁻¹ : Oˣ) : O) * (l : O) := by
      rw [hlu, ← mul_assoc, Units.inv_mul, one_mul]
    have hnorm : ‖f ϖ‖ ^ e ≤ (l : ℝ)⁻¹ := by
      rw [← norm_pow, ← map_pow, he, map_mul, norm_mul, hlnorm]
      calc ‖f ((u⁻¹ : Oˣ) : O)‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (h1 _) (by positivity)
        _ = _ := one_mul _
    have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    by_contra hge
    push_neg at hge
    have : 1 ≤ ‖f ϖ‖ ^ e := one_le_pow₀ hge
    linarith
  have hcont : ContinuousAt f 0 := by
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr
    have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hO).1 n
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
    rw [dist_zero_right]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    calc ‖f a‖ * ‖f ϖ‖ ^ n ≤ 1 * ‖f ϖ‖ ^ n := mul_le_mul_of_nonneg_right (h1 a) (by positivity)
      _ < ε := by rwa [one_mul]
  exact continuous_of_continuousAt_zero f hcont

end GlobalTheory.AdicCont

end
end

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_ringHom_finite_dvr_to_padicAlgClosure : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ iq : FractionRing O →+* Qbar l, (∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) → Continuous (fun x : O => iq (algebraMap O (FractionRing O) x)) := by
  atlas_forward_decl GlobalTheory.AdicCont.continuous_adic
end

section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_continuous_of_eq_on_dense : ∀ {X A : Type} [TopologicalSpace X] [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Infinite A] {n : ℕ} (M N : X → Matrix (Fin n) (Fin n) A), Continuous M → Continuous N → ∀ U : Set X, Dense U → (∀ x ∈ U, (M x).charpoly = (N x).charpoly) → ∀ x, (M x).charpoly = (N x).charpoly := by
  first | exact @GlobalTheory.charpoly_eq_of_eqOn_dense | exact GlobalTheory.charpoly_eq_of_eqOn_dense | (intros; apply GlobalTheory.charpoly_eq_of_eqOn_dense <;> assumption)
end

section
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem lift_rep_of_entries_in_image : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  intro k L Γ _ _ _ f b τ h
  choose pre hpre using h
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin b) (Fin b) k →+* Matrix (Fin b) (Fin b) L) :=
    Matrix.map_injective f.injective
  have key : ∀ g, f.mapMatrix (Matrix.of (pre g)) = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
    intro g; ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, hpre]
  let m : Γ →* Matrix (Fin b) (Fin b) k :=
    { toFun := fun g => Matrix.of (pre g)
      map_one' := hinj (by rw [key, map_one, map_one]; rfl)
      map_mul' := fun x y => hinj (by rw [map_mul, key, key, key, map_mul]; rfl) }
  refine ⟨MonoidHom.toHomUnits m, ?_⟩
  ext g i j
  simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  rw [MonoidHom.coe_toHomUnits]
  exact congrFun (congrFun (key g) i) j

end GlobalTheory
end

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_lift_of_entries_mem_range : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  atlas_forward_decl GlobalTheory.lift_rep_of_entries_in_image
end

section
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem image_finite_mem_subring (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  refine ⟨s.image (fun x => iq (algebraMap O (FractionRing O) x)), ?_⟩
  intro R hR hT x
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set O) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact hT (by simpa using Finset.mem_image_of_mem (fun x => iq (algebraMap O (FractionRing O) x)) hy)
  | zero => simpa using R.zero_mem
  | add a b _ _ ha hb => simpa using R.add_mem ha hb
  | smul c a _ ha =>
    rw [Algebra.smul_def, map_mul, map_mul, hiq]
    exact R.mul_mem (hR c) ha

end GlobalTheory
end

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_image_mem_subring : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l), (∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) → ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  atlas_forward_decl GlobalTheory.image_finite_mem_subring
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section
namespace GlobalTheory.OSplitCore

theorem mem_mul_of_mem {A : Type} [CommRing A] (R : Subring A) {m n q : ℕ} (X : Matrix (Fin m) (Fin n) A)
    (Y : Matrix (Fin n) (Fin q) A) (hX : ∀ i j, X i j ∈ R) (hY : ∀ i j, Y i j ∈ R) :
    ∀ i j, (X * Y) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => R.mul_mem (hX _ _) (hY _ _)

theorem coe_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f :=
  rfl

theorem mapped_props (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ}
    (U : Set Γ) (p : Γ → ℂ[X]) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hadic : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (r : Γ →* GL (Fin a) O) (hr : Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)))
    (hss : IsSSRep (mapRep (algebraMap O (FractionRing O)) r))
    (hp : ∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map
      (ι.toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) :
    IsSSRep (mapRep iq (mapRep (algebraMap O (FractionRing O)) r)) ∧
    Continuous (fun g => ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l))) ∧
    (∀ σ ∈ U, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) σ : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
      (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j,
      ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
        Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R := by
  have hcz : CharZero (FractionRing O) := ⟨fun m n h => by
    have := congrArg iq h
    simpa using this⟩
  have hcoe : ∀ g, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)) =
      ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (iq.comp (algebraMap O (FractionRing O))) := by
    intro g
    rw [coe_mapRep, coe_mapRep, Matrix.map_map]
    rfl
  refine ⟨GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ iq a _ hss, ?_, ?_, ?_⟩
  · simp only [hcoe]
    exact hr.matrix_map (GlobalTheory.T.continuous_ringHom_finite_dvr_to_padicAlgClosure l O hadic iq hiq)
  · intro σ hσ
    rw [hcoe, Matrix.charpoly_map, Polynomial.map_map]
    exact hp σ hσ
  · obtain ⟨T, hT⟩ := GlobalTheory.T.exists_finset_image_mem_subring l O iq hiq
    refine ⟨T, fun R hR hTR g i j => ?_⟩
    rw [hcoe]
    exact hT R hR hTR _

theorem exists_splitting_set : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (G E Ω)) (p : G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ (l' : ℕ) [Fact l'.Prime] (h : l = l') (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l'] O] [Module.Finite ℤ_[l'] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ iq : FractionRing O →+* Qbar l', (∀ z : ℤ_[l'], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l'] O z)) = algebraMap ℚ_[l'] (Qbar l') (z : ℚ_[l'])) → (∀ z ∈ S, ∃ x, qCast h ι (iq x) = z) → ∀ r : G E Ω →* GL (Fin a) O, Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) → IsSSRep (mapRep (algebraMap O (FractionRing O)) r) → (∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map ((qCast h ι).toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) → GlobalTheory.SplitCoef.SplitRep (mapRep (algebraMap O (FractionRing O)) r) := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ (ρ₀ : G E Ω →* GL (Fin a) (Qbar l)) (T : Finset (Qbar l)), IsSSRep ρ₀ ∧
      Continuous (fun g => ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
      ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
        (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j, ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R
  swap
  · refine ⟨∅, ?_⟩
    intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq _ r hr hss hp
    subst h
    exfalso
    obtain ⟨h1, h2, h3, T, h4⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
    exact hex ⟨_, T, h1, h2, h3, h4⟩
  obtain ⟨ρ₀, T, hss₀, hc₀, hp₀, hT⟩ := hex
  obtain ⟨n, Vs, hint, hirr⟩ := GlobalTheory.semisimple_matrix_rep_decomp ρ₀ hss₀
  choose b E D σ₀ hDE hran hσ₀ using fun j => GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep ρ₀ (Vs j) (hirr j).2.1
  let T' : Finset (Qbar l) := T ∪ Finset.univ.biUnion (fun j : Fin n =>
    Finset.univ.image (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) ∪
      Finset.univ.image (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2))
  refine ⟨T'.image ι, ?_⟩
  intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq hS r hr hss hp
  subst h
  obtain ⟨hss', hc', hp', -⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
  have hT'R : ∀ t ∈ T', t ∈ iq.range := by
    intro t ht
    obtain ⟨x, hx⟩ := hS (ι t) (Finset.mem_image_of_mem _ ht)
    exact ⟨x, ι.injective hx⟩
  have hRz : ∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ iq.range := fun z => ⟨_, hiq z⟩
  have hTR : (↑T : Set (Qbar l)) ⊆ (iq.range : Set (Qbar l)) := fun t ht => hT'R t (Finset.mem_union_left _ ht)
  have hER : ∀ j i s, E j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hDR : ∀ j i s, D j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hρ₀R := hT iq.range hRz hTR
  set ρ := mapRep (algebraMap O (FractionRing O)) r with hρ
  have hcp : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
    GlobalTheory.T.charpoly_eq_of_continuous_of_eq_on_dense _ _ hc' hc₀ U hU fun x hx =>
      Polynomial.map_injective _ ι.injective (by rw [hp' x hx, hp₀ x hx])
  obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (mapRep iq ρ) ρ₀ hss' hss₀ hcp
  have hint' : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) *
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) =
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) * ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g
    rw [hPm g]
    simp only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  apply GlobalTheory.T.isAbsolutelyIrreducibleSplitRep_of_constituent_models iq ρ
  intro V hV
  obtain ⟨j, M, hM, hMV, hMd⟩ := GlobalTheory.T.exists_intertwiner_map_eq_of_irrSub (mapRep iq ρ) ρ₀ Pm hint' hss' Vs
    hint.submodule_iSup_eq_top hirr V hV
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_rep_lift_of_entries_mem_range iq (σ₀ j) fun g i s => by
    have : ((σ₀ j g : GL (Fin (b j)) (Qbar l)) : Matrix (Fin (b j)) (Fin (b j)) (Qbar l)) i s ∈ iq.range := by
      rw [(hσ₀ j g).1]
      exact mem_mul_of_mem _ _ _ (mem_mul_of_mem _ _ _ (hDR j) (hρ₀R g)) (hER j) i s
    exact this
  refine ⟨b j, σ, M * E j, ?_, ?_, ?_⟩
  · intro v w hvw
    simp only [← Matrix.mulVec_mulVec] at hvw
    have hv : (E j).mulVec v ∈ Vs j := hran j ▸ ⟨v, rfl⟩
    have hw : (E j).mulVec w ∈ Vs j := hran j ▸ ⟨w, rfl⟩
    have hsub : (E j).mulVec v - (E j).mulVec w ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 hvw
    have h0 := hMd.le_bot ⟨hsub, Submodule.sub_mem _ hv hw⟩
    have hEq : (E j).mulVec v = (E j).mulVec w := sub_eq_zero.1 h0
    have := congrArg (D j).mulVec hEq
    simpa [Matrix.mulVec_mulVec, hDE j] using this
  · rw [Matrix.mulVecLin_mul, LinearMap.range_comp, hran j, hMV]
  · intro g
    rw [hσ, ← Matrix.mul_assoc, hM g, Matrix.mul_assoc, (hσ₀ j g).2, Matrix.mul_assoc]

end GlobalTheory.OSplitCore
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_splitting_set_frobeniusPolynomials : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (G E Ω)) (p : G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ (l' : ℕ) [Fact l'.Prime] (h : l = l') (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l'] O] [Module.Finite ℤ_[l'] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ iq : FractionRing O →+* Qbar l', (∀ z : ℤ_[l'], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l'] O z)) = algebraMap ℚ_[l'] (Qbar l') (z : ℚ_[l'])) → (∀ z ∈ S, ∃ x, qCast h ι (iq x) = z) → ∀ r : G E Ω →* GL (Fin a) O, Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) → IsSSRep (mapRep (algebraMap O (FractionRing O)) r) → (∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map ((qCast h ι).toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) → GlobalTheory.SplitCoef.SplitRep (mapRep (algebraMap O (FractionRing O)) r) := by
  atlas_forward_decl GlobalTheory.OSplitCore.exists_splitting_set
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.OSplitBig

theorem exists_big_oSplit : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∃ big : D.what₂.places.Pl → Finset ℂ, ∀ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), AutSpec A M tp.tup Sp.iq L.Y L.C → GlobalTheory.SplitCoef.OSplit (withLoc L) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb
  classical
  have hsys := fun w => GlobalTheory.T.galois_family_local_global D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb w
  choose FA Sy hSy using hsys
  have hexc := fun w : D.what₂.places.Pl => GlobalTheory.T.finite_exceptional_places_over_prime D (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)
  choose FB hFB using hexc
  let Fw : D.what₂.places.Pl → Finset (PlE D.host) := fun w => FA w ∪ FB w ∪ C.Q w
  let Pv : D.what₂.places.Pl → G D.host.E D.nd.Om → PlE D.host → Prop := fun w σ v =>
    v ∉ Fw w ∧ IsSplitPl D.host v ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ
  let pw : D.what₂.places.Pl → (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X] := fun w c σ =>
    if h : ∃ v, Pv w σ v then sysPol D c h.choose else 0
  have hcore := fun (w : D.what₂.places.Pl) (c : PlE D.host → ℕ → ℂ) =>
    GlobalTheory.T.exists_finite_splitting_set_frobeniusPolynomials (D.what₂.places.resChar w) (A.pl.ι w) D.host.E D.nd.Om D.R.nV (frobSet D (Fw w)) (pw w c)
      (dense_frobSet D hCheb (Fw w))
  choose SC hSC using hcore
  refine ⟨fun w => (Sy w).biUnion (SC w), ?_⟩
  intro L Sp hAut i x r hr
  obtain ⟨c, hcS, hc⟩ := hSy ((withLoc L).nd.w i) _ L Sp hAut i x rfl
  haveI : Fact ((withLoc L).nd.l i).Prime := (withLoc L).nd.lPrime i
  letI := (withLoc L).nd.dvrO i
  letI := (withLoc L).nd.algO i
  letI := (withLoc L).nd.finO i
  letI := (withLoc L).nd.topO i
  letI := (withLoc L).nd.trO i
  refine hSC ((withLoc L).nd.w i) c ((withLoc L).nd.l i) ((withLoc L).nd.w_l i) ((withLoc L).nd.O i) ((withLoc L).nd.O_adic i) (Sp.iq i) ?_ ?_ r
    hr.1 hr.2.1 ?_
  · exact fun z => Sp.iq_alg i z
  · intro z hz
    exact Sp.iq_big i z (Finset.mem_biUnion.2 ⟨c, hcS, hz⟩)
  · intro σ hσ
    have hex : ∃ v, Pv ((withLoc L).nd.w i) σ v := hσ
    have hspec := hex.choose_spec
    obtain ⟨hvF, hvs, B, hB, hFr⟩ := hspec
    have hvF' := hvF
    simp only [Fw, Finset.mem_union, not_or] at hvF'
    obtain ⟨⟨hvA, hvB⟩, hvQ⟩ := hvF'
    have hSO : SplitOut (withLoc L).nd i hex.choose := by
      have hQi : (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i) :=
        (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
      obtain ⟨h1, h2⟩ := hFB ((withLoc L).nd.w i) _ hvB
      refine ⟨hvs, ?_, ?_, ?_⟩
      · rw [← (withLoc L).nd.w_l i]; exact h1
      · intro hmem
        apply h2
        have := ((withLoc L).nd.S_def i _).1 hmem
        rw [← (withLoc L).nd.w_l i] at this
        exact this
      · show _ ∉ (withLoc L).nd.Q i
        rw [hQi]; exact hvQ
    refine (congrArg (Polynomial.map _) (hr.2.2 _ hSO B σ hB hFr)).trans ?_
    have hio : (qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i))).toRingHom.comp
        ((Sp.iq i).comp (algebraMap ((withLoc L).nd.O i) (FractionRing ((withLoc L).nd.O i)))) = iotaOC (withLoc L) i := by
      ext z
      simp only [iotaOC, RingHom.comp_apply]
      rw [show (withLoc L).naut.iotaQC i = L.Y.naut.iotaQC i from rfl, hAut.iotaQC i,
        show (withLoc L).naut.iotaQ i = L.Y.naut.iotaQ i from rfl, hAut.iotaQ i]
      rfl
    refine (congrArg (fun f => (heckePol (withLoc L).nd i x hex.choose).map f) hio).trans ?_
    rw [heckePol_map D L i x _ hSO]
    simp only [pw, dif_pos hex, sysPol]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc _ hvA k]

end GlobalTheory.OSplitBig
end
