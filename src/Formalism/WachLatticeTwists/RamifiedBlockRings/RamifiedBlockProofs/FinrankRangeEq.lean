import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CharpolyRevMap
import Formalism.CharacterColumnKernels.IdempotentNormalForms.IdemNormalForm
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaDetPoly
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Normal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsolutelyIrreducibleSpan
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SpacedProductLowerBound
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.BridgeDet
import Formalism.CharacterColumnKernels.IdempotentNormalForms.IsUnitDetOfConst

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section Span
variable {O K : Type} [CommRing O] [CommRing K] [Algebra O K] {X : Type} (T : Subalgebra O (X → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Monoid G] (r : G →* (X → Matrix d d K))

def term (c : X → O) (g : G) : X → Matrix d d K := fun x => algebraMap O K (c x) • r g x

theorem term_add (c c' : X → O) (g : G) : term r (c + c') g = term r c g + term r c' g := by
  funext x
  simp [term, add_smul]

theorem term_zero (g : G) : term r (0 : X → O) g = 0 := by
  funext x
  simp [term]

theorem term_mul (c c' : X → O) (g g' : G) : term r c g * term r c' g' = term r (c * c') (g * g') := by
  funext x
  simp only [term, Pi.mul_apply, map_mul]
  first
  | exact smul_mul_smul_comm _ _ _ _
  | exact smul_mul_smul _ _ _ _
  | simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

theorem mem_tSpan_iff (F : X → Matrix d d K) :
    F ∈ tSpan T r ↔ ∃ (s : Finset G) (c : G → X → O), (∀ g, c g ∈ T) ∧ F = ∑ g ∈ s, term r (c g) g := Iff.rfl

theorem term_mem {c : X → O} (hc : c ∈ T) (g : G) : term r c g ∈ tSpan T r := (mem_tSpan_iff T r _).2 ⟨{g}, fun _ => c, fun _ => hc, by simp⟩

theorem zero_mem_tSpan : (0 : X → Matrix d d K) ∈ tSpan T r := (mem_tSpan_iff T r 0).2 ⟨∅, fun _ => 0, fun _ => T.zero_mem, by simp⟩

theorem add_mem_tSpan {F F' : X → Matrix d d K} (h : F ∈ tSpan T r) (h' : F' ∈ tSpan T r) :
    F + F' ∈ tSpan T r := by
  classical
  obtain ⟨s, c, hc, rfl⟩ := (mem_tSpan_iff T r _).1 h
  obtain ⟨s', c', hc', rfl⟩ := (mem_tSpan_iff T r _).1 h'
  refine (mem_tSpan_iff T r _).2 ⟨s ∪ s', fun g => (if g ∈ s then c g else 0) + (if g ∈ s' then c' g else 0),
    fun g => T.add_mem (by split_ifs; exacts [hc g, T.zero_mem]) (by split_ifs; exacts [hc' g, T.zero_mem]), ?_⟩
  simp only [term_add, Finset.sum_add_distrib]
  congr 1
  · refine (Finset.sum_congr rfl fun g hg => ?_).trans (Finset.sum_subset Finset.subset_union_left fun g _ hg => ?_)
    · rw [if_pos hg]
    · rw [if_neg hg, term_zero]
  · refine (Finset.sum_congr rfl fun g hg => ?_).trans (Finset.sum_subset Finset.subset_union_right fun g _ hg => ?_)
    · rw [if_pos hg]
    · rw [if_neg hg, term_zero]

theorem sum_mem_tSpan {ι : Type*} (s : Finset ι) (F : ι → X → Matrix d d K)
    (h : ∀ i ∈ s, F i ∈ tSpan T r) : ∑ i ∈ s, F i ∈ tSpan T r := Finset.sum_induction _ (· ∈ tSpan T r) (fun _ _ ha hb => add_mem_tSpan T r ha hb)
  (zero_mem_tSpan T r) h

theorem mul_mem_tSpan {F F' : X → Matrix d d K} (h : F ∈ tSpan T r) (h' : F' ∈ tSpan T r) :
    F * F' ∈ tSpan T r := by
  obtain ⟨s, c, hc, rfl⟩ := (mem_tSpan_iff T r _).1 h
  obtain ⟨s', c', hc', rfl⟩ := (mem_tSpan_iff T r _).1 h'
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact sum_mem_tSpan T r _ _ fun g _ => sum_mem_tSpan T r _ _ fun g' _ => by
    rw [term_mul]
    exact term_mem T r (T.mul_mem (hc _) (hc' _)) _

theorem smul_mem_tSpan {f : X → O} (hf : f ∈ T) {F : X → Matrix d d K} (h : F ∈ tSpan T r) :
    (fun x => algebraMap O K (f x) • F x) ∈ tSpan T r := by
  obtain ⟨s, c, hc, rfl⟩ := (mem_tSpan_iff T r _).1 h
  refine (mem_tSpan_iff T r _).2 ⟨s, fun g => f * c g, fun g => T.mul_mem hf (hc g), ?_⟩
  funext x
  simp [term, Finset.sum_apply, Finset.smul_sum, smul_smul, map_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← map_mul, algebraMap_smul]

def spanSub : Subalgebra O (X → Matrix d d K) where
  carrier := tSpan T r
  mul_mem' := mul_mem_tSpan T r
  add_mem' := add_mem_tSpan T r
  algebraMap_mem' c := by
    have h1 : algebraMap O (X → Matrix d d K) c = term r (algebraMap O (X → O) c) 1 := by
      funext x
      simp [term, Algebra.algebraMap_eq_smul_one]
    rw [h1]
    exact term_mem T r (T.algebraMap_mem c) 1

end Span

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical Polynomial

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section
variable {O : Type} [CommRing O] {Xs : Type} (T : Subalgebra O (Xs → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (Xs → Matrix d d O))

def polyT : Subalgebra O[X] (Xs → O[X]) where
  carrier := {f | ∀ k, (fun x => (f x).coeff k) ∈ T}
  mul_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f * g) x).coeff k) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, (fun x => (f x).coeff p.1) * (fun x => (g x).coeff p.2) := by
      funext x; simp [Polynomial.coeff_mul, Finset.sum_apply]
    rw [h]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f + g) x).coeff k) = (fun x => (f x).coeff k) + fun x => (g x).coeff k := by
      funext x; simp
    rw [h]
    exact T.add_mem (hf k) (hg k)
  algebraMap_mem' p := by
    intro k
    have h : (fun x => ((algebraMap O[X] (Xs → O[X]) p) x).coeff k) =
        algebraMap O (Xs → O) (p.coeff k) := by
      funext x; simp
    rw [h]
    exact T.algebraMap_mem _

theorem C_mem_polyT {c : Xs → O} (hc : c ∈ T) : (fun x => C (c x)) ∈ polyT T := by
  show ∀ k, (fun x => (C (c x)).coeff k) ∈ T
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hc
  · have h0 : (fun x => (C (c x)).coeff k) = 0 := by
      funext x
      simp [Polynomial.coeff_C, hk.ne']
    rw [h0]
    exact T.zero_mem

def rPoly : G →* (Xs → Matrix d d O[X]) where
  toFun g x := (r g x).map C
  map_one' := by funext x; simp
  map_mul' g h := by funext x; simp [Matrix.map_mul]

theorem lift_mem {a : Xs → Matrix d d O} (ha : a ∈ tSpan T r) :
    (fun x => (a x).map C) ∈ tSpan (polyT T) (rPoly r) := by
  obtain ⟨s, c, hc, rfl⟩ := ha
  refine ⟨s, fun g x => C (c g x), fun g => C_mem_polyT T (hc g), ?_⟩
  funext x
  ext i j
  simp [rPoly, Finset.sum_apply, Matrix.sum_apply, map_sum]

private theorem matrix_charpolyRev_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix d d R) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]

theorem detT (hG1 : ∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T)
    (M : Xs → Matrix d d O[X]) (hM : M ∈ tSpan (polyT T) (rPoly r)) (k : ℕ) :
    (fun x => (M x).det.coeff k) ∈ T := by
  have h1 : ∀ (g : G) (k : ℕ), FromT (polyT T) (fun x => (Matrix.charpolyRev (rPoly r g x)).coeff k) := by
    intro g k
    refine ⟨fun x => C ((Matrix.charpolyRev (r g x)).coeff k), C_mem_polyT T (hG1 g k), fun x => ?_⟩
    have hx : rPoly r g x = (r g x).map C := rfl
    dsimp only
    rw [hx, matrix_charpolyRev_map, Polynomial.coeff_map]
    rfl
  obtain ⟨u, hu, hux⟩ := det_poly_statement O[X] O[X] Xs G d (polyT T) (rPoly r) h1 1 (fun _ => M)
    (fun _ => hM) (Finsupp.single 0 (Fintype.card d))
  have key : ∀ x, u x = (M x).det := by
    intro x
    have hx := hux x
    dsimp only at hx
    rw [Fin.sum_univ_one, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, mul_comm,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow] at hx
    simpa using hx
  have hfun : (fun x => (M x).det.coeff k) = fun x => (u x).coeff k := by
    funext x
    rw [key x]
  rw [hfun]
  exact hu k

end

theorem charT : StatCharT := by
  intro O _ X T d _ _ G _ r hG1 a ha k
  have hA : (fun x => (a x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r ha
  have hM : (fun x => 1 - (Polynomial.X : O[X]) • (a x).map C) ∈ spanSub (polyT T) (rPoly r) := by
    have he : (fun x => 1 - (Polynomial.X : O[X]) • (a x).map C) =
        1 - algebraMap O[X] (X → Matrix d d O[X]) Polynomial.X * (fun x => (a x).map C) := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc]
    rw [he]
    exact Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hA)
  exact detT T r hG1 _ hM k

theorem blockPolyT : StatBlockPolyT := by
  intro O _ X T d _ _ G _ r hG1 e he a ha k
  have hE : (fun x => (e x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r he
  have hA : (fun x => (a x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r ha
  have hM : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) ∈
      spanSub (polyT T) (rPoly r) := by
    have hq : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) =
        algebraMap O[X] (X → Matrix d d O[X]) Polynomial.X * (fun x => (e x).map C) -
          (fun x => (a x).map C) + (1 - fun x => (e x).map C) := by
      funext x
      ext i j
      by_cases h : i = j
      · subst h
        simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply]
      · simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply, h]
    rw [hq]
    exact Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hE) hA)
      (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hE)
  exact detT T r hG1 _ hM k

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem burnsideMat : StatBurnsideMat := by
  intro k _ n _ _ _ G _ ρ hρ
  obtain ⟨hirr, hcom⟩ := hρ
  let A := MonoidAlgebra k G
  let V := n → k
  let L : A →ₐ[k] Matrix n n k := MonoidAlgebra.lift k (Matrix n n k) G ρ
  let φ : A →ₐ[k] Module.End k V := (Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] _).toAlgHom.comp L
  letI : Module A V := Module.compHom V φ.toRingHom
  have hact : ∀ (a : A) (v : V), a • v = (L a).mulVec v := fun a v => rfl
  haveI : IsScalarTower k A V := ⟨fun c a v => by
    rw [hact, hact, map_smul, Matrix.smul_mulVec]⟩
  have hof : ∀ g, L (MonoidAlgebra.of k G g) = ρ g := fun g => MonoidAlgebra.lift_of ρ g
  have hS : IsSimpleModule A V := by
    haveI : Nontrivial (Submodule A V) := by
      refine ⟨⊥, ⊤, fun h => ?_⟩
      have : (⊤ : Submodule A V) = ⊥ := h.symm
      have h2 : (fun _ : n => (1 : k)) ∈ (⊤ : Submodule A V) := Submodule.mem_top
      rw [this, Submodule.mem_bot] at h2
      exact one_ne_zero (congrFun h2 (Classical.arbitrary n))
    suffices hso : IsSimpleOrder (Submodule A V) from @IsSimpleModule.mk _ _ _ _ _ hso
    refine ⟨fun W => ?_⟩
    rcases hirr (W.restrictScalars k) (fun g v hv => by
      have := W.smul_mem (MonoidAlgebra.of k G g) hv
      rw [hact, hof] at this
      exact this) with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff k A V).mp h
    · right; exact (Submodule.restrictScalars_eq_top_iff k A V).mp h
  have hsc : ∀ ψ : V →ₗ[A] V, ∃ c : k, ∀ v, ψ v = c • v := by
    intro ψ
    let M : Matrix n n k := LinearMap.toMatrix' (ψ.restrictScalars k)
    have hM : ∀ v, M.mulVec v = ψ v := fun v => by
      have := LinearMap.toMatrix'_mulVec (ψ.restrictScalars k) v
      simpa [M] using this
    obtain ⟨c, hc⟩ := hcom M (fun g => by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      rw [hM, hM, ← hof, ← hact, ← hact, map_smul])
    refine ⟨c, fun v => ?_⟩
    rw [← hM, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hsurj := burnside k A V hS hsc
  refine eq_top_iff.mpr fun B _ => ?_
  obtain ⟨a, ha⟩ := hsurj (Matrix.toLin' B)
  have hB : B = L a := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun ha v
    simp only [Matrix.toLin'_apply]
    rw [← hact]
    exact this.symm
  rw [hB]
  exact MonoidAlgebra.induction_on (motive := fun a => L a ∈ Submodule.span k (Set.range ρ)) a
    (fun g => by rw [hof]; exact Submodule.subset_span ⟨g, rfl⟩)
    (fun f g hf hg => by rw [map_add]; exact Submodule.add_mem _ hf hg)
    (fun c f hf => by rw [map_smul]; exact Submodule.smul_mem _ _ hf)

theorem ontoSpan : StatOntoSpan := by
  first | exact UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan .. | (apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (intros; apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> first | assumption | infer_instance)

theorem noeth : StatNoeth := by
  intro O _ _ _ X' _ d _ _ R' hint
  let L : (X' → d → d → O) →ₗ[O] (X' → Matrix d d (FractionRing O)) :=
    { toFun := fun F x' => Matrix.of fun i j => algebraMap O (FractionRing O) (F x' i j)
      map_add' := fun F F' => by funext x'; ext i j; simp
      map_smul' := fun c F => by funext x'; ext i j; simp [Algebra.smul_def] }
  have hle : Subalgebra.toSubmodule R' ≤ LinearMap.range L := by
    intro a ha
    choose F hF using hint a ha
    exact ⟨F, by funext x'; ext i j; exact hF x' i j⟩
  haveI : IsNoetherian O (LinearMap.range L) := inferInstance
  haveI h1 : IsNoetherian O (Subalgebra.toSubmodule R') := isNoetherian_of_le hle
  haveI h2 : IsNoetherian O R' := h1
  exact isNoetherian_of_tower O h2

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section Blocks
variable {A : Type*} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
  (bl : d → α)

theorem blk_mul {M N : Matrix d d A} (hM : ∀ i j, bl i ≠ bl j → M i j = 0) (c : α) :
    (M * N).toSquareBlock bl c = M.toSquareBlock bl c * N.toSquareBlock bl c := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]
  have h0 : ∑ k : {k // ¬ bl k = c}, M i (k : d) * N (k : d) j = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hM i k (by rw [hi]; exact Ne.symm k.2), zero_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => bl k = c) (fun k => M i k * N k j), h0,
    add_zero]

theorem diag_mul {M N : Matrix d d A} (hM : ∀ i j, bl i ≠ bl j → M i j = 0) (i : d)
    (hi : ∀ l, bl i = bl l → i = l) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rw [hM i k (fun h => hk (hi k h).symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Blocks

theorem r_mem {O : Type} [CommRing O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Monoid G] (r : G →* (X → Matrix d d O)) (g : G) : r g ∈ tSpan T r := by
  refine ⟨{g}, fun _ => 1, fun _ => T.one_mem, ?_⟩
  funext x
  simp

theorem rank_diag_ite {K : Type*} [Field K] {d : Type} [Fintype d] [DecidableEq d] (S : d → Prop)
    [DecidablePred S] :
    (Matrix.diagonal fun a => if S a then (1 : K) else 0).rank = Nat.card {a // S a} := by
  rw [Matrix.rank_diagonal, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by by_cases h : S a <;> simp [h])

set_option maxHeartbeats 1000000 in
theorem idem : StatIdem := by
  intro O _ _ _ _ X _ T d _ _ G _ r π t bl χ₁ ε hP hirr hcard0
  obtain ⟨hloc, hpts, hG1, hbd, hc1, hχ⟩ := hP
  let R := spanSub T r
  let k := IsLocalRing.ResidueField O
  let res : O →+* k := IsLocalRing.residue O
  have huniq : ∀ a b : d, bl a ≠ 0 → bl a = bl b → a = b := by
    intro a b ha hab
    have hs : Subsingleton {x // bl x = bl a} :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 _ ha))
    exact congrArg Subtype.val (hs.elim ⟨a, rfl⟩ ⟨b, hab.symm⟩)
  have hBD : ∀ a ∈ tSpan T r, ∀ i j, bl i ≠ bl j → a π i j = 0 := by
    rintro a ⟨s, c, hc, rfl⟩ i j hij
    simp [Finset.sum_apply, Matrix.sum_apply, hbd _ i j hij]
  let n0 := {a // bl a = 0}
  let ι := {a // bl a ≠ 0}
  let Φ : R →+* Matrix n0 n0 O × (ι → O) :=
    { toFun := fun a => ((a.1 π).toSquareBlock bl 0, fun i => a.1 π i.1 i.1)
      map_one' := by
        refine Prod.ext ?_ ?_
        · ext i j
          by_cases h : i = j
          · subst h; simp [Matrix.toSquareBlock_def]
          · have h' : i.1 ≠ j.1 := fun e => h (Subtype.ext e)
            simp [Matrix.toSquareBlock_def, Matrix.one_apply, h, h']
        · funext i
          simp
      map_mul' := fun a b => Prod.ext (blk_mul bl (hBD a.1 a.2) 0)
        (funext fun i => diag_mul bl (hBD a.1 a.2) i.1 (fun l hl => huniq _ _ i.2 hl))
      map_zero' := by
        refine Prod.ext ?_ ?_
        · ext i j; simp [Matrix.toSquareBlock_def]
        · funext i; simp
      map_add' := fun a b => by
        refine Prod.ext ?_ ?_
        · ext i j; simp [Matrix.toSquareBlock_def]
        · funext i; simp }
  let f₀ : R →+* Matrix n0 n0 k × (ι → k) :=
    (RingHom.prodMap res.mapMatrix (RingHom.compLeft res ι)).comp Φ
  have hf1 : ∀ (a : R) i j, (f₀ a).1 i j = res (a.1 π i.1 j.1) := fun a i j => rfl
  have hf2 : ∀ (a : R) i, (f₀ a).2 i = res (a.1 π i.1 i.1) := fun a i => rfl
  have hsm : ∀ (c : O) (a : R), f₀ (c • a) = res c • f₀ a := by
    intro c a
    refine Prod.ext ?_ ?_
    · ext i j
      rw [hf1]
      simp [hf1]
    · funext i
      rw [hf2]
      simp [hf2]
  let B' : Subalgebra k (Matrix n0 n0 k × (ι → k)) :=
    { toSubsemiring := f₀.rangeS
      algebraMap_mem' := fun c => by
        obtain ⟨c0, rfl⟩ := IsLocalRing.residue_surjective c
        refine ⟨c0 • (1 : R), ?_⟩
        rw [hsm, map_one, Algebra.algebraMap_eq_smul_one] }
  have hB' : ∀ z, z ∈ B' ↔ ∃ a, f₀ a = z := fun z => Iff.rfl
  obtain ⟨i0⟩ : Nonempty n0 := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num) hcard0)
  have : Nonempty n0 := ⟨i0⟩
  let rR : G →* R :=
    { toFun := fun g => ⟨r g, r_mem T r g⟩
      map_one' := Subtype.ext (map_one r)
      map_mul' := fun g h => Subtype.ext (map_mul r g h) }
  let ρb : G →* Matrix n0 n0 k := (((RingHom.fst _ _).comp f₀).toMonoidHom).comp rR
  have hb : Submodule.span k (Set.range ρb) = ⊤ := burnsideMat k n0 G ρb hirr
  have hsurj : ∀ A : Matrix n0 n0 k, ∃ z ∈ B', z.1 = A := by
    intro A
    have hA : A ∈ Submodule.span k (Set.range ρb) := hb ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨f₀ (rR g), ⟨rR g, rfl⟩, rfl⟩
    | zero => exact ⟨0, B'.zero_mem, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb', rfl⟩ := hy
      exact ⟨a + b, B'.add_mem ha hb', rfl⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨c • a, B'.smul_mem ha c, rfl⟩
  have hcor := cornerIdem k n0 ι B' hcard0 hsurj
  obtain ⟨u1, hu1⟩ := (hB' _).mp (hcor 1)
  obtain ⟨u2, hu2⟩ := (hB' _).mp (hcor (Matrix.single i0 i0 1))
  have hv1 : f₀ (1 - u1) = (0, 1) := by
    rw [map_sub, map_one, hu1]
    refine Prod.ext ?_ ?_ <;> simp
  have hfin : Module.Finite O R :=
    (inferInstance : Module.Finite O (Subalgebra.toSubmodule R))
  let f := f₀.rangeRestrict
  have hfs : Function.Surjective f := f₀.rangeRestrict_surjective
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨N, hN⟩ := satur O (X → Matrix d d O) (Subalgebra.toSubmodule R)
  have h5 : ∀ a ∈ IsLocalRing.maximalIdeal O • Subalgebra.toSubmodule R,
      ∃ w : R, w ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O R) ∧ w.1 = a := by
    intro a ha
    induction ha using Submodule.smul_induction_on' with
    | smul c hc m hm => exact ⟨c • ⟨m, hm⟩, Submodule.smul_mem_smul hc Submodule.mem_top, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨w, hw, rfl⟩ := ha
      obtain ⟨w', hw', rfl⟩ := hb
      exact ⟨w + w', Submodule.add_mem _ hw hw', rfl⟩
  have hker : ∀ x : R, f x = 0 →
      ∃ n : ℕ, x ^ n ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O R) := by
    intro x hx
    have hx0 : f₀ x = 0 := congrArg Subtype.val hx
    have hπ : (x.1 π).map res = 0 := by
      ext i j
      by_cases hij : bl i = bl j
      · by_cases hi : bl i = 0
        · exact congrFun (congrFun (congrArg Prod.fst hx0) ⟨i, hi⟩) ⟨j, hij ▸ hi⟩
        · have hh := huniq i j hi hij
          subst hh
          exact congrFun (congrArg Prod.snd hx0) ⟨i, hi⟩
      · simp [hBD x.1 x.2 i j hij]
    have hnil := nilConst O X T d hloc x.1 (charT O X T d G r hG1 x.1 x.2) π hπ
    have hdiv : ∀ y i j, ∃ c, ((x.1 y) ^ Fintype.card d) i j = ϖ * c := by
      intro y i j
      have h1 : res (((x.1 y) ^ Fintype.card d) i j) = 0 := congrFun (congrFun (hnil y) i) j
      have h2 : ((x.1 y) ^ Fintype.card d) i j ∈ IsLocalRing.maximalIdeal O :=
        (IsLocalRing.residue_eq_zero_iff _).mp h1
      rw [hmax, Ideal.mem_span_singleton] at h2
      exact h2
    choose c hc using hdiv
    let y : X → Matrix d d O := fun z => Matrix.of (c z)
    have hxy : x.1 ^ Fintype.card d = ϖ • y := by
      funext z; ext i j
      simp [y, hc]
    refine ⟨Fintype.card d * N, ?_⟩
    have h3 : x.1 ^ (Fintype.card d * N) ∈
        (IsLocalRing.maximalIdeal O) ^ N • (⊤ : Submodule O (X → Matrix d d O)) := by
      rw [pow_mul, hxy, smul_pow]
      exact Submodule.smul_mem_smul
        (Ideal.pow_mem_pow (hmax ▸ Ideal.mem_span_singleton_self ϖ) N) Submodule.mem_top
    obtain ⟨w, hw, hwe⟩ := h5 _ (hN (x.1 ^ (Fintype.card d * N)) (R.pow_mem x.2 _) h3)
    have hwx : w = x ^ (Fintype.card d * N) := Subtype.ext hwe
    rw [← hwx]; exact hw
  have hi1 : IsIdempotentElem (f (1 - u1)) := Subtype.ext (by
    show f₀ (1 - u1) * f₀ (1 - u1) = f₀ (1 - u1)
    rw [hv1]; refine Prod.ext ?_ ?_ <;> simp)
  have hi2 : IsIdempotentElem (f u2) := Subtype.ext (by
    show f₀ u2 * f₀ u2 = f₀ u2
    rw [hu2]; refine Prod.ext ?_ ?_ <;> simp)
  have h12 : f (1 - u1) * f u2 = 0 := Subtype.ext (by
    show f₀ (1 - u1) * f₀ u2 = 0
    rw [hv1, hu2]; refine Prod.ext ?_ ?_ <;> simp)
  have h21 : f u2 * f (1 - u1) = 0 := Subtype.ext (by
    show f₀ u2 * f₀ (1 - u1) = 0
    rw [hv1, hu2]; refine Prod.ext ?_ ?_ <;> simp)
  obtain ⟨E₁, E₂, hE1, hE2, hE12, hE21, hfE1, hfE2⟩ :=
    idemLift O R f₀.range f hfs hker _ _ hi1 hi2 h12 h21
  have hg1 : f₀ E₁ = (0, 1) := (congrArg Subtype.val hfE1).trans hv1
  have hg2 : f₀ E₂ = (Matrix.single i0 i0 1, 0) := (congrArg Subtype.val hfE2).trans hu2
  have hΦ1 : Φ E₁ * Φ E₁ = Φ E₁ := by rw [← map_mul, hE1.eq]
  have hΦ2 : Φ E₂ * Φ E₂ = Φ E₂ := by rw [← map_mul, hE2.eq]
  have hb1 : (Φ E₁).1 = 0 :=
    idemSmall O n0 (Φ E₁).1 (congrArg Prod.fst hΦ1) (congrArg Prod.fst hg1)
  have hd1 : ∀ i : ι, E₁.1 π i.1 i.1 = 1 := by
    intro i
    have h1 : IsIdempotentElem (E₁.1 π i.1 i.1) := congrFun (congrArg Prod.snd hΦ1) i
    have h2 : res (E₁.1 π i.1 i.1) = 1 := congrFun (congrArg Prod.snd hg1) i
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp h1 with h | h
    · rw [h, map_zero] at h2; exact absurd h2 zero_ne_one
    · exact h
  have hd2 : ∀ i : ι, E₂.1 π i.1 i.1 = 0 := by
    intro i
    have h1 : IsIdempotentElem (E₂.1 π i.1 i.1) := congrFun (congrArg Prod.snd hΦ2) i
    have h2 : res (E₂.1 π i.1 i.1) = 0 := congrFun (congrArg Prod.snd hg2) i
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp h1 with h | h
    · exact h
    · rw [h, map_one] at h2; exact absurd h2 one_ne_zero
  have heB : E₁.1 π = Matrix.diagonal (fun a => if bl a = 0 then 0 else 1) := by
    ext i j
    by_cases hij : bl i = bl j
    · by_cases hi : bl i = 0
      · have h1 : E₁.1 π i j = 0 := congrFun (congrFun hb1 ⟨i, hi⟩) ⟨j, hij ▸ hi⟩
        rw [h1]
        by_cases hh : i = j
        · subst hh; simp [hi]
        · rw [Matrix.diagonal_apply_ne _ hh]
      · have hh := huniq i j hi hij
        subst hh
        rw [hd1 ⟨i, hi⟩]; simp [hi]
    · rw [hBD E₁.1 E₁.2 i j hij, Matrix.diagonal_apply_ne _ (fun h => hij (congrArg bl h))]
  have he1 : ∀ a b, (bl a ≠ 0 ∨ bl b ≠ 0) → E₂.1 π a b = 0 := by
    intro a b hab
    by_cases hij : bl a = bl b
    · have ha : bl a ≠ 0 := by
        rcases hab with h | h
        · exact h
        · rw [hij]; exact h
      have hh := huniq a b ha hij
      subst hh
      exact hd2 ⟨a, ha⟩
    · exact hBD E₂.1 E₂.2 a b hij
  have hcardι : Fintype.card {a // bl a ≠ 0} = t := by
    have hbij : Function.Bijective
        (fun a : {a // bl a ≠ 0} => (⟨bl a.1, a.2⟩ : {c : Fin (t + 1) // c ≠ 0})) := by
      constructor
      · intro a b hab
        exact Subtype.ext (huniq a.1 b.1 a.2 (congrArg Subtype.val hab))
      · intro c
        obtain ⟨a⟩ : Nonempty {a // bl a = c.1} :=
          Fintype.card_pos_iff.mp (by rw [hc1 c.1 c.2]; norm_num)
        exact ⟨⟨a.1, by rw [a.2]; exact c.2⟩, Subtype.ext a.2⟩
    rw [Fintype.card_of_bijective hbij]
    simp [Fintype.card_subtype_compl]
  have hrB : ((E₁.1 π).map (algebraMap O (FractionRing O))).rank = t := by
    have h1 : (E₁.1 π).map (algebraMap O (FractionRing O)) =
        Matrix.diagonal fun a => if bl a ≠ 0 then (1 : FractionRing O) else 0 := by
      rw [heB]
      ext i j
      by_cases hh : i = j
      · subst hh
        by_cases hi : bl i = 0 <;> simp [hi]
      · simp [Matrix.diagonal_apply_ne _ hh]
    rw [h1, rank_diag_ite, Nat.card_eq_fintype_card]
    convert hcardι
  have hr1 : ((E₂.1 π).map (algebraMap O (FractionRing O))).rank = 1 := by
    rw [← rankMod O d (E₂.1 π) (congrFun (congrArg Subtype.val hE2.eq) π)]
    have h1 : (E₂.1 π).map (IsLocalRing.residue O) =
        Matrix.diagonal fun a => if a = i0.1 then (1 : k) else 0 := by
      ext i j
      by_cases hi : bl i = 0 ∧ bl j = 0
      · have h2 : res (E₂.1 π i j) = Matrix.single i0 i0 (1 : k) ⟨i, hi.1⟩ ⟨j, hi.2⟩ :=
          congrFun (congrFun (congrArg Prod.fst hg2) ⟨i, hi.1⟩) ⟨j, hi.2⟩
        show res (E₂.1 π i j) = _
        rw [h2, Matrix.single_apply, Matrix.diagonal_apply]
        by_cases h3 : i = i0.1
        · by_cases h4 : j = i0.1
          · subst h3; subst h4; simp
          · have : ¬ (i0 = ⟨j, hi.2⟩) := fun e => h4 (congrArg Subtype.val e).symm
            have h5 : i ≠ j := fun e => h4 (e ▸ h3)
            simp [this, h5]
        · have : ¬ (i0 = ⟨i, hi.1⟩) := fun e => h3 (congrArg Subtype.val e).symm
          simp [this, h3]
      · have h2 : E₂.1 π i j = 0 := he1 i j (by
          by_contra hcon
          push Not at hcon
          exact hi hcon)
        show res (E₂.1 π i j) = _
        rw [h2, map_zero, Matrix.diagonal_apply]
        by_cases h3 : i = j
        · subst h3
          have : i ≠ i0.1 := fun e => hi ⟨e ▸ i0.2, e ▸ i0.2⟩
          simp [this]
        · simp [h3]
    rw [h1, rank_diag_ite, Nat.card_eq_fintype_card]
    simp
  refine ⟨E₁.1, E₂.1, E₁.2, E₂.2, congrArg Subtype.val hE1.eq, congrArg Subtype.val hE2.eq,
    congrArg Subtype.val hE12, congrArg Subtype.val hE21, fun x => ?_, fun x => ?_, heB, he1⟩
  · rw [rankConst O X T d hloc E₁.1 (congrArg Subtype.val hE1.eq)
      (charT O X T d G r hG1 E₁.1 E₁.2) x π, hrB]
  · rw [rankConst O X T d hloc E₂.1 (congrArg Subtype.val hE2.eq)
      (charT O X T d G r hG1 E₂.1 E₂.2) x π, hr1]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem blockPoly_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {d : Type*} [Fintype d]
    [DecidableEq d] (e a : Matrix d d A) :
    (blockPoly e a).map f = blockPoly (e.map f) (a.map f) := by
  unfold blockPoly
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]

theorem r_mem' {O K : Type} [CommRing O] [CommRing K] [Algebra O K] {X : Type} (T : Subalgebra O (X → O))
    {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Monoid G] (r : G →* (X → Matrix d d K)) (g : G) :
    r g ∈ tSpan T r := by
  refine ⟨{g}, fun _ => 1, fun _ => T.one_mem, ?_⟩
  funext x
  simp

section Build
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type}
  (T' : Subalgebra O (X' → O)) {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G]
  (rK : G →* (X' → Matrix d d (FractionRing O)))

def scal : T' →+* spanSub T' rK where
  toFun f := ⟨term rK f.1 1, term_mem T' rK f.2 1⟩
  map_one' := Subtype.ext (by funext y; simp [term])
  map_mul' f g := Subtype.ext (by
    show term rK (f.1 * g.1) 1 = term rK f.1 1 * term rK g.1 1
    rw [term_mul, mul_one])
  map_zero' := Subtype.ext (term_zero rK 1)
  map_add' f g := Subtype.ext (term_add rK f.1 g.1 1)

theorem scal_apply (f : T') (y : X') :
    (scal T' rK f).1 y = algebraMap O (FractionRing O) (f.1 y) • (1 : Matrix d d (FractionRing O)) := by
  simp [scal, term]

@[instance_reducible] def algRp : Algebra T' (spanSub T' rK) :=
  RingHom.toAlgebra' (scal T' rK) (fun f a => Subtype.ext (by
    funext y
    show (scal T' rK f).1 y * a.1 y = a.1 y * (scal T' rK f).1 y
    rw [scal_apply]; simp))

@[instance_reducible] def modEvRp (x' : X') : Module T' (EvalSp O d (spanSub T' rK) x') :=
  Module.compHom _ ((algebraMap O (FractionRing O)).comp
    ((Pi.evalRingHom (fun _ : X' => O) x').comp T'.val.toRingHom))

theorem smul_val (f : T') (a : spanSub T' rK) (y : X') :
    (letI := algRp T' rK; (f • a : spanSub T' rK)).1 y =
      algebraMap O (FractionRing O) (f.1 y) • a.1 y := by
  letI := algRp T' rK
  show ((scal T' rK f) * a).1 y = _
  rw [Subalgebra.coe_mul, Pi.mul_apply, scal_apply, smul_mul_assoc, one_mul]


theorem finrank_range_eq (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (x' : X') (a : R') :
    Module.finrank (FractionRing O)
      (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') a)) =
      (a.1 x').rank := by
  show Module.finrank (FractionRing O) (LinearMap.range (a.1 x').mulVecLin) = _
  rfl

end Build

theorem inj_of_prod_eq {K : Type*} [Field K] {t : ℕ} (a b : Fin t → K) (hb : Function.Injective b)
    (h : ∏ i, (Polynomial.X - Polynomial.C (a i)) = ∏ i, (Polynomial.X - Polynomial.C (b i))) :
    Function.Injective a := by
  have key : ∀ c : Fin t → K, ∏ i, (Polynomial.X - Polynomial.C (c i)) =
      ((Finset.univ.val.map c).map fun x => Polynomial.X - Polynomial.C x).prod := by
    intro c
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  have hm : Finset.univ.val.map a = Finset.univ.val.map b := by
    have h2 := congrArg Polynomial.roots h
    rwa [key a, key b, Polynomial.roots_multiset_prod_X_sub_C,
      Polynomial.roots_multiset_prod_X_sub_C] at h2
  have hnd : (Finset.univ.val.map a).Nodup := by
    rw [hm]
    exact Multiset.Nodup.map hb Finset.univ.nodup
  intro x y hxy
  exact Multiset.inj_on_of_nodup_map hnd x (by simp) y (by simp) hxy

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end
