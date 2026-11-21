import Formalism.WachLatticeTwists.RamifiedBlockRings.ChainFromPrimitiveData
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.FinrankRangeEq
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdemFactor
import Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SplitFibre
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Normal
import Formalism.WachLatticeTwists.RamifiedBlockRings.LocalToDisplayFree
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveTopHolds
import Formalism.WachLatticeTwists.RamifiedBlockRings.DeltaRingProp
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.DensityPointOfCornerSimple
import Formalism.WachLatticeTwists.RamifiedBlockRings.Statement
import Formalism.CharacterColumnKernels.IdempotentNormalForms.MemCcIdealIffForall

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem rank_block {K : Type*} [Field K] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
    (bl : d → α) (k : α) (M : Matrix d d K) (hM : ∀ a b, (bl a ≠ k ∨ bl b ≠ k) → M a b = 0) :
    (M.toSquareBlock bl k).rank = M.rank := by
  let P : Matrix {a // bl a = k} d K := Matrix.of fun i a => if (i : d) = a then (1 : K) else 0
  have h1 : M.toSquareBlock bl k = P * M * P.transpose := by
    ext i j
    simp [P, Matrix.mul_apply, Matrix.toSquareBlock_def, Matrix.transpose_apply]
  have h2 : M = P.transpose * M.toSquareBlock bl k * P := by
    ext a b
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.toSquareBlock_def]
    by_cases ha : bl a = k
    · by_cases hb : bl b = k
      · rw [Finset.sum_eq_single ⟨b, hb⟩]
        · rw [Finset.sum_eq_single ⟨a, ha⟩]
          · simp
          · intro i _ hi
            have hne : (i : d) ≠ a := fun h => hi (Subtype.ext h)
            simp [hne]
          · simp
        · intro j _ hj
          have hne : (j : d) ≠ b := fun h => hj (Subtype.ext h)
          simp [hne]
        · simp
      · rw [hM a b (Or.inr hb)]
        refine (Finset.sum_eq_zero fun j _ => ?_).symm
        have hne : (j : d) ≠ b := fun h => hb (by rw [← h]; exact j.2)
        simp [hne]
    · rw [hM a b (Or.inl ha)]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      refine mul_eq_zero_of_left (Finset.sum_eq_zero fun i _ => ?_) _
      have hne : (i : d) ≠ a := fun h => ha (by rw [← h]; exact i.2)
      simp [hne]
  apply le_antisymm
  · rw [h1]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · calc M.rank = (P.transpose * M.toSquareBlock bl k * P).rank := congrArg Matrix.rank h2
      _ ≤ (M.toSquareBlock bl k).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem eDiag' (A : Type) [CommRing A] (d : Type) [Fintype d] [DecidableEq d] (S : d → Prop)
    [DecidablePred S] (β : d → A) (t : ℕ) (α : ℕ → A) :
    (Matrix.diagonal fun a => if S a then (1 : A) else 0) * ((List.range t).tail.map fun i =>
      (Matrix.diagonal fun a => if S a then β a else 0) -
        α i • (Matrix.diagonal fun a => if S a then (1 : A) else 0)).prod =
      Matrix.diagonal fun a => if S a then ∏ i ∈ Finset.Ioo 0 t, (β a - α i) else 0 := by
  have hc : ∀ f g : d → A, Matrix.diagonal f * Matrix.diagonal g =
      Matrix.diagonal g * Matrix.diagonal f := by
    intro f g
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _
  have hf : ∀ i, (Matrix.diagonal fun a => if S a then β a else 0) -
      α i • (Matrix.diagonal fun a => if S a then (1 : A) else 0) =
      Matrix.diagonal fun a => if S a then β a - α i else 0 := by
    intro i
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hs : S a <;> simp [hs]
    · simp [Matrix.diagonal_apply, hab]
  have hp : ∀ l : List ℕ, (Matrix.diagonal fun a => if S a then (1 : A) else 0) *
      (l.map fun i => Matrix.diagonal fun a => if S a then β a - α i else 0).prod =
      Matrix.diagonal fun a => if S a then (l.map fun i => β a - α i).prod else 0 := by
    intro l
    induction l with
    | nil => simp only [List.map_nil, List.prod_nil, mul_one]
    | cons x l ih =>
      rw [List.map_cons, List.prod_cons, ← mul_assoc, hc, mul_assoc, ih,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      by_cases hs : S a <;> simp [hs]
  have hl : ∀ f : ℕ → A, ((List.range t).tail.map f).prod = ∏ i ∈ Finset.Ioo 0 t, f i := by
    intro f
    have hnd : (List.range t).tail.Nodup :=
      List.Nodup.sublist (List.tail_sublist _) (List.nodup_range ..)
    rw [← List.prod_toFinset f hnd]
    congr 1
    ext x
    rw [List.mem_toFinset, Finset.mem_Ioo]
    cases t with
    | zero => simp
    | succ n =>
      rw [List.range_succ_eq_map, List.tail_cons, List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [List.mem_range] at hy
        omega
      · intro h
        exact ⟨x - 1, List.mem_range.2 (by omega), by omega⟩
  simp only [hf]
  rw [hp]
  congr 1
  funext a
  simp only [hl]

set_option maxHeartbeats 8000000 in
theorem ring_objects_of_matrix_data (hEM : StatEMat) (hSP : StatSplitPts) (hKO : StatIdemKO) : RingObjectsExist := by
  intro O _ _ _ X _ T d _ _ G _ r₀ π t ht bl χ₁ ε hP hA eB e₁ hI g₀ s hX
  obtain ⟨hloc, hpts, hG1, hbd, hc1, hχ⟩ := hP
  obtain ⟨heBm, he1m, heBB, he11, heB1, he1B, hrkB, hrk1, heBπ, he1π⟩ := hI
  obtain ⟨hsm, hes, hse, hsπ, hroots⟩ := hX
  let K := FractionRing O
  let ι : O →+* K := algebraMap O K
  have hι : Function.Injective ι := IsFractionRing.injective O K
  have huniq : ∀ a b : d, bl a ≠ 0 → bl a = bl b → a = b := by
    intro a b ha hab
    have hs : Subsingleton {x // bl x = bl a} :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 _ ha))
    exact congrArg Subtype.val (hs.elim ⟨a, rfl⟩ ⟨b, hab.symm⟩)
  let X0 : X → Matrix d d O := eB * r₀ g₀ * eB + s
  have hX0m : X0 ∈ tSpan T r₀ := add_mem_tSpan T r₀
    (mul_mem_tSpan T r₀ (mul_mem_tSpan T r₀ heBm (r_mem T r₀ g₀)) heBm) hsm
  let P : X → Polynomial O := fun x => blockPoly (eB x) (X0 x)
  have hPc : ∀ k, (fun x => (P x).coeff k) ∈ T := blockPolyT O X T d G r₀ hG1 eB heBm X0 hX0m
  have hPK : ∀ x, (P x).map ι = blockPoly ((eB x).map ι) ((X0 x).map ι) :=
    fun x => blockPoly_map ι _ _
  have hPr : ∀ x, ∃ α : Fin t → O, Function.Injective α ∧
      P x = ∏ i, (Polynomial.X - Polynomial.C (α i)) := by
    intro x
    obtain ⟨α, hα, h⟩ := hroots x
    obtain ⟨β, hβ, hPβ⟩ := rootsInt O (P x) t α (by rw [hPK]; exact h)
    exact ⟨β, fun i j hij => hα (by rw [← hβ, ← hβ, hij]), hPβ⟩
  obtain ⟨b, hb0, hb1, hb2⟩ := hSP O X T t P hPc hPr
  let X' := SplitPts t P
  let p : X' → X := fun y => y.1.1
  let T' : Subalgebra O (X' → O) := splitT T t P
  have hTT' : ∀ f ∈ T, (fun y : X' => f (p y)) ∈ T' :=
    fun f hf => Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)
  let rr : ℕ → T' := fun i =>
    if h : i < t then ⟨splitRoot t P ⟨i, h⟩, Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)⟩ else 0
  have hrr : ∀ i (h : i < t) (y : X'), (rr i).1 y = y.1.2 ⟨i, h⟩ := by
    intro i h y
    simp only [rr, dif_pos h]; rfl
  let rK : G →* (X' → Matrix d d K) :=
    { toFun := fun g y => (r₀ g (p y)).map ι
      map_one' := by funext y; simp
      map_mul' := fun g h => by funext y; simp [Matrix.map_mul] }
  let R' : Subalgebra O (X' → Matrix d d K) := spanSub T' rK
  letI iA : Algebra T' R' := algRp T' rK
  letI iE : ∀ x', Module T' (EvalSp O d R' x') := modEvRp T' rK
  have hpull : ∀ a ∈ tSpan T r₀, (fun y : X' => (a (p y)).map ι) ∈ tSpan T' rK := by
    rintro a ⟨S, c, hc, rfl⟩
    refine ⟨S, fun g y => c g (p y), fun g => hTT' _ (hc g), ?_⟩
    funext y; ext i j
    simp [Finset.sum_apply, Matrix.sum_apply, rK, ι]
    exact Finset.sum_congr rfl fun g _ => (Algebra.smul_def _ _).symm
  have hint : ∀ a ∈ tSpan T' rK, ∀ y, ∃ A : Matrix d d O, A.map ι = a y := by
    rintro a ⟨S, c, hc, rfl⟩ y
    refine ⟨∑ g ∈ S, c g y • r₀ g (p y), ?_⟩
    ext i j
    simp [Finset.sum_apply, Matrix.sum_apply, rK, ι]
    exact Finset.sum_congr rfl fun g _ => (Algebra.smul_def _ _).symm

  let γ : ℕ → O := fun i => (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)
  have heBπ' : eB π = Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0 := by
    rw [heBπ]; congr 1; funext a; by_cases h : bl a = 0 <;> simp [h]
  have hX0π : X0 π = Matrix.diagonal fun a => if bl a ≠ 0 then γ ((bl a : ℕ) - 1) else 0 := by
    show eB π * r₀ g₀ π * eB π + s π = _
    rw [hsπ, add_zero, heBπ']
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = j
    · subst hij
      by_cases hi : bl i = 0
      · simp [hi]
      · simp [hi, hχ g₀ i hi, γ]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hb : bl i = bl j
      · have hi : bl i = 0 := by
          by_contra hi
          exact hij (huniq i j hi hb)
        simp [hi]
      · rw [hbd g₀ i j hb]; simp
  have hPπ : P π = ∏ i : Fin t, (Polynomial.X - Polynomial.C (γ i)) := by
    let F : Fin (t + 1) → Polynomial O :=
      fun c => if c ≠ 0 then Polynomial.X - Polynomial.C (γ ((c : ℕ) - 1)) else 1
    have h1 : P π = ∏ a : d, F (bl a) := by
      show blockPoly (eB π) (X0 π) = _
      rw [heBπ', hX0π]
      unfold blockPoly
      have h2 : ((Polynomial.X : Polynomial O) •
          (Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0).map Polynomial.C -
          (Matrix.diagonal fun a => if bl a ≠ 0 then γ ((bl a : ℕ) - 1) else 0).map Polynomial.C +
          (1 - Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0).map Polynomial.C) =
          Matrix.diagonal fun a => F (bl a) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          by_cases hi : bl i = 0 <;> simp [hi, F]
        · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      rw [h2, Matrix.det_diagonal]
    have h3 : ∏ a : d, F (bl a) = ∏ c, F c := by
      rw [← Finset.prod_fiberwise univ bl (fun a => F (bl a))]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [Finset.prod_congr rfl (fun a ha => by rw [(mem_filter.mp ha).2]), Finset.prod_const]
      by_cases hc : c = 0
      · simp [hc, F]
      · have : #{a ∈ (univ : Finset d) | bl a = c} = 1 := by
          have h := hc1 c hc
          rw [Fintype.card_subtype] at h
          convert h
        rw [this, pow_one]
    rw [h1, h3, Fin.prod_univ_succ]
    simp [F, Fin.succ_ne_zero]
  let π' : X' := ⟨(π, fun i => γ i), hPπ⟩
  have hpπ : p π' = π := rfl
  have hrrπ : ∀ i, i < t → (rr i).1 π' = γ i := fun i h => hrr i h π'

  let ρf : R' → Matrix d d O := fun a => Classical.choose (hint a.1 a.2 π')
  have hρf : ∀ a : R', (ρf a).map ι = a.1 π' := fun a => Classical.choose_spec (hint a.1 a.2 π')
  have hent : ∀ (a : R') i j, ι (ρf a i j) = a.1 π' i j :=
    fun a i j => congrFun (congrFun (hρf a) i) j
  let ρπ : R' →ₐ[O] Matrix d d O :=
    { toFun := ρf
      map_one' := by
        ext i j; apply hι; rw [hent]
        show (1 : Matrix d d K) i j = ι ((1 : Matrix d d O) i j)
        by_cases h : i = j <;> simp [h, Matrix.one_apply]
      map_mul' := fun a b => by
        ext i j; apply hι; rw [hent]
        show (a.1 π' * b.1 π') i j = _
        simp only [Matrix.mul_apply, map_sum, map_mul, hent]
      map_zero' := by
        ext i j; apply hι; rw [hent]
        show (0 : Matrix d d K) i j = ι ((0 : Matrix d d O) i j)
        simp
      map_add' := fun a b => by
        ext i j; apply hι; rw [hent]
        show a.1 π' i j + b.1 π' i j = ι (ρf a i j + ρf b i j)
        rw [map_add, hent, hent]
      commutes' := fun c => by
        ext i j; apply hι; rw [hent]
        show (algebraMap O (Matrix d d K) c) i j = ι ((algebraMap O (Matrix d d O) c) i j)
        by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply, ι] }
  have hentπ : ∀ (a : R') i j, ι (ρπ a i j) = a.1 π' i j := hent
  have hBDK : ∀ a ∈ tSpan T' rK, ∀ i j, bl i ≠ bl j → a π' i j = 0 := by
    rintro a ⟨S, c, hc, rfl⟩ i j hij
    have : ∀ g, rK g π' i j = 0 := fun g => by
      show ι (r₀ g π i j) = 0
      rw [hbd g i j hij, map_zero]
    simp [Finset.sum_apply, Matrix.sum_apply, this]
  have hBD : ∀ (a : R') i j, bl i ≠ bl j → ρπ a i j = 0 := fun a i j hij => by
    apply hι; rw [hentπ, hBDK a.1 a.2 i j hij, map_zero]
  let ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O := fun k =>
    { toFun := fun a => (ρπ a).toSquareBlock bl k
      map_one' := by
        rw [map_one]
        ext i j
        by_cases h : i = j
        · subst h; simp [Matrix.toSquareBlock_def]
        · have h' : i.1 ≠ j.1 := fun e => h (Subtype.ext e)
          simp [Matrix.toSquareBlock_def, Matrix.one_apply, h, h']
      map_mul' := fun a b => by rw [map_mul]; exact blk_mul bl (hBD a) k
      map_zero' := by rw [map_zero]; ext i j; simp [Matrix.toSquareBlock_def]
      map_add' := fun a b => by rw [map_add]; ext i j; simp [Matrix.toSquareBlock_def]
      commutes' := fun c => by
        rw [AlgHom.commutes]
        ext i j
        by_cases h : i = j
        · subst h; simp [Matrix.toSquareBlock_def, Matrix.algebraMap_matrix_apply]
        · have h' : i.1 ≠ j.1 := fun e => h (Subtype.ext e)
          simp [Matrix.toSquareBlock_def, Matrix.algebraMap_matrix_apply, h, h'] }
  have hρk : ∀ k (a : R') i j, ρk k a i j = ρπ a i.1 j.1 := fun k a i j => rfl
  letI iB : ∀ k, Module T' (blockRestrictedRepresentationType bl ρk k) := fun k =>
    Module.compHom _ ((Pi.evalRingHom (fun _ : X' => O) π').comp T'.val.toRingHom)
  have hactB : ∀ k (a : R') (m : blockRestrictedRepresentationType bl ρk k), a • m = fun i => ∑ j, ρk k a i j • (m j : KO O) :=
    fun k a m => rfl
  have hTB : ∀ (f : T') k (m : blockRestrictedRepresentationType bl ρk k), f • m = (f.1 π') • m := fun f k m => rfl
  have hTE : ∀ (f : T') x' (v : EvalSp O d R' x'), f • v = ι (f.1 x') • v := fun f x' v => rfl

  let rR : G →* R' :=
    { toFun := fun g => ⟨rK g, r_mem' T' rK g⟩
      map_one' := Subtype.ext (map_one rK)
      map_mul' := fun g h => Subtype.ext (map_mul rK g h) }
  let χ : G →* (T')ˣ := (Units.map (algebraMap O T').toMonoidHom).comp χ₁
  let eB' : R' := ⟨fun y => (eB (p y)).map ι, hpull eB heBm⟩
  let e₁' : R' := ⟨fun y => (e₁ (p y)).map ι, hpull e₁ he1m⟩
  let X₀' : R' := ⟨fun y => (X0 (p y)).map ι, hpull X0 hX0m⟩
  let E : R' := eB' * ((List.range t).tail.map fun i => X₀' - rr i • eB').prod
  let δ : T' := ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i)
  have hsv : ∀ (f : T') (a : R') y, (f • a : R').1 y = ι (f.1 y) • a.1 y := smul_val T' rK
  have hEy : ∀ y, E.1 y = eB'.1 y *
      ((List.range t).tail.map fun i => X₀'.1 y - ι ((rr i).1 y) • eB'.1 y).prod := by
    intro y
    show evalAt O d R' y E = _
    rw [map_mul, map_list_prod, List.map_map]
    refine congrArg₂ _ rfl (congrArg List.prod (List.map_congr_left fun i _ => ?_))
    show X₀'.1 y - (rr i • eB' : R').1 y = _
    rw [hsv]
  have hδy : ∀ y, ι (δ.1 y) = ∏ i ∈ Finset.Ioo 0 t, (ι ((rr 0).1 y) - ι ((rr i).1 y)) := by
    intro y
    have h1 : δ.1 y = ∏ i ∈ Finset.Ioo 0 t, ((rr 0).1 y - (rr i).1 y) := by
      show ((Pi.evalRingHom (fun _ : X' => O) y).comp T'.val.toRingHom) δ = _
      rw [map_prod]; rfl
    rw [h1, map_prod]
    simp only [map_sub]
  have heX0 : eB * X0 = X0 := by
    show eB * (eB * r₀ g₀ * eB + s) = eB * r₀ g₀ * eB + s
    rw [mul_add, hes, ← mul_assoc, ← mul_assoc, heBB]
  have hX0e : X0 * eB = X0 := by
    show (eB * r₀ g₀ * eB + s) * eB = eB * r₀ g₀ * eB + s
    rw [add_mul, hse, mul_assoc, heBB]
  have hmapmul : ∀ (u v w : X → Matrix d d O), u * v = w → ∀ x, (u x).map ι * (v x).map ι = (w x).map ι := by
    intro u v w h x
    rw [← Matrix.map_mul, ← h]; rfl
  have hyinj : ∀ y : X', Function.Injective y.1.2 := by
    intro y
    obtain ⟨α, hα, hPα⟩ := hPr (p y)
    have h2 : (P (p y)).map ι = ∏ i, (Polynomial.X - Polynomial.C (ι (y.1.2 i))) := by
      rw [show P (p y) = _ from y.2, Polynomial.map_prod]; simp
    have h3 : (P (p y)).map ι = ∏ i, (Polynomial.X - Polynomial.C (ι (α i))) := by
      rw [hPα, Polynomial.map_prod]; simp
    have h4 := inj_of_prod_eq (fun i => ι (y.1.2 i)) (fun i => ι (α i)) (hι.comp hα) (h2.symm.trans h3)
    exact fun i j hij => h4 (congrArg ι hij)
  have hpoly : ∀ y : X', blockPoly (eB'.1 y) (X₀'.1 y) =
      ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (ι ((rr i).1 y))) := by
    intro y
    show blockPoly ((eB (p y)).map ι) ((X0 (p y)).map ι) = _
    rw [← hPK, show P (p y) = _ from y.2, Polynomial.map_prod, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hrr i.1 i.2 y]; simp
  have hpt : ∀ y : X', E.1 y * E.1 y = ι (δ.1 y) • E.1 y ∧ (E.1 y).rank = 1 ∧ ι (δ.1 y) ≠ 0 := by
    intro y
    obtain ⟨h1, h2, -, -, -, h6⟩ := hEM K d (eB'.1 y) (X₀'.1 y) t (fun i => ι ((rr i).1 y)) ht
      (hmapmul eB eB eB heBB (p y)) (hmapmul eB X0 X0 heX0 (p y)) (hmapmul X0 eB X0 hX0e (p y))
      (hpoly y) (fun i j hi hj hij => by
        have hij' : ι ((rr i).1 y) = ι ((rr j).1 y) := hij
        rw [hrr i hi, hrr j hj] at hij'
        exact congrArg Fin.val (hyinj y (hι hij')))
    rw [hEy, hδy]
    exact ⟨h1, h2, h6⟩

  let δO : O := δ.1 π'
  let val : d → K := fun a => if bl a ≠ 0 then
    ∏ i ∈ Finset.Ioo 0 t, (ι (γ ((bl a : ℕ) - 1)) - ι ((rr i).1 π')) else 0
  have hEπ : E.1 π' = Matrix.diagonal val := by
    rw [hEy]
    have h1 : eB'.1 π' = Matrix.diagonal fun a => if bl a ≠ 0 then (1 : K) else 0 := by
      show (eB π).map ι = _
      rw [heBπ']
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases hi : bl i = 0 <;> simp [hi]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have h2 : X₀'.1 π' = Matrix.diagonal fun a => if bl a ≠ 0 then ι (γ ((bl a : ℕ) - 1)) else 0 := by
      show (X0 π).map ι = _
      rw [hX0π]
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases hi : bl i = 0 <;> simp [hi]
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [h1, h2]
    exact eDiag' K d (fun a => bl a ≠ 0) (fun a => ι (γ ((bl a : ℕ) - 1))) t
      (fun i => ι ((rr i).1 π'))
  have hval0 : ∀ a, bl a = 0 → val a = 0 := fun a h => by simp [val, h]
  have hval1 : ∀ a, (bl a : ℕ) = 1 → val a = ι δO := fun a h => by
    have h0 : bl a ≠ 0 := fun e => by rw [e] at h; simp at h
    simp only [val, if_pos h0, h, Nat.sub_self]
    rw [hδy, hrrπ 0 (by omega)]
  have hval2 : ∀ a, 2 ≤ (bl a : ℕ) → val a = 0 := fun a h => by
    have h0 : bl a ≠ 0 := fun e => by rw [e] at h; simp at h
    simp only [val, if_pos h0]
    have hlt : (bl a : ℕ) - 1 < t := by have := (bl a).2; omega
    refine Finset.prod_eq_zero (i := (bl a : ℕ) - 1) (Finset.mem_Ioo.mpr ⟨by omega, hlt⟩) ?_
    rw [hrrπ _ hlt, sub_self]
  have hscal : ∀ k (a : R') (w : O),
      (∀ i j : {a // bl a = k}, a.1 π' i.1 j.1 = if i = j then ι w else 0) →
      ∀ m : blockRestrictedRepresentationType bl ρk k, a • m = w • m := by
    intro k a w h m
    rw [hactB]
    funext i
    have h1 : ∀ j, ρk k a i j = if i = j then w else 0 := fun j => by
      apply hι; rw [hρk, hentπ, h]; split_ifs <;> simp
    show ∑ j, ρk k a i j • (m j : KO O) = w • (m i : KO O)
    simp only [h1, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hEblk : ∀ k (w : O), (∀ a, bl a = k → val a = ι w) → ∀ m : blockRestrictedRepresentationType bl ρk k, E • m = w • m := by
    intro k w h
    refine hscal k E w fun i j => ?_
    rw [hEπ, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [h i.1 i.2]
    · have h' : i.1 ≠ j.1 := fun e => hij (Subtype.ext e)
      simp [hij, h']
  have he1blk : ∀ k, k ≠ 0 → ∀ m : blockRestrictedRepresentationType bl ρk k, e₁' • m = 0 := by
    intro k hk m
    rw [hscal k e₁' 0 (fun i j => by
      show ι (e₁ π i.1 j.1) = _
      rw [he1π i.1 j.1 (Or.inl (by rw [i.2]; exact hk))]; simp), zero_smul]
  obtain ⟨sE, cE, hcE, hEsum⟩ := (E.2 : E.1 ∈ tSpan T' rK)
  let tE : G → T' := fun g => ⟨cE g, hcE g⟩
  have hEs : E = ∑ g ∈ sE, tE g • rR g := Subtype.ext (by
    show E.1 = R'.val (∑ g ∈ sE, tE g • rR g)
    rw [hEsum, map_sum]
    exact Finset.sum_congr rfl fun g _ => funext fun y => (hsv (tE g) (rR g) y).symm)
  let τ : T' := ∑ g ∈ sE, tE g * ((χ g : (T')ˣ) : T')
  let c1 : Fin (t + 1) := ⟨1, by omega⟩
  have hc10 : c1 ≠ 0 := fun e => by simpa [c1] using congrArg Fin.val e
  obtain ⟨a1⟩ : Nonempty {a // bl a = c1} := Fintype.card_pos_iff.mp (by rw [hc1 c1 hc10]; norm_num)
  have hτ : τ.1 π' = δO := by
    apply hι
    have h1 : τ.1 π' = ∑ g ∈ sE, cE g π' * (χ₁ g : O) := by
      show ((Pi.evalRingHom (fun _ : X' => O) π').comp T'.val.toRingHom) τ = _
      rw [map_sum]; rfl
    have h2 : E.1 π' a1.1 a1.1 = ι δO := by
      rw [hEπ, Matrix.diagonal_apply_eq]
      exact hval1 a1.1 (by rw [a1.2])
    rw [← h2, hEsum, h1, map_sum]
    simp only [Finset.sum_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    show _ = ι (cE g π') • ι (r₀ g π a1.1 a1.1)
    rw [hχ g a1.1 (by rw [a1.2]; exact hc10), a1.2]
    simp [c1]
  have hfinX : Finite X' := by
    let Zs : Finset O := univ.biUnion fun x => (P x).roots.toFinset
    let f : X' → X × (Fin t → Zs) := fun y => (y.1.1, fun i => ⟨y.1.2 i, by
      refine mem_biUnion.mpr ⟨y.1.1, mem_univ _, ?_⟩
      have hy : P y.1.1 = ∏ i, (Polynomial.X - Polynomial.C (y.1.2 i)) := y.2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      refine ⟨?_, ?_⟩
      · rw [hy]
        exact (Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _).ne_zero
      · rw [Polynomial.IsRoot, hy, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (mem_univ i) (by simp)⟩)
    refine Finite.of_injective f fun y y' h => ?_
    have h1 : y.1.1 = y'.1.1 := congrArg (fun z => z.1) h
    have h2 : ∀ i, y.1.2 i = y'.1.2 i := fun i => congrArg (fun z => (z.2 i).1) h
    exact Subtype.ext (Prod.ext h1 (funext h2))
  have i1 : IsNoetherian R' R' := noeth O X' d R' (fun a ha x' i j => by
    obtain ⟨A, hA'⟩ := hint a ha x'
    exact ⟨A i j, congrFun (congrFun hA' i) j⟩)
  have i2 : ∀ x', IsScalarTower T' R' (EvalSp O d R' x') := fun x' => ⟨fun f a v => by
    rw [hTE]
    funext i
    show ∑ j, (f • a : R').1 x' i j • (v j : K) = ι (f.1 x') • ∑ j, a.1 x' i j • (v j : K)
    rw [hsv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]⟩
  have i3 : ∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k) := fun k =>
    ⟨fun a c m => LinearMap.map_smul (matEnd O (KO O) _ ((ρk k).toRingHom a)) c m⟩
  have hρsm : ∀ (f : T') (a : R') i j, ρπ (f • a) i j = f.1 π' * ρπ a i j := by
    intro f a i j
    apply hι
    rw [hentπ, hsv, map_mul, hentπ]; rfl
  have i4 : ∀ k, IsScalarTower T' R' (blockRestrictedRepresentationType bl ρk k) := fun k => ⟨fun f a m => by
    rw [hTB]
    funext i
    show ∑ j, ρk k (f • a) i j • (m j : KO O) = f.1 π' • ∑ j, ρk k a i j • (m j : KO O)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hρk, hρsm, mul_smul]; rfl⟩
  have i5 : ∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k) := fun k => ⟨fun c a m => by
    funext i
    show ∑ j, ρk k (c • a) i j • (m j : KO O) = c • ∑ j, ρk k a i j • (m j : KO O)
    rw [Finset.smul_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, mul_smul]⟩
  have hρr : ∀ g, ρπ (rR g) = r₀ g π := fun g => by
    ext i j; apply hι; rw [hentπ]; rfl
  have hsurj : ∀ k, Function.Surjective (ρk k) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      let ρ0 : G →* Matrix {a // bl a = 0} {a // bl a = 0} O :=
        ((ρk 0).toRingHom.toMonoidHom).comp rR
      have h0 : (fun g => (ρ0 g).map (IsLocalRing.residue O)) =
          fun g => ((r₀ g π).toSquareBlock bl 0).map (IsLocalRing.residue O) := funext fun g => by
        show ((ρπ (rR g)).toSquareBlock bl 0).map _ = _
        rw [hρr]
      have hspan := ontoSpan O _ G ρ0 (h0 ▸ hA)
      intro B
      have hB : B ∈ Submodule.span O (Set.range ρ0) := hspan ▸ Submodule.mem_top
      have hle : Submodule.span O (Set.range ρ0) ≤ LinearMap.range (ρk 0).toLinearMap :=
        Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact ⟨rR g, rfl⟩)
      obtain ⟨a, ha⟩ := hle hB
      exact ⟨a, ha⟩
    · intro B
      have hs : Subsingleton {a // bl a = k} :=
        Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 k hk))
      obtain ⟨i0⟩ : Nonempty {a // bl a = k} :=
        Fintype.card_pos_iff.mp (by rw [hc1 k hk]; norm_num)
      refine ⟨algebraMap O R' (B i0 i0), ?_⟩
      rw [AlgHom.commutes]
      ext i j
      rw [hs.elim i i0, hs.elim j i0]
      simp [Matrix.algebraMap_matrix_apply]
  have he1e1 : e₁' * e₁' = e₁' := Subtype.ext (funext fun y => hmapmul e₁ e₁ e₁ he11 (p y))
  have hKO1 : Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁')) ≃ₗ[O] KO O) := by
    have h1 : DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁' = matEnd O (KO O) _ (ρk 0 e₁') :=
      LinearMap.ext fun m => rfl
    rw [h1]
    refine hKO O _ (ρk 0 e₁') (by rw [← map_mul, he1e1]) ?_
    have h2 : (ρk 0 e₁').map (algebraMap O (FractionRing O)) = ((e₁ π).map ι).toSquareBlock bl 0 := by
      ext i j
      exact hentπ e₁' i.1 j.1
    rw [h2, rank_block bl 0 ((e₁ π).map ι) (fun a b hab => by
      show ι (e₁ π a b) = 0
      rw [he1π a b hab, map_zero])]
    exact hrk1 π
  have hχinv : ∀ g, (((χ g)⁻¹ : (T')ˣ) : T').1 π' = (((χ₁ g)⁻¹ : Oˣ) : O) := fun g => by
    rw [← map_inv, ← map_inv]; rfl
  have hu1 : ∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt rR χ g • m = m := by
    intro g m
    have hs : Subsingleton {a // bl a = c1} :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 c1 hc10))
    rw [hscal c1 (uElt rR χ g) 1 (fun i j => by
      rw [if_pos (hs.elim i j), hs.elim j i]
      show ((((χ g)⁻¹ : (T')ˣ) : T') • rR g : R').1 π' i.1 i.1 = ι 1
      rw [hsv, hχinv]
      show ι _ • ι (r₀ g π i.1 i.1) = ι 1
      rw [hχ g i.1 (by rw [i.2]; exact hc10), i.2]
      have h0 : ((c1 : Fin (t + 1)) : ℕ) - 1 = 0 := rfl
      rw [h0, pow_zero, Units.val_one, mul_one, smul_eq_mul, ← map_mul, Units.inv_mul]), one_smul]
  have hG1' : ∀ (g : G) (k : ℕ), FromT T' (fun x => (Matrix.charpolyRev (rK g x)).coeff k) :=
    fun g k => ⟨fun y => (Matrix.charpolyRev (r₀ g (p y))).coeff k, hTT' _ (hG1 g k), fun y => by
      show ι _ = (Matrix.charpolyRev ((r₀ g (p y)).map ι)).coeff k
      rw [← charpolyRev_map, Polynomial.coeff_map]⟩
  have hcomp : (R'.val.toRingHom.toMonoidHom.comp rR) = rK := MonoidHom.ext fun g => rfl
  let D : RingData O X d G t bl :=
    { X' := X', T' := T', p := p, q := t.factorial, b := b, R' := R', algT := iA, modEv := iE,
      r := rR, χ := χ, eB := eB', e₁ := e₁', X₀ := X₀', E := E, rr := rr, π' := π', ρπ := ρπ,
      ρk := ρk, blockModuleStructure := iB, sE := sE, tE := tE }
  refine ⟨D, ⟨hpoly, ?_, ?_, rfl, rfl, hrrπ, fun g x' => rfl, ?_, hsv, hTE, hTB, fun g x' => rfl,
    fun x' => rfl, fun x' => rfl, fun x' => rfl, rfl, hρf, fun a k => rfl, hb0, hb1, ?_, hEs⟩,
    ⟨i1, i2, i3, i4, i5⟩, i3, ?_⟩
  · intro x α h
    have hPx : P x = ∏ i : Fin t, (Polynomial.X - Polynomial.C (α i)) := by
      apply Polynomial.map_injective ι hι
      rw [hPK, Polynomial.map_prod]
      refine Eq.trans h ?_
      rw [Finset.prod_range]
      exact Finset.prod_congr rfl fun i _ => by simp [ι] <;> rfl
    refine ⟨⟨(x, fun i => α i), hPx⟩, ⟨rfl, fun i hi => hrr i hi _⟩, ?_⟩
    rintro y ⟨hy1, hy2⟩
    exact Subtype.ext (Prod.ext hy1 (funext fun i => by
      rw [← hrr i.1 i.2 y]; exact hy2 i.1 i.2))
  · show Algebra.adjoin O _ = Algebra.adjoin O _
    congr 2
    ext f'
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, funext fun y => (hrr i.1 i.2 y).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, funext fun y => (hrr i hi y).symm⟩
  · intro a
    show a ∈ R' ↔ a ∈ tSpan T' (R'.val.toRingHom.toMonoidHom.comp rR)
    rw [hcomp]
    exact Iff.rfl
  · intro a _ h0
    funext k x
    refine congrFun (hb2 x (fun k => a k x) fun x' hx' => ?_) k
    have h1 := congrFun h0 x'
    rw [Finset.sum_apply] at h1
    rw [← hx']
    exact h1
  · show RingTop O X X' T T' p t.factorial b d R' T' G rR χ E e₁' δ π' ρπ t ht bl ρk sE tE δO
    refine ⟨hb1, hb2, fun g _ _ Θ => eta_determinant_comparison det_poly_statement blockDet O X' G T' d R' rK hG1'
      (fun a ha => ha) g Θ, ?_, he1e1, ?_, hρf, fun a i j hij => hBD a i j (ne_of_gt hij), hsurj,
      fun a k => rfl, hc1, hEs, ?_, fun m => hTB δ 0 m, ?_, hKO1, ?_, hu1, he1blk c1 hc10, ?_,
      fun m => hTB δ c1 m⟩
    · exact Subtype.ext (funext fun y => by
        show E.1 y * E.1 y = (scal T' rK δ).1 y * E.1 y
        rw [(hpt y).1, scal_apply, Matrix.smul_mul, Matrix.one_mul])
    · exact fun x' => ⟨ι (δ.1 x'), (hpt x').2.2, fun v => hTE δ x' v,
        by rw [finrank_range_eq]; exact (hpt x').2.1, by rw [finrank_range_eq]; exact hrk1 (p x')⟩
    · intro m
      rw [hEblk 0 0 (fun a ha => by rw [hval0 a ha, map_zero]), zero_smul]
    · intro m
      rw [hTB τ 0 m, hτ]
    · intro c hc
      have hc0 : c ≠ 0 := fun e => by rw [e] at hc; simp at hc
      refine ⟨he1blk c hc0, fun m => ?_, fun m => hTB δ c m, fun m => ?_⟩
      · rw [hEblk c 0 (fun a ha => by rw [hval2 a (by rw [ha]; exact hc), map_zero]), zero_smul]
      · rw [hTB τ c m, hτ]
    · exact hEblk c1 δO (fun a ha => hval1 a (by rw [ha]))

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

set_option maxHeartbeats 1000000 in
theorem splitPts : StatSplitPts := by
  intro O _ _ Xs T t P hPc hPr
  rcases isEmpty_or_nonempty Xs with hX | hX
  · exact ⟨fun _ _ => 0, fun _ => (splitT T t P).zero_mem, fun f' _ => ⟨fun _ _ => 0, fun _ => T.zero_mem,
      funext fun y => (hX.elim y.1.1)⟩, fun x => hX.elim x⟩
  have hnt : Nontrivial T := inferInstance
  let evT : Xs → (T →+* O) := fun x => (Pi.evalRingHom (fun _ : Xs => O) x).comp T.val.toRingHom
  have hmonP : ∀ x, (P x).Monic := fun x => by
    obtain ⟨α, -, h⟩ := hPr x
    rw [h]; exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdegP : ∀ x, (P x).natDegree = t := fun x => by
    obtain ⟨α, -, h⟩ := hPr x
    rw [h, Polynomial.natDegree_finset_prod_X_sub_C_eq_card]; simp
  let PT : Polynomial T := ∑ k ∈ range (t + 1), Polynomial.monomial k ⟨fun x => (P x).coeff k, hPc k⟩
  have hcoef : ∀ k, PT.coeff k = if k ≤ t then ⟨fun x => (P x).coeff k, hPc k⟩ else 0 := by
    intro k
    simp only [PT, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_range, Nat.lt_succ_iff]
  have hmap : ∀ x, PT.map (evT x) = P x := by
    intro x
    ext k
    rw [Polynomial.coeff_map, hcoef]
    split_ifs with hk
    · rfl
    · rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegP]; omega)]
  have hle : PT.natDegree ≤ t := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hcoef, if_neg (by omega)]
  have hone : PT.coeff t = 1 := by
    rw [hcoef, if_pos le_rfl]
    refine Subtype.ext (funext fun x => ?_)
    have := (hmonP x).coeff_natDegree
    rw [hdegP] at this
    exact this
  have hmon : PT.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one t hle hone
  have hdeg : PT.natDegree = t :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (by rw [hone]; exact one_ne_zero))
  have key := splitAlg T PT hmon
  rw [hdeg] at key
  obtain ⟨T', _, _, rr, hfree, hfin, hrank, hfac, hadj, huniv⟩ := key
  have hψ : ∀ y : SplitPts t P, ∃ ψ : T' →+* O, ψ.comp (algebraMap T T') = evT y.1.1 ∧
      ∀ i, ψ (rr i) = y.1.2 i := by
    intro y
    letI : Algebra T O := (evT y.1.1).toAlgebra
    obtain ⟨φ, hφ, -⟩ := huniv O y.1.2 (by
      show PT.map (evT y.1.1) = _
      rw [hmap]; exact y.2)
    exact ⟨φ.toRingHom, RingHom.ext fun τ => φ.commutes τ, hφ⟩
  choose ψ hψ1 hψ2 using hψ
  let Ψ : T' →+* (SplitPts t P → O) := Pi.ringHom ψ
  let bas : Module.Basis (Fin t.factorial) T T' := Module.finBasisOfFinrankEq T T' hrank
  have hΨa : ∀ τ : T, Ψ (algebraMap T T' τ) = fun y => τ.1 y.1.1 :=
    fun τ => funext fun y => RingHom.congr_fun (hψ1 y) τ
  have hrange : ∀ f' ∈ splitT T t P, ∃ z, Ψ z = f' := by
    intro f' hf'
    induction hf' using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨f, hf, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨algebraMap T T' ⟨f, hf⟩, hΨa _⟩
      · exact ⟨rr i, funext fun y => hψ2 y i⟩
    | algebraMap c => exact ⟨algebraMap T T' (algebraMap O T c), hΨa _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩
  have hmemΨ : ∀ z, Ψ z ∈ splitT T t P := by
    intro z
    have hz : z ∈ Algebra.adjoin T (Set.range rr) := hadj ▸ Algebra.mem_top
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have h1 : Ψ (rr i) = splitRoot t P i := funext fun y => hψ2 y i
      rw [h1]
      exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
    | algebraMap τ =>
      rw [hΨa]
      exact Algebra.subset_adjoin (Or.inl ⟨τ.1, τ.2, rfl⟩)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨fun k => Ψ (bas k), fun k => hmemΨ _, ?_, ?_⟩
  · intro f' hf'
    obtain ⟨z, rfl⟩ := hrange f' hf'
    refine ⟨fun k => (bas.repr z k).1, fun k => (bas.repr z k).2, ?_⟩
    conv_lhs => rw [← bas.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hΨa]
  · intro x a ha
    let K := FractionRing O
    let ι : O →+* K := algebraMap O K
    have hι : Function.Injective ι := IsFractionRing.injective O K
    obtain ⟨α, hα, hPα⟩ := hPr x
    have hmapK : PT.map (ι.comp (evT x)) = ∏ i, (Polynomial.X - Polynomial.C (ι (α i))) := by
      rw [← Polynomial.map_map, hmap, hPα, Polynomial.map_prod]; simp
    have sf := splitFibre T T' K PT hmon
    rw [hdeg] at sf
    have hz := sf rr hfac hadj bas (ι.comp (evT x)) (fun i => ι (α i)) (hι.comp hα) hmapK
      (fun k => ι (a k)) (by
      intro φ hφ
      have h1 : ∏ i, (Polynomial.X - Polynomial.C (φ (rr i))) =
          ∏ i, (Polynomial.X - Polynomial.C (ι (α i))) := by
        rw [← hmapK, ← hφ, ← Polynomial.map_map, hfac, Polynomial.map_prod]; simp
      have h2 : ∀ i, ∃ j, φ (rr i) = ι (α j) := by
        intro i
        have h3 : (∏ j, (Polynomial.X - Polynomial.C (ι (α j)))).eval (φ (rr i)) = 0 := by
          rw [← h1, Polynomial.eval_prod]
          exact Finset.prod_eq_zero (mem_univ i) (by simp)
        rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h3
        obtain ⟨j, -, hj⟩ := h3
        exact ⟨j, by simpa [sub_eq_zero] using hj⟩
      choose σ hσ using h2
      have hy : P x = ∏ i, (Polynomial.X - Polynomial.C (α (σ i))) := by
        apply Polynomial.map_injective ι hι
        rw [hPα, Polynomial.map_prod, Polynomial.map_prod]
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        rw [← h1]
        exact Finset.prod_congr rfl fun i _ => by rw [hσ]
      let y : SplitPts t P := ⟨(x, fun i => α (σ i)), hy⟩
      have hφy : ∀ z, φ z = ι (ψ y z) := by
        letI : Algebra T K := (ι.comp (evT x)).toAlgebra
        let φ1 : T' →ₐ[T] K := { φ with commutes' := fun τ => RingHom.congr_fun hφ τ }
        let φ2 : T' →ₐ[T] K :=
          { (ι.comp (ψ y)) with
            commutes' := fun τ => by
              show ι (ψ y (algebraMap T T' τ)) = _
              rw [show ψ y (algebraMap T T' τ) = evT x τ from RingHom.congr_fun (hψ1 y) τ]
              rfl }
        have h12 : φ1 = φ2 := AlgHom.ext_of_adjoin_eq_top hadj (by
          rintro _ ⟨i, rfl⟩
          show φ (rr i) = ι (ψ y (rr i))
          rw [hψ2, hσ])
        exact fun z => DFunLike.congr_fun h12 z
      have h4 := congrArg ι (ha y rfl)
      rw [map_sum, map_zero] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hφy, map_mul]
      rfl)
    funext k
    exact hι (by
      show ι (a k) = ι 0
      rw [map_zero]; exact congrFun hz k)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem idemKO : StatIdemKO := by
  intro O _ _ _ n _ _ e he hr
  classical
  set eK := e.map (algebraMap O (FractionRing O)) with heK
  have hidK : eK * eK = eK := by
    rw [heK, ← Matrix.map_mul, he]
  have hsub : (LinearMap.range (Matrix.toLin' eK)).subtype.comp (Matrix.toLin' eK).rangeRestrict =
      Matrix.toLin' eK := LinearMap.ext fun v => rfl
  have hid : (Matrix.toLin' eK).rangeRestrict.comp (LinearMap.range (Matrix.toLin' eK)).subtype =
      LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨v, w, rfl⟩
    apply Subtype.ext
    show Matrix.toLin' eK (Matrix.toLin' eK w) = Matrix.toLin' eK w
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hidK]
  have hfr : Module.finrank (FractionRing O) (LinearMap.range (Matrix.toLin' eK)) = 1 := by
    rw [← hr]
    rfl
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 1) (FractionRing O) (LinearMap.range (Matrix.toLin' eK))) :=
    ⟨Module.finBasisOfFinrankEq _ _ hfr⟩
  obtain ⟨U, W, hUW, hWU⟩ : ∃ (U : Matrix n (Fin 1) (FractionRing O))
      (W : Matrix (Fin 1) n (FractionRing O)), U * W = eK ∧ W * U = 1 :=
    ⟨LinearMap.toMatrix b (Pi.basisFun _ n) (LinearMap.range (Matrix.toLin' eK)).subtype,
      LinearMap.toMatrix (Pi.basisFun _ n) b (Matrix.toLin' eK).rangeRestrict,
      by rw [← LinearMap.toMatrix_comp, hsub, LinearMap.toMatrix_eq_toMatrix',
        LinearMap.toMatrix'_toLin'],
      by rw [← LinearMap.toMatrix_comp, hid, LinearMap.toMatrix_id]⟩
  have hfact : ∀ i j, eK i j = U i 0 * W 0 j := by
    intro i j
    rw [← hUW, Matrix.mul_apply, Fin.sum_univ_one]
  have hsum : ∑ i, W 0 i * U i 0 = 1 := by
    have h := congrFun (congrFun hWU 0) 0
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have inj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have hmap : ∀ i j, algebraMap O (FractionRing O) (e i j) = eK i j := fun i j => rfl
  have htr : ∑ i, e i i = 1 := by
    apply inj
    rw [map_sum, map_one]
    simp only [hmap, hfact]
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨i0, hi0⟩ : ∃ i0, IsUnit (e i0 i0) := by
    by_contra hcon
    push_neg at hcon
    have hmem : ∑ i, e i i ∈ IsLocalRing.maximalIdeal O :=
      Ideal.sum_mem _ fun i _ => (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (hcon i))
    rw [htr] at hmem
    exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hmem) isUnit_one
  have hminor : ∀ i j k l, e i j * e k l = e i l * e k j := by
    intro i j k l
    apply inj
    simp only [map_mul, hmap, hfact]
    ring
  obtain ⟨c, hc⟩ := hi0
  have hfe : ∀ i j, e i j = e i i0 * (↑c⁻¹ * e i0 j) := by
    intro i j
    have h := hminor i j i0 i0
    rw [← hc] at h
    calc e i j = e i j * ↑c * ↑c⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h]; ring
  have hφu : ∑ j, ↑c⁻¹ * e i0 j * e j i0 = 1 := by
    have h := congrFun (congrFun he i0) i0
    rw [Matrix.mul_apply, ← hc] at h
    calc ∑ j, ↑c⁻¹ * e i0 j * e j i0 = ↑c⁻¹ * ∑ j, e i0 j * e j i0 := by
          rw [Finset.mul_sum]
          simp only [mul_assoc]
      _ = 1 := by rw [h, Units.inv_mul]
  let ψ : KO O →ₗ[O] (n → KO O) := LinearMap.pi fun i => e i i0 • LinearMap.id
  let χ : (n → KO O) →ₗ[O] KO O := ∑ j, (↑c⁻¹ * e i0 j) • LinearMap.proj j
  have hχψ : ∀ m, χ (ψ m) = m := by
    intro m
    simp only [χ, ψ, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, LinearMap.pi_apply, LinearMap.id_apply, smul_smul]
    rw [← Finset.sum_smul, hφu, one_smul]
  have hmat : matEnd O (KO O) n e = ψ.comp χ := by
    apply LinearMap.ext
    intro v
    funext i
    show ∑ j, e i j • v j = _
    simp only [χ, ψ, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.sum_apply, LinearMap.proj_apply,
      Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [hfe i j]
  have hinj : Function.Injective ψ := fun a b h => by rw [← hχψ a, ← hχψ b, h]
  have hχ : LinearMap.range χ = ⊤ := LinearMap.range_eq_top.2 fun m => ⟨ψ m, hχψ m⟩
  exact ⟨(LinearEquiv.ofEq _ _ (by rw [hmat, LinearMap.range_comp_of_range_eq_top ψ hχ])).trans
    (LinearEquiv.ofInjective ψ hinj).symm⟩

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

theorem ring_objects_exist : RingObjectsExist := ring_objects_of_matrix_data eMat splitPts idemKO

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities


end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem densityMod (k A : Type*) [Field k] [Ring A] [Algebra k A] {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, Module A (V i)]
    [∀ i, IsScalarTower k A (V i)] [∀ i, FiniteDimensional k (V i)]
    (hS : ∀ i, IsSemisimpleModule A (V i))
    (hsc : ∀ i, ∀ φ : V i →ₗ[A] V i, ∃ c : k, ∀ v, φ v = c • v)
    (hz : ∀ i j, i ≠ j → ∀ φ : V j →ₗ[A] V i, φ = 0)
    (f : ∀ i, V i →ₗ[k] V i) : ∃ a : A, ∀ i v, a • v = f i v := by
  have hφ : ∀ φ : Module.End A (∀ i, V i), ∃ c : ι → k, ∀ w i, φ w i = c i • w i := by
    intro φ
    choose c hc using fun i => hsc i ((LinearMap.proj i).comp (φ.comp (LinearMap.single A V i)))
    refine ⟨c, fun w i => ?_⟩
    have hw : w = ∑ j, Pi.single j (w j) := (Finset.univ_sum_single w).symm
    conv_lhs => rw [hw]
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · exact hc i (w i)
    · intro j _ hj
      have := LinearMap.congr_fun
        (hz i j (Ne.symm hj) ((LinearMap.proj i).comp (φ.comp (LinearMap.single A V j)))) (w j)
      exact this
    · intro h; exact absurd (Finset.mem_univ i) h
  let F : Module.End (Module.End A (∀ i, V i)) (∀ i, V i) :=
    { toFun := fun w i => f i (w i)
      map_add' := fun w w' => by funext i; simp
      map_smul' := fun φ w => by
        obtain ⟨c, hc⟩ := hφ φ
        funext i
        simp only [Module.End.smul_def, RingHom.id_apply, hc, (f i).map_smul] }
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image (Module.finBasis k (∀ i, V i)))
  let F' : (∀ i, V i) →ₗ[k] (∀ i, V i) := LinearMap.pi fun i => (f i).comp (LinearMap.proj i)
  have hEq : DistribSMul.toLinearMap k (∀ i, V i) a = F' := by
    refine (Module.finBasis k (∀ i, V i)).ext fun b => ?_
    have := ha (Module.finBasis k (∀ i, V i) b) (Finset.mem_image_of_mem _ (Finset.mem_univ b))
    exact this.symm
  refine ⟨a, fun i v => ?_⟩
  have := congrFun (LinearMap.congr_fun hEq (Pi.single i v)) i
  simpa [F'] using this

theorem toSquareBlock_mul_of_diag {K : Type*} [CommRing K] {d : Type*} [Fintype d] [DecidableEq d]
    {m : ℕ} (c : d → Fin m) (M N : Matrix d d K) (hM : ∀ a b, c a ≠ c b → M a b = 0) (i : Fin m) :
    (M * N).toSquareBlock c i = M.toSquareBlock c i * N.toSquareBlock c i := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun x => c x = i) (by simp)
    (fun x => M a x * N x b)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
  have hx' : c x ≠ i := by simpa using hx
  rw [hM a x (by rw [ha]; exact Ne.symm hx'), zero_mul]

theorem density : StatDensity := by
  intro K _ d _ _ G _ ρ m c P hG B hB
  obtain ⟨hP, hdiag, hirr, hint⟩ := hG
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hP'P : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet

  let σ : G →* Matrix d d K :=
    { toFun := fun g => P * ρ g * P⁻¹
      map_one' := by rw [map_one, Matrix.mul_one, hPP]
      map_mul' := fun g h => by
        have : P * ρ g * P⁻¹ * (P * ρ h * P⁻¹) = P * ρ g * (P⁻¹ * P) * ρ h * P⁻¹ := by
          simp only [Matrix.mul_assoc]
        rw [this, hP'P, Matrix.mul_one, map_mul]
        simp only [Matrix.mul_assoc] }
  have hσ : ∀ g, σ g = P * ρ g * P⁻¹ := fun g => rfl

  let τ : ∀ i : Fin m, G →* Matrix {a // c a = i} {a // c a = i} K := fun i =>
    { toFun := fun g => (σ g).toSquareBlock c i
      map_one' := by
        rw [map_one]
        ext ⟨a, ha⟩ ⟨b, hb⟩
        simp [Matrix.toSquareBlock_def, Matrix.one_apply]
      map_mul' := fun g h => by
        rw [map_mul]
        exact toSquareBlock_mul_of_diag c _ _ (hdiag g) i }
  have hτ : ∀ i g, τ i g = (P * ρ g * P⁻¹).toSquareBlock c i := fun i g => rfl
  let A := MonoidAlgebra K G
  let V : Fin m → Type _ := fun i => {a // c a = i} → K
  let L : A →ₐ[K] Matrix d d K := MonoidAlgebra.lift K (Matrix d d K) G σ
  let Lb : ∀ i, A →ₐ[K] Matrix {a // c a = i} {a // c a = i} K := fun i =>
    MonoidAlgebra.lift K _ G (τ i)
  have hof : ∀ g, L (MonoidAlgebra.of K G g) = σ g := fun g => MonoidAlgebra.lift_of σ g
  have hofb : ∀ i g, Lb i (MonoidAlgebra.of K G g) = τ i g := fun i g => MonoidAlgebra.lift_of (τ i) g
  let _ : ∀ i, AddCommGroup (V i) := fun i => inferInstanceAs (AddCommGroup ({a // c a = i} → K))
  let _ : ∀ i, Module K (V i) := fun i => inferInstanceAs (Module K ({a // c a = i} → K))
  have : ∀ i, FiniteDimensional K (V i) := fun i =>
    inferInstanceAs (FiniteDimensional K ({a // c a = i} → K))
  let _ : ∀ i, Module A (V i) := fun i => Module.compHom (V i)
    ((Matrix.toLinAlgEquiv' : Matrix {a // c a = i} {a // c a = i} K ≃ₐ[K] _).toAlgHom.comp
      (Lb i)).toRingHom
  have hact : ∀ i (a : A) (v : V i), a • v = (Lb i a).mulVec v := fun i a v => rfl
  have : ∀ i, IsScalarTower K A (V i) := fun i => ⟨fun x a v => by
    rw [hact, hact, map_smul, Matrix.smul_mulVec]⟩
  have hS : ∀ i, IsSemisimpleModule A (V i) := by
    intro i
    rcases isEmpty_or_nonempty {a // c a = i} with hn | hn
    · have : Subsingleton (V i) := inferInstanceAs (Subsingleton ({a // c a = i} → K))
      have : Subsingleton (Submodule A (V i)) := inferInstance
      exact (isSemisimpleModule_iff A (V i)).mpr Subsingleton.instComplementedLattice
    · have : Nontrivial (Submodule A (V i)) := by
        refine ⟨⊥, ⊤, fun h => ?_⟩
        have h2 : (fun _ : {a // c a = i} => (1 : K)) ∈ (⊤ : Submodule A (V i)) := Submodule.mem_top
        rw [← h, Submodule.mem_bot] at h2
        exact one_ne_zero (congrFun h2 (Classical.arbitrary _))
      suffices hso : IsSimpleOrder (Submodule A (V i)) from
        have := @IsSimpleModule.mk _ _ _ _ _ hso
        inferInstance
      refine ⟨fun W => ?_⟩
      rcases (hirr i).1 (W.restrictScalars K) (fun g v hv => by
        have := W.smul_mem (MonoidAlgebra.of K G g) hv
        rw [hact, hofb] at this
        exact this) with h | h
      · left; exact (Submodule.restrictScalars_eq_bot_iff K A (V i)).mp h
      · right; exact (Submodule.restrictScalars_eq_top_iff K A (V i)).mp h

  have hmat : ∀ i j (ψ : V j →ₗ[A] V i), ∃ M : Matrix {a // c a = i} {a // c a = j} K,
      (∀ v, M.mulVec v = ψ v) ∧ ∀ g, M * τ j g = τ i g * M := by
    intro i j ψ
    let M : Matrix {a // c a = i} {a // c a = j} K := LinearMap.toMatrix' (ψ.restrictScalars K)
    have hM : ∀ v, M.mulVec v = ψ v := fun v => by
      simp [M]
    refine ⟨M, hM, fun g => ?_⟩
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    rw [hM, hM, ← hofb, ← hofb, ← hact, ← hact, map_smul]
  have hsc : ∀ i, ∀ ψ : V i →ₗ[A] V i, ∃ x : K, ∀ v, ψ v = x • v := by
    intro i ψ
    obtain ⟨M, hM, hMg⟩ := hmat i i ψ
    obtain ⟨x, hx⟩ := (hirr i).2 M hMg
    refine ⟨x, fun v => ?_⟩
    rw [← hM, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hz : ∀ i j, i ≠ j → ∀ ψ : V j →ₗ[A] V i, ψ = 0 := by
    intro i j hij ψ
    obtain ⟨M, hM, hMg⟩ := hmat i j ψ
    have h0 := hint i j hij M hMg
    refine LinearMap.ext fun v => ?_
    rw [← hM, h0, Matrix.zero_mulVec]
    rfl
  obtain ⟨a, ha⟩ := densityMod K A V hS hsc hz
    (fun i => Matrix.toLin' ((P * B * P⁻¹).toSquareBlock c i))

  have hLdiag : ∀ a : A, (∀ x y, c x ≠ c y → L a x y = 0) ∧
      ∀ i, (L a).toSquareBlock c i = Lb i a := by
    intro a
    refine MonoidAlgebra.induction_on (motive := fun a => (∀ x y, c x ≠ c y → L a x y = 0) ∧
      ∀ i, (L a).toSquareBlock c i = Lb i a) a ?_ ?_ ?_
    · intro g
      refine ⟨fun x y hxy => ?_, fun i => ?_⟩
      · rw [hof]; exact hdiag g x y hxy
      · rw [hof, hofb]; rfl
    · intro f g hf hg
      refine ⟨fun x y hxy => ?_, fun i => ?_⟩
      · rw [map_add, Matrix.add_apply, hf.1 x y hxy, hg.1 x y hxy, add_zero]
      · rw [map_add, map_add, ← hf.2 i, ← hg.2 i]; rfl
    · intro x f hf
      refine ⟨fun y z hyz => ?_, fun i => ?_⟩
      · rw [map_smul, Matrix.smul_apply, hf.1 y z hyz, smul_zero]
      · rw [map_smul, map_smul, ← hf.2 i]; rfl
  have hLa : L a = P * B * P⁻¹ := by
    have hb : ∀ i, Lb i a = (P * B * P⁻¹).toSquareBlock c i := by
      intro i
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, ← ha i v, hact]
    ext x y
    by_cases hxy : c x = c y
    · have := congrFun (congrFun (((hLdiag a).2 (c y)).trans (hb (c y))) ⟨x, hxy⟩) ⟨y, rfl⟩
      exact this
    · rw [(hLdiag a).1 x y hxy, hB x y hxy]
  have hspan : ∀ a : A, P⁻¹ * L a * P ∈ Submodule.span K (Set.range ρ) := by
    intro a
    refine MonoidAlgebra.induction_on
      (motive := fun a => P⁻¹ * L a * P ∈ Submodule.span K (Set.range ρ)) a ?_ ?_ ?_
    · intro g
      have : P⁻¹ * L (MonoidAlgebra.of K G g) * P = ρ g := by
        rw [hof, hσ]
        have : P⁻¹ * (P * ρ g * P⁻¹) * P = (P⁻¹ * P) * ρ g * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
        rw [this, hP'P, Matrix.one_mul, Matrix.mul_one]
      rw [this]; exact Submodule.subset_span ⟨g, rfl⟩
    · intro f g hf hg
      rw [map_add, Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hf hg
    · intro x f hf
      rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ _ hf
  have hfin : B = P⁻¹ * L a * P := by
    rw [hLa]
    have : P⁻¹ * (P * B * P⁻¹) * P = (P⁻¹ * P) * B * (P⁻¹ * P) := by
      simp only [Matrix.mul_assoc]
    rw [this, hP'P, Matrix.one_mul, Matrix.mul_one]
  rw [hfin]
  exact hspan a

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem blockPoly_corner {K : Type} [Field K] {d S : Type} [Fintype d] [DecidableEq d] [Fintype S]
    [DecidableEq S] (e : Matrix d d K) (U : Matrix d S K) (W : Matrix S d K) (hUW : U * W = e)
    (hWU : W * U = 1) (A : Matrix S S K) : blockPoly e (U * A * W) = A.charpoly := by
  unfold blockPoly Matrix.charpoly Matrix.charmatrix
  let C' : K →+* Polynomial K := Polynomial.C
  have hUW' : U.map C' * W.map C' = e.map C' := by rw [← Matrix.map_mul, hUW]
  have hWU' : W.map C' * U.map C' = 1 := by
    rw [← Matrix.map_mul, hWU, Matrix.map_one _ C'.map_zero C'.map_one]
  have hx' : (U * A * W).map C' = U.map C' * A.map C' * W.map C' := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
  have h1 : (Polynomial.X : Polynomial K) • e.map C' - (U * A * W).map C' + (1 - e).map C' =
      1 + U.map C' * (((Polynomial.X : Polynomial K) • 1 - A.map C' - 1) * W.map C') := by
    have h2 : (1 - e).map C' = 1 - e.map C' := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [h2, hx', ← hUW']
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij, C']

theorem cornerSimple : StatCornerSimple := by
  intro K _ _ d _ _ m c P e hP he hblk
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  obtain ⟨f, hf⟩ : ∃ f, f = P * e * P⁻¹ := ⟨_, rfl⟩
  rw [← hf] at hblk
  have hff : f * f = f := by
    have : P * e * P⁻¹ * (P * e * P⁻¹) = P * (e * (P⁻¹ * P) * e) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [hf, this, hPP', Matrix.mul_one, he]
  have hef : e = P⁻¹ * f * P := by
    have : P⁻¹ * (P * e * P⁻¹) * P = (P⁻¹ * P) * e * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    rw [hf, this, hPP', Matrix.one_mul, Matrix.mul_one]
  let σ : (Σ i, {a // c a = i}) ≃ d := Equiv.sigmaFiberEquiv c
  have hfb : f.submatrix σ σ = Matrix.blockDiagonal' (fun i => f.toSquareBlock c i) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst h
      rw [Matrix.blockDiagonal'_apply_eq]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      exact hblk _ _ (by show c a.1 ≠ c b.1; rw [a.2, b.2]; exact h)
  have hidem : ∀ i, f.toSquareBlock c i * f.toSquareBlock c i = f.toSquareBlock c i := by
    have h1 : Matrix.blockDiagonal' (fun i => f.toSquareBlock c i * f.toSquareBlock c i) =
        Matrix.blockDiagonal' (fun i => f.toSquareBlock c i) := by
      rw [Matrix.blockDiagonal'_mul, ← hfb, Matrix.submatrix_mul_equiv, hff]
    intro i
    exact congrFun (Matrix.blockDiagonal'_injective h1) i
  choose S hS1 hS2 U W hUW hWU using fun i => idem_factor (f.toSquareBlock c i) (hidem i)
  let v : (Σ i, S i) ↪ K :=
    ((Fintype.equivFin (Σ i, S i)).toEmbedding.trans Fin.valEmbedding).trans (Infinite.natEmbedding K)
  let U0 : Matrix d (Σ i, S i) K := (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _)
  let W0 : Matrix (Σ i, S i) d K := (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm
  have hU0W0 : U0 * W0 = f := by
    show (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _) *
      (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm = f
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, funext hUW, ← hfb]
    ext a b
    simp
  have hW0U0 : W0 * U0 = 1 := by
    show (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm *
      (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _) = 1
    have h1 : (fun i => W i * U i) = 1 := funext hWU
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, h1, Matrix.blockDiagonal'_one]
    exact Matrix.submatrix_one_equiv _
  have hB : U0 * Matrix.diagonal v * W0 = (Matrix.blockDiagonal' (fun i =>
      U i * Matrix.diagonal (fun s => v ⟨i, s⟩) * W i)).submatrix σ.symm σ.symm := by
    rw [Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_diagonal]
    ext a b
    rfl
  refine ⟨P⁻¹ * (U0 * Matrix.diagonal v * W0) * P, ?_, ?_⟩
  · intro a b hab
    have h1 : P * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * P⁻¹ =
        (P * P⁻¹) * (U0 * Matrix.diagonal v * W0) * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    rw [h1, hPP, Matrix.one_mul, Matrix.mul_one, hB]
    show Matrix.blockDiagonal' (fun i => U i * Matrix.diagonal (fun s => v ⟨i, s⟩) * W i)
      ⟨c a, ⟨a, rfl⟩⟩ ⟨c b, ⟨b, rfl⟩⟩ = 0
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hab
  · have h1 : e * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * e =
        (P⁻¹ * U0) * Matrix.diagonal v * (W0 * P) := by
      have h2 : P⁻¹ * f * P * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * (P⁻¹ * f * P) =
          P⁻¹ * (f * (P * P⁻¹) * (U0 * Matrix.diagonal v * W0) * (P * P⁻¹) * f) * P := by
        simp only [Matrix.mul_assoc]
      have h3 : U0 * W0 * (U0 * Matrix.diagonal v * W0) * (U0 * W0) =
          U0 * ((W0 * U0) * Matrix.diagonal v * (W0 * U0)) * W0 := by
        simp only [Matrix.mul_assoc]
      rw [hef, h2, hPP, Matrix.mul_one, Matrix.mul_one, ← hU0W0, h3, hW0U0, Matrix.one_mul,
        Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    have h4 : (P⁻¹ * U0) * (W0 * P) = e := by
      have : (P⁻¹ * U0) * (W0 * P) = P⁻¹ * (U0 * W0) * P := by simp only [Matrix.mul_assoc]
      rw [this, hU0W0, ← hef]
    have h5 : (W0 * P) * (P⁻¹ * U0) = 1 := by
      have : (W0 * P) * (P⁻¹ * U0) = W0 * (P * P⁻¹) * U0 := by simp only [Matrix.mul_assoc]
      rw [this, hPP, Matrix.mul_one, hW0U0]
    rw [h1, blockPoly_corner e _ _ h4 h5, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr v.injective

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

theorem x0 : DensityPointExists := density_point_of_corner_simple density cornerSimple

theorem bridge : StatBridge := by
  intro O _ _ X T d _ _ G _ r π eB heB hid m jj a h c
  have hx : ∀ x, eB x * eB x = eB x := fun x => congrFun hid x
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (fun x => c • ∑ i, jj i x • (eB x * a i x * eB x)) =
        c • ∑ i, (fun x => jj i x • (eB * a i * eB) x) := by
      funext x; simp [Finset.sum_apply]
    rw [h1]
    refine (spanSub T r).smul_mem ((spanSub T r).sum_mem fun i _ => ?_) c
    have h2 : (fun x => jj i x • (eB * a i * eB) x) = term r (jj i) 1 * (eB * a i * eB) := by
      funext x; simp [term]
    rw [h2]
    exact mul_mem_tSpan T r (term_mem T r (h i).1 1)
      (mul_mem_tSpan T r (mul_mem_tSpan T r heB (h i).2.2) heB)
  · funext x
    simp only [Pi.mul_apply, Matrix.mul_smul, Finset.mul_sum, ← mul_assoc, hx]
  · funext x
    simp only [Pi.mul_apply, Matrix.smul_mul, Finset.sum_mul, mul_assoc, hx]
  · simp [(h _).2.1]

theorem bcSpan : StatBcSpan := by
  intro O O' _ _ _ X T
  let φ : (X → O) →+* (X → O') := (algebraMap O O').compLeft X
  have h1 : ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O))) =
      ((T.toSubsemiring.toSubmonoid.map φ.toMonoidHom : Submonoid (X → O')) : Set (X → O')) := rfl
  have h2 := Algebra.adjoin_eq_span O' ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O)))
  have h3 : (bcT O' T : Set (X → O')) = (Subalgebra.toSubmodule (bcT O' T) : Set (X → O')) := rfl
  rw [h3]
  unfold bcT
  rw [h2, h1, Submonoid.closure_eq]

theorem mem_bcT {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {X : Type}
    (T : Subalgebra O (X → O)) {f : X → O} (hf : f ∈ T) :
    (fun x => algebraMap O O' (f x)) ∈ bcT O' T :=
  Algebra.subset_adjoin ⟨f, hf, rfl⟩

theorem bcLocal : StatBcLocal := by
  intro O O' _ _ _ _ _ _ X _ _ T hT
  have hres : ∀ f ∈ bcT O' T, ∀ x y : X,
      IsLocalRing.residue O' (f x) = IsLocalRing.residue O' (f y) := by
    intro f hf x y
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨f0, hf0, rfl⟩ := hf
      have h := resConst O X T hT f0 hf0 x y
      have h2 := congrArg (IsLocalRing.ResidueField.map (algebraMap O O')) h
      exact h2
    | algebraMap c => rfl
    | add f g _ _ hf hg => simp only [Pi.add_apply, map_add, hf, hg]
    | mul f g _ _ hf hg => simp only [Pi.mul_apply, map_mul, hf, hg]
  have : Algebra.IsIntegral O' (X → O') := inferInstance
  have : Algebra.IsIntegral (bcT O' T) (X → O') := Algebra.IsIntegral.tower_top O'
  have : FaithfulSMul (bcT O' T) (X → O') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  have hloc : IsLocalHom (algebraMap (bcT O' T) (X → O')) := inferInstance
  obtain ⟨π⟩ := ‹Nonempty X›
  have hunit : ∀ a : bcT O' T, IsUnit (a.1 π) → IsUnit a := by
    intro a ha
    refine hloc.map_nonunit a ?_
    show IsUnit a.1
    rw [Pi.isUnit_iff]
    intro x
    have h1 : IsLocalRing.residue O' (a.1 x) ≠ 0 := by
      rw [hres a.1 a.2 x π]
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr ha
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h1
  have : Nontrivial (bcT O' T) := inferInstance
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (a.1 π) with h | h
  · exact Or.inl (hunit a h)
  · exact Or.inr (hunit (1 - a) h)

theorem absIrr_of_span {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {G : Type}
    (ρ : G → Matrix n n k) (h : ∀ i j, Matrix.single i j (1 : k) ∈ Submodule.span k (Set.range ρ)) :
    AbsIrr ρ := by
  constructor
  · intro W hW
    have hall : ∀ A ∈ Submodule.span k (Set.range ρ), ∀ v ∈ W, A.mulVec v ∈ W := by
      intro A hA
      induction hA using Submodule.span_induction with
      | mem A hA => obtain ⟨g, rfl⟩ := hA; exact hW g
      | zero => intro v _; rw [Matrix.zero_mulVec]; exact W.zero_mem
      | add A B _ _ hA hB => intro v hv; rw [Matrix.add_mulVec]; exact W.add_mem (hA v hv) (hB v hv)
      | smul c A _ hA => intro v hv; rw [Matrix.smul_mulVec]; exact W.smul_mem c (hA v hv)
    by_cases hb : W = ⊥
    · exact Or.inl hb
    right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp hb
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hc
      exact hv0 (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
    have hs : ∀ i, Pi.single i (1 : k) ∈ W := by
      intro i
      have h1 := W.smul_mem (v j)⁻¹ (hall _ (h i j) v hv)
      have h2 : (v j)⁻¹ • (Matrix.single i j (1 : k)).mulVec v = Pi.single i (1 : k) := by
        funext a
        by_cases ha : a = i
        · subst ha
          simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hj]
        · simp [Matrix.mulVec, dotProduct, ha, Ne.symm ha]
      rwa [h2] at h1
    refine eq_top_iff.mpr fun w _ => ?_
    have h3 : w = ∑ i, w i • Pi.single i (1 : k) := by
      funext a
      simp [Finset.sum_apply, Pi.single_apply]
    rw [h3]
    exact W.sum_mem fun i _ => W.smul_mem _ (hs i)
  · intro M hM
    have hall : ∀ A ∈ Submodule.span k (Set.range ρ), M * A = A * M := by
      intro A hA
      induction hA using Submodule.span_induction with
      | mem A hA => obtain ⟨g, rfl⟩ := hA; exact hM g
      | zero => simp
      | add A B _ _ hA hB => rw [mul_add, add_mul, hA, hB]
      | smul c A _ hA => rw [Matrix.mul_smul, Matrix.smul_mul, hA]
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
      (fun i j => (hall _ (h i j)).symm)
    exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem absIrrExt : StatAbsIrrExt := by
  intro k k' _ _ f n _ _ G _ ρ hρ
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨fun W _ => Or.inl (Subsingleton.elim _ _), fun M _ => ⟨0, Subsingleton.elim _ _⟩⟩
  have hspan := burnsideMat k n G ρ hρ
  have hmap : ∀ A ∈ Submodule.span k (Set.range ρ),
      A.map f ∈ Submodule.span k' (Set.range fun g => (ρ g).map f) := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA => obtain ⟨g, rfl⟩ := hA; exact Submodule.subset_span ⟨g, rfl⟩
    | zero => rw [Matrix.map_zero f f.map_zero]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [Matrix.map_add f f.map_add]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA =>
      have h1 : (c • A).map f = f c • A.map f := by
        ext i j; simp
      rw [h1]; exact Submodule.smul_mem _ _ hA
  refine absIrr_of_span _ fun i j => ?_
  have h1 := hmap (Matrix.single i j (1 : k)) (hspan ▸ Submodule.mem_top)
  have h2 : (Matrix.single i j (1 : k)).map f = Matrix.single i j (1 : k') := by
    ext a b
    by_cases hab : i = a ∧ j = b <;> simp [hab]
  rwa [h2] at h1

theorem bcRank : StatBcRank := by
  intro O _ _ F F' _ _ f f' d _ _ e he
  obtain ⟨P, Q, dd, hdd, hPQ, hQP, rfl⟩ := idem_normal_form e he
  rw [rank_map_conj f' P Q dd hdd hPQ hQP, rank_map_conj f P Q dd hdd hPQ hQP]

theorem bcSplit : StatBcSplit := by
  intro K _ d _ _ e a t he hea hae hrk
  obtain ⟨S, _, _, U, W, hUW, hWU⟩ := idem_factor e he
  have hcard : Fintype.card S = t := by
    rw [← hrk, ← hUW]
    apply le_antisymm
    · calc Fintype.card S = (1 : Matrix S S K).rank := (Matrix.rank_one).symm
        _ = (W * (U * W) * U).rank := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hWU, Matrix.mul_one, hWU]
        _ ≤ (U * W).rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width U)
  have ha : a = U * (W * a * U) * W := by
    calc a = e * a * e := by rw [hea, hae]
      _ = _ := by rw [← hUW]; simp only [Matrix.mul_assoc]
  have hpoly : blockPoly e a = (W * a * U).charpoly := by
    conv_lhs => rw [ha, ← hUW]
    exact blockPoly_factor U W hWU _
  have hmon : (blockPoly e a).Monic := hpoly ▸ Matrix.charpoly_monic _
  have hdeg : (blockPoly e a).natDegree = t := by
    rw [hpoly, Matrix.charpoly_natDegree_eq_dim, hcard]
  refine ⟨hmon, hdeg, fun hsep hspl => ?_⟩
  set Q := blockPoly e a with hQ
  have hnd : Q.roots.Nodup := Polynomial.nodup_roots hsep
  have hc : Q.roots.toFinset.card = t := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← hspl.natDegree_eq_card_roots, hdeg]
  let en := Q.roots.toFinset.equivFinOfCardEq hc
  refine ⟨fun i => (en.symm i).1, fun i j hij => en.symm.injective (Subtype.ext hij), ?_⟩
  rw [Equiv.prod_comp en.symm (fun z : Q.roots.toFinset => Polynomial.X - Polynomial.C z.1),
    Finset.prod_coe_sort Q.roots.toFinset (fun z => Polynomial.X - Polynomial.C z)]
  conv_lhs => rw [hspl.eq_prod_roots_of_monic hmon]
  rw [Finset.prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

theorem bcM_mem {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {X d G : Type} [Fintype d]
    [DecidableEq d] [Group G] (T : Subalgebra O (X → O)) (r : G →* (X → Matrix d d O))
    {a : X → Matrix d d O} (ha : a ∈ tSpan T r) : bcM O' a ∈ tSpan (bcT O' T) (bcR O' r) := by
  obtain ⟨S, c, hc, rfl⟩ := ha
  refine ⟨S, fun g x => algebraMap O O' (c g x), fun g => mem_bcT O' T (hc g), ?_⟩
  funext x; ext i j
  simp [bcM, bcR, Finset.sum_apply, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun g _ => (Algebra.smul_def _ _).symm

theorem bcM_mul {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {X d : Type} [Fintype d]
    (a b : X → Matrix d d O) : bcM O' (a * b) = bcM O' a * bcM O' b := by
  funext x
  simp [bcM, Matrix.map_mul]

theorem sep_ext {O : Type} [CommRing O] [IsDomain O] {F : Type} [Field F] (f : O →+* F)
    (hf : Function.Injective f) (P : Polynomial O)
    (h : (P.map (algebraMap O (FractionRing O))).Separable) : (P.map f).Separable := by
  have hκ : (IsFractionRing.lift hf : FractionRing O →+* F).comp (algebraMap O (FractionRing O)) = f :=
    RingHom.ext (IsFractionRing.lift_algebraMap hf)
  rw [← hκ, ← Polynomial.map_map, Polynomial.separable_map]
  exact h

set_option maxHeartbeats 1000000 in
theorem stageC : StatStageC := by
  intro O O' _ _ _ _ _ _ _ _ _ e he X _ T d _ _ G _ r π t bl χ₁ ε hP hA eB e₁ hI g₀ s hsm hes hse hsπ
    hsep hspl
  obtain ⟨hloc, hpts, hG1, hbd, hc1, hχ⟩ := hP
  obtain ⟨heBm, he1m, heBB, he11, heB1, he1B, hrkB, hrk1, heBπ, he1π⟩ := hI
  let j : O →+* O' := algebraMap O O'
  have hj : Function.Injective j := FaithfulSMul.algebraMap_injective O O'
  have hjl : IsLocalHom (algebraMap O O') := inferInstance
  let ι : O →+* FractionRing O := algebraMap O (FractionRing O)
  let ι' : O' →+* FractionRing O' := algebraMap O' (FractionRing O')
  have hι' : Function.Injective ι' := IsFractionRing.injective O' (FractionRing O')
  have : Nonempty X := ⟨π⟩
  refine ⟨⟨bcLocal O O' X T hloc, ?_, ?_, ?_, hc1, ?_⟩, ?_, ⟨bcM_mem O' T r heBm, bcM_mem O' T r he1m,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨bcM_mem O' T r hsm, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y hxy
    obtain ⟨f, hf, hne⟩ := hpts x y hxy
    exact ⟨_, mem_bcT O' T hf, fun h => hne (hj h)⟩
  · intro g k
    have h1 : (fun x => (Matrix.charpolyRev (bcR O' r g x)).coeff k) =
        fun x => algebraMap O O' ((Matrix.charpolyRev (r g x)).coeff k) := by
      funext x
      show (Matrix.charpolyRev ((r g x).map j)).coeff k = _
      rw [← charpolyRev_map, Polynomial.coeff_map]
    rw [h1]
    exact mem_bcT O' T (hG1 g k)
  · intro g a b hab
    show j (r g π a b) = 0
    rw [hbd g a b hab, map_zero]
  · intro g a ha
    show j (r g π a a) = _
    rw [hχ g a ha, map_mul]
    simp [bcChar, j]
  ·
    let ρ0 : G →* Matrix {a // bl a = 0} {a // bl a = 0} (IsLocalRing.ResidueField O) :=
      { toFun := fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)
        map_one' := by
          rw [map_one]
          ext a b
          by_cases h : a = b
          · subst h; simp [Matrix.toSquareBlock_def]
          · have h' : a.1 ≠ b.1 := fun e => h (Subtype.ext e)
            simp [Matrix.toSquareBlock_def, Matrix.one_apply, h, h']
        map_mul' := fun g h => by
          rw [map_mul, Pi.mul_apply, blk_mul bl (hbd g) 0, Matrix.map_mul] }
    exact absIrrExt _ _ (IsLocalRing.ResidueField.map (algebraMap O O')) _ G ρ0 hA
  · rw [← bcM_mul, heBB]
  · rw [← bcM_mul, he11]
  · rw [← bcM_mul, heB1]; funext x; simp [bcM]
  · rw [← bcM_mul, he1B]; funext x; simp [bcM]
  · intro x
    show (((eB x).map j).map ι').rank = t
    rw [Matrix.map_map, ← hrkB x]
    exact bcRank O _ _ ι (ι'.comp j) d (eB x) (congrFun heBB x)
  · intro x
    show (((e₁ x).map j).map ι').rank = 1
    rw [Matrix.map_map, ← hrk1 x]
    exact bcRank O _ _ ι (ι'.comp j) d (e₁ x) (congrFun he11 x)
  · show (eB π).map j = _
    rw [heBπ]
    ext a b
    by_cases hab : a = b
    · subst hab; by_cases h0 : bl a = 0 <;> simp [h0]
    · simp [Matrix.diagonal_apply_ne _ hab]
  · intro a b hab
    show j (e₁ π a b) = 0
    rw [he1π a b hab, map_zero]
  · rw [← bcM_mul, hes]
  · rw [← bcM_mul, hse]
  · show (s π).map j = 0
    rw [hsπ]; ext a b; simp
  · intro x
    let X0 : Matrix d d O := eB x * r g₀ x * eB x + s x
    have hX0 : (bcM O' eB x * bcR O' r g₀ x * bcM O' eB x + bcM O' s x) = X0.map j := by
      show (eB x).map j * (r g₀ x).map j * (eB x).map j + (s x).map j = _
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add j j.map_add]
    have hpoly : blockPoly ((bcM O' eB x).map ι') ((X0.map j).map ι') =
        (blockPoly (eB x) X0).map (ι'.comp j) := by
      show blockPoly (((eB x).map j).map ι') _ = _
      rw [Matrix.map_map, Matrix.map_map]
      exact (blockPoly_map (ι'.comp j) _ _).symm
    have hinj : Function.Injective (ι'.comp j) := hι'.comp hj
    have hsep' : ((blockPoly (eB x) X0).map (ι'.comp j)).Separable := by
      refine sep_ext _ hinj _ ?_
      rw [blockPoly_map]
      exact hsep x
    have hmm : ∀ u v w : Matrix d d O, u * v = w →
        (u.map j).map ι' * (v.map j).map ι' = (w.map j).map ι' := by
      intro u v w h
      rw [← Matrix.map_mul, ← Matrix.map_mul, h]
    have hbb : eB x * eB x = eB x := congrFun heBB x
    have hbs : eB x * s x = s x := congrFun hes x
    have hsb : s x * eB x = s x := congrFun hse x
    have heX0 : eB x * X0 = X0 := by
      show eB x * (eB x * r g₀ x * eB x + s x) = _
      rw [mul_add, ← mul_assoc, ← mul_assoc, hbb, hbs]
    have hX0e : X0 * eB x = X0 := by
      show (eB x * r g₀ x * eB x + s x) * eB x = _
      rw [add_mul, mul_assoc, hbb, hsb]
    have hrk : ((bcM O' eB x).map ι').rank = t := by
      show (((eB x).map j).map ι').rank = t
      rw [Matrix.map_map, ← hrkB x]
      exact bcRank O _ _ ι (ι'.comp j) d (eB x) (congrFun heBB x)
    obtain ⟨-, -, h3⟩ := bcSplit (FractionRing O') d ((bcM O' eB x).map ι') ((X0.map j).map ι') t
      (hmm _ _ _ (congrFun heBB x)) (hmm _ _ _ heX0) (hmm _ _ _ hX0e) hrk
    rw [hX0]
    exact h3 (hpoly ▸ hsep') (hpoly ▸ hspl x)
  · intro Z
    exact vccBaseChange O O' e he X T (bcT O' T) (bcSpan O O' X T) Z π

theorem deltaO_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
    [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)}
    {r₀ : G →* (X → Matrix d d O)} {π : X} {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O}
    {D : RingData O X d G t bl} (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) :
    D.δO = ∏ i ∈ Finset.Ioo 0 t, ((χ₁ g₀ : O) - (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)) := by
  obtain ⟨-, -, -, -, -, hrr, -⟩ := hD
  have h2 : D.δO = ∏ i ∈ Finset.Ioo 0 t,
      ((D.rr 0 : D.X' → O) D.π' - (D.rr i : D.X' → O) D.π') := by
    show ((Pi.evalRingHom (fun _ : D.X' => O) D.π').comp D.T'.val.toRingHom) D.δ = _
    unfold RingData.δ
    rw [map_prod]; rfl
  rw [h2]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_Ioo] at hi
  rw [hrr 0 (by omega), hrr i hi.2]
  simp

theorem deltaBc : StatDeltaBc := by
  intro O O' _ _ _ _ _ _ _ e he
  refine ⟨?_, fun ℓ => ?_⟩
  · intro X d G _ _ _ t bl T r π χ₁ ε g₀ eB e₁ s D' hD'
    have h1 : D'.δO = algebraMap O O'
        (∏ i ∈ Finset.Ioo 0 t, ((χ₁ g₀ : O) - (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O))) := by
      rw [deltaO_eq hD', map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [bcChar]
    exact ⟨h1, by rw [h1, he]⟩
  · rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, ← he, map_natCast (algebraMap O O')]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end
