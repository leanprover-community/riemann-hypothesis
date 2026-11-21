import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import BuildAid.ForwardExisting

section
section
open Module TopologicalSpace GlobalTheory.FlagPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPts

open MvPolynomial

variable {k : Type} [Field k] {J : Type}

def affPtsVanIdeal (x : AffPts k J) : PrimeSpectrum (MvPolynomial J k) :=
  ⟨RingHom.ker (MvPolynomial.eval (show J → k from x)), RingHom.ker_isPrime _⟩

theorem mem_affPtsVanIdeal_preimage_basicOpen (p : MvPolynomial J k) (x : AffPts k J) :
    x ∈ affPtsVanIdeal ⁻¹' (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial J k))) ↔
      MvPolynomial.eval x p ≠ 0 := by
  simp [affPtsVanIdeal, PrimeSpectrum.mem_basicOpen]

theorem isInducing_affPtsVanIdeal : Topology.IsInducing (affPtsVanIdeal (k := k) (J := J)) := by
  rw [Topology.isInducing_iff, PrimeSpectrum.isTopologicalBasis_basic_opens.eq_generateFrom,
    induced_generateFrom_eq]
  show TopologicalSpace.generateFrom _ = _
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨_, ⟨p, rfl⟩, by ext x; exact mem_affPtsVanIdeal_preimage_basicOpen p x⟩
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, by ext x; exact mem_affPtsVanIdeal_preimage_basicOpen p x⟩

theorem topologicalKrullDim_affPts_le [Fintype J] :
    topologicalKrullDim (AffPts k J) ≤ (Fintype.card J : ℕ) := by
  refine isInducing_affPtsVanIdeal.topologicalKrullDim_le.trans ?_
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card]
  simp

theorem isTopologicalBasis_affPts :
    IsTopologicalBasis (Set.preimage (affPtsVanIdeal (k := k) (J := J)) ''
      Set.range fun p : MvPolynomial J k ↦ (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial J k)))) :=
  PrimeSpectrum.isTopologicalBasis_basic_opens.isInducing isInducing_affPtsVanIdeal

theorem isIrreducible_univ_affPts [Infinite k] : IsIrreducible (Set.univ : Set (AffPts k J)) := by
  refine ⟨⟨fun _ ↦ 0, trivial⟩, ?_⟩
  rintro u v hu hv ⟨x, -, hx⟩ ⟨y, -, hy⟩
  obtain ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, hxp, hpu⟩ := isTopologicalBasis_affPts.exists_subset_of_mem_open hx hu
  obtain ⟨_, ⟨_, ⟨q, rfl⟩, rfl⟩, hyq, hqv⟩ := isTopologicalBasis_affPts.exists_subset_of_mem_open hy hv
  rw [mem_affPtsVanIdeal_preimage_basicOpen] at hxp hyq
  have hp : p ≠ 0 := by rintro rfl; simp at hxp
  have hq : q ≠ 0 := by rintro rfl; simp at hyq
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  obtain ⟨z, hz⟩ : ∃ z : AffPts k J, MvPolynomial.eval z (p * q) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hpq (MvPolynomial.funext fun z ↦ by simpa using h z)
  rw [map_mul] at hz
  refine ⟨z, trivial, hpu ?_, hqv ?_⟩
  · exact (mem_affPtsVanIdeal_preimage_basicOpen p z).2 (left_ne_zero_of_mul hz)
  · exact (mem_affPtsVanIdeal_preimage_basicOpen q z).2 (right_ne_zero_of_mul hz)

open Classical in

def affPtsProj (S : Set J) (x : AffPts k J) : AffPts k J := fun j ↦ if j ∈ S then x j else 0

open Classical in
theorem eval_affPtsProj (S : Set J) (x : AffPts k J) (p : MvPolynomial J k) :
    MvPolynomial.eval (affPtsProj S x) p =
      MvPolynomial.eval x (MvPolynomial.bind₁ (fun j ↦ if j ∈ S then (X j : MvPolynomial J k) else 0) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.bind₁_C_right]
    exact (MvPolynomial.eval_C (f := affPtsProj S x) a).trans (MvPolynomial.eval_C (f := x) a).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.bind₁_X_right]
    congr 1
    rw [MvPolynomial.eval_X (f := affPtsProj S x)]
    by_cases hj : j ∈ S
    · rw [if_pos hj, MvPolynomial.eval_X (f := x)]
      show (if j ∈ S then x j else 0) = x j
      rw [if_pos hj]
    · rw [if_neg hj, map_zero]
      show (if j ∈ S then x j else 0) = 0
      rw [if_neg hj]

theorem continuous_affPtsProj (S : Set J) : Continuous (affPtsProj (k := k) S) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨p, rfl⟩
  classical
  convert isOpen_affPts_ne_zero (k := k)
    (MvPolynomial.bind₁ (fun j ↦ if j ∈ S then (X j : MvPolynomial J k) else 0) p) using 1
  ext x
  show MvPolynomial.eval (affPtsProj S x) p ≠ 0 ↔ _
  rw [eval_affPtsProj]
  rfl

theorem range_affPtsProj (S : Set J) :
    Set.range (affPtsProj (k := k) S) = {x : AffPts k J | ∀ j, j ∉ S → x j = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ j hj
    simp [affPtsProj, hj]
  · intro hx
    refine ⟨x, funext fun j ↦ ?_⟩
    by_cases hj : j ∈ S
    · simp [affPtsProj, hj]
    · simp [affPtsProj, hj, hx j hj]

theorem isClosed_coordSubspace (S : Set J) : IsClosed {x : AffPts k J | ∀ j, j ∉ S → x j = 0} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦ ?_
  rw [← isOpen_compl_iff]
  have : ({x : AffPts k J | x j = 0}ᶜ : Set (AffPts k J)) =
      {x : AffPts k J | MvPolynomial.eval x (X j : MvPolynomial J k) ≠ 0} := by
    ext x
    exact Iff.not (Eq.to_iff (congrArg (· = (0 : k)) (MvPolynomial.eval_X (f := x) j).symm))
  rw [this]
  exact isOpen_affPts_ne_zero _

def coordSubspace [Infinite k] (S : Set J) : IrreducibleCloseds (AffPts k J) :=
  ⟨{x : AffPts k J | ∀ j, j ∉ S → x j = 0},
    by
      rw [← range_affPtsProj, ← Set.image_univ]
      exact isIrreducible_univ_affPts.image _ (continuous_affPtsProj S).continuousOn,
    isClosed_coordSubspace S⟩

theorem le_topologicalKrullDim_affPts [Infinite k] [Fintype J] :
    ((Fintype.card J : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (AffPts k J) := by
  classical
  set e := Fintype.equivFin J
  set n := Fintype.card J
  let f : Fin (n + 1) → IrreducibleCloseds (AffPts k J) :=
    fun m ↦ coordSubspace {j | (e j : ℕ) < m}
  have hf : StrictMono f := by
    intro a b hab
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun x hx j hj ↦ hx j fun h ↦ hj ?_, ?_⟩
    · exact lt_trans (Set.mem_setOf.1 h) hab
    have ha : (a : ℕ) < n := lt_of_lt_of_le hab (Nat.lt_succ_iff.1 b.2)
    refine ⟨fun j ↦ if (e j : ℕ) = a then 1 else 0, ?_, ?_⟩
    · intro j hj
      have : (e j : ℕ) ≠ a := fun h ↦ hj (by simp only [Set.mem_setOf_eq, h]; exact hab)
      simp [this]
    · intro hx
      have := hx (e.symm ⟨a, ha⟩) (by simp)
      simp at this
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk n f hf)

theorem topologicalKrullDim_affPts_eq_card :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J],
      topologicalKrullDim (AffPts k J) = (Fintype.card J : ℕ) := by
  intro k _ _ J _
  haveI : Infinite k := inferInstance
  exact le_antisymm topologicalKrullDim_affPts_le le_topologicalKrullDim_affPts

end GlobalTheory.FlagPts
end
end

open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_affine_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J], topologicalKrullDim (AffPts k J) = (Fintype.card J : ℕ) := by
  atlas_forward_decl GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card
end

section
section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace GlobalTheory.FlagPts

namespace GlobalTheory.FlagPts.CellCont

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def polyMat (i : ι) :
    Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) (MvPolynomial (CellIdx k V) k) :=
  fun a c => if a = c then 1 else if h : c < a then MvPolynomial.X ⟨i, (a, c), h⟩ else 0

theorem map_polyMat (u : AffPts k (CellIdx k V)) (i : ι) :
    (polyMat (k := k) (V := V) i).map (MvPolynomial.eval u) = uniMat u i := by
  ext a c
  simp only [Matrix.map_apply, polyMat, uniMat]
  split_ifs
  · exact map_one _
  · exact MvPolynomial.eval_X (f := u) _
  · exact map_zero _

theorem eval_adjugate_polyMat (u : AffPts k (CellIdx k V)) (i : ι) (a c : Fin (finrank k (V i))) :
    MvPolynomial.eval u ((polyMat (k := k) (V := V) i).adjugate a c) = (uniMat u i).adjugate a c := by
  have := RingHom.map_adjugate (MvPolynomial.eval u) (polyMat (k := k) (V := V) i)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_polyMat] at this
  exact congrFun (congrFun this a) c

def polyOnCell (b : Frames k V) : Subalgebra k (Frames k V → k) where
  carrier := {f | ∃ P : MvPolynomial (CellIdx k V) k, ∀ u, f (cellFrame b u) = MvPolynomial.eval u P}
  mul_mem' := by
    rintro f g ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P * Q, fun u => by simp [hP, hQ]⟩
  add_mem' := by
    rintro f g ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun u => by simp [hP, hQ]⟩
  algebraMap_mem' := fun c => ⟨MvPolynomial.C c, fun u => (MvPolynomial.eval_C (f := u) c).symm⟩

theorem dual_mem_polyOnCell (b : Frames k V) (i : ι) (φ : Dual k (V i)) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => φ (b' i a)) ∈ polyOnCell b :=
  ⟨∑ l, MvPolynomial.C (φ (b i l)) * polyMat (k := k) (V := V) i l a, fun u => by
    simp only [cellFrame_apply, map_sum, map_smul, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [MvPolynomial.eval_C (f := u), ← map_polyMat u i, Matrix.map_apply, mul_comm]⟩

theorem repr_cellFrame (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) (v : V i) :
    (cellFrame b u i).repr v = (uniMat u i).adjugate.mulVec ((b i).repr v) := by
  have hu : IsUnit (uniMat u i).det := by rw [det_uniMat]; exact isUnit_one
  have hM : (uniMat u i)⁻¹ = (uniMat u i).adjugate := by
    rw [Matrix.inv_def, det_uniMat]; simp
  rw [← hM]
  have he : (Matrix.toLinearEquiv (b i) (uniMat u i) hu).symm v =
      Matrix.toLin (b i) (b i) (uniMat u i)⁻¹ v := by
    rw [LinearEquiv.symm_apply_eq, Matrix.toLinearEquiv_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul,
      Matrix.mul_nonsing_inv _ hu, Matrix.toLin_one]
    rfl
  simp only [cellFrame, Basis.map_repr, LinearEquiv.trans_apply]
  rw [he, ← LinearMap.toMatrix_mulVec_repr (b i) (b i), LinearMap.toMatrix_toLin]

theorem repr_mem_polyOnCell (b : Frames k V) (i : ι) (v : V i) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => (b' i).repr v a) ∈ polyOnCell b :=
  ⟨∑ c, (polyMat (k := k) (V := V) i).adjugate a c * MvPolynomial.C ((b i).repr v c), fun u => by
    show (cellFrame b u i).repr v a = _
    rw [repr_cellFrame]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MvPolynomial.eval_C (f := u), eval_adjugate_polyMat]⟩

theorem regFns_le_polyOnCell (b : Frames k V) : regFns k V ≤ polyOnCell b := by
  refine Algebra.adjoin_le ?_
  rintro f (⟨i, φ, a, rfl⟩ | ⟨i, v, a, rfl⟩)
  · exact dual_mem_polyOnCell b i φ a
  · exact repr_mem_polyOnCell b i v a

theorem continuous_cellFrame (b : Frames k V) : Continuous (cellFrame b) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨P, hP⟩ := regFns_le_polyOnCell b hf
  have : cellFrame b ⁻¹' {b' | f b' ≠ 0} = {u | MvPolynomial.eval u P ≠ 0} := by
    refine Set.ext fun u => ?_
    show f (cellFrame b u) ≠ 0 ↔ _
    rw [hP]
    rfl
  rw [this]
  exact isOpen_affPts_ne_zero P

end GlobalTheory.FlagPts.CellCont

namespace GlobalTheory.FlagPts

theorem continuous_cellMap : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), Continuous (cellMap b) := by
  intro k _ ι _ V _ _ _ b
  exact continuous_coinduced_rng.comp (CellCont.continuous_cellFrame b)

end GlobalTheory.FlagPts
end
end

open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_cellMap' : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), Continuous (cellMap b) := by
  atlas_forward_decl GlobalTheory.FlagPts.continuous_cellMap
end

section
section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

theorem toMatrix_cellFrame {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) :
    (b i).toMatrix (cellFrame b u i) = uniMat u i := by
  ext a c
  rw [Basis.toMatrix_apply, cellFrame_apply, map_sum]
  simp [Finsupp.single_apply]

theorem cellMap_injective (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) :
    Function.Injective (cellMap b) := by
  intro u u' h
  have key : ∀ i, uniMat u i = uniMat u' i := by
    intro i
    have hflag : (cellFrame b u i).flag = (cellFrame b u' i).flag :=
      congrArg FullFlag.sub (congrFun h i)
    set B := cellFrame b u i
    set B' := cellFrame b u' i
    set Y := B.toMatrix B'
    have hmul : uniMat u i * Y = uniMat u' i := by
      rw [← toMatrix_cellFrame b u i, ← toMatrix_cellFrame b u' i, Basis.toMatrix_mul_toMatrix]
    have hup : ∀ j c, c < j → Y j c = 0 := by
      intro j c hcj
      have hm : B' c ∈ B'.flag c.succ := B'.self_mem_flag Fin.castSucc_lt_succ
      rw [← hflag] at hm
      exact (mem_basis_flag_iff B _ _).1 hm j (Fin.succ_le_castSucc_iff.mpr hcj)
    have hdet : IsUnit (uniMat u i).det := by rw [det_uniMat]; exact isUnit_one
    have hY : Y = (uniMat u i)⁻¹ * uniMat u' i := by
      rw [← hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have hlow : ∀ j c, j < c → Y j c = 0 := by
      letI := (uniMat u i).invertibleOfIsUnitDet hdet
      have h1 := Matrix.blockTriangular_inv_of_blockTriangular (uniMat_blockTriangular u i)
      have h2 := h1.mul (uniMat_blockTriangular u' i)
      intro j c hjc
      rw [hY]
      exact h2 (by simpa using hjc)
    have hdiag : ∀ c, Y c c = 1 := by
      intro c
      have := congrFun (congrFun hmul c) c
      rw [Matrix.mul_apply, Finset.sum_eq_single c, uniMat_apply_self, uniMat_apply_self, one_mul] at this
      · exact this
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hj | hj
        · rw [hlow j c hj, mul_zero]
        · rw [hup j c hj, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    have hY1 : Y = 1 := by
      ext j c
      rcases lt_trichotomy j c with hjc | rfl | hjc
      · rw [hlow j c hjc, Matrix.one_apply_ne hjc.ne]
      · rw [hdiag, Matrix.one_apply_eq]
      · rw [hup j c hjc, Matrix.one_apply_ne hjc.ne']
    rw [← hmul, hY1, Matrix.mul_one]
  funext x
  obtain ⟨i, ⟨a, c⟩, hac⟩ := x
  have := congrFun (congrFun (key i) a) c
  rwa [uniMat_apply_of_lt u i hac, uniMat_apply_of_lt u' i hac] at this

end GlobalTheory.FlagPts
end
end

open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_cellMap : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), Function.Injective (cellMap b) := by
  atlas_forward_decl GlobalTheory.FlagPts.cellMap_injective
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPts

variable {k : Type} [Field k] {n : ℕ}

def leadBlock (P : Matrix (Fin n) (Fin n) k) (m : Fin n) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  P.submatrix (Fin.castLE m.isLt) (Fin.castLE m.isLt)

def leadMinor (P : Matrix (Fin n) (Fin n) k) (m : Fin n) : k := (leadBlock P m).det

def luNum (P : Matrix (Fin n) (Fin n) k) (a m : Fin n) : k :=
  ∑ l : Fin (m + 1), P a (Fin.castLE m.isLt l) * (leadBlock P m).cramer (Pi.single (Fin.last m) 1) l

def luLower (P : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k := fun a m =>
  if a = m then 1 else if m < a then luNum P a m / leadMinor P m else 0

theorem luLower_apply_self (P : Matrix (Fin n) (Fin n) k) (a : Fin n) : luLower P a a = 1 := by
  simp [luLower]

theorem luLower_apply_of_lt (P : Matrix (Fin n) (Fin n) k) {a m : Fin n} (h : m < a) :
    luLower P a m = luNum P a m / leadMinor P m := by
  simp [luLower, h, h.ne']

theorem luLower_lowerTriangular (P : Matrix (Fin n) (Fin n) k) : (luLower P).BlockTriangular OrderDual.toDual :=
  fun a m h => by
    have h' : a < m := by simpa using h
    simp [luLower, h'.ne, not_lt.2 h'.le]

example (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : leadMinor P (Fin.last n) = P.det := by
  simp [leadMinor, leadBlock]

end GlobalTheory.FlagPts
end
end

section
section
set_option autoImplicit false
noncomputable section

open Module TopologicalSpace GlobalTheory.FlagPts

namespace GlobalTheory.FlagPts

theorem exists_pow_mul_eval_mem {k : Type} [Field k] {X J : Type} (R : Subalgebra k (X → k)) (D : X → k) (g : J → X → k) (hD : D ∈ R)
    (hg : ∀ j, D * g j ∈ R) (q : MvPolynomial J k) :
    ∃ N : ℕ, (D ^ N * fun x => MvPolynomial.eval (fun j => g j x) q) ∈ R := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    convert R.algebraMap_mem a using 1
    funext x
    simp
  | add p q hp hq =>
    obtain ⟨N₁, h₁⟩ := hp
    obtain ⟨N₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, ?_⟩
    have : (D ^ (N₁ + N₂) * fun x => MvPolynomial.eval (fun j => g j x) (p + q)) =
        D ^ N₂ * (D ^ N₁ * fun x => MvPolynomial.eval (fun j => g j x) p) +
          D ^ N₁ * (D ^ N₂ * fun x => MvPolynomial.eval (fun j => g j x) q) := by
      funext x
      simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, map_add]
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hD _) h₁) (mul_mem (pow_mem hD _) h₂)
  | mul_X p j hp =>
    obtain ⟨N, h⟩ := hp
    refine ⟨N + 1, ?_⟩
    have : (D ^ (N + 1) * fun x => MvPolynomial.eval (fun j => g j x) (p * MvPolynomial.X j)) =
        (D ^ N * fun x => MvPolynomial.eval (fun j => g j x) p) * (D * g j) := by
      funext x
      simp only [Pi.mul_apply, Pi.pow_apply, map_mul, MvPolynomial.eval_X]
      ring
    rw [this]
    exact mul_mem h (hg j)

theorem flags_apply_eq_cellMap_iff (k : Type) [Field k] (ι : Type) (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (b c : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) :
    c.flags i = cellMap b u i ↔ ((uniMat u i)⁻¹ * (b i).toMatrix (c i)).BlockTriangular id := by
  have hcell : (b i).toMatrix (cellFrame b u i) = uniMat u i := by
    ext a m
    rw [Basis.toMatrix_apply, cellFrame_apply]
    simp [Finsupp.single_apply]
  have h1 : IsUnit ((b i).toMatrix (cellFrame b u i)).det := by rw [hcell, det_uniMat]; exact isUnit_one
  have hchg : (cellFrame b u i).toMatrix (c i) = (uniMat u i)⁻¹ * (b i).toMatrix (c i) := by
    rw [← hcell, ← Basis.toMatrix_mul_toMatrix (b i) (cellFrame b u i) (c i), ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ h1, Matrix.one_mul]
  show FullFlag.ofBasis (c i) = FullFlag.ofBasis (cellFrame b u i) ↔ _
  rw [FullFlag.ofBasis_eq_ofBasis_iff]
  constructor
  · rintro ⟨g, hg, hgc⟩
    rw [← hchg, ← hgc, toMatrix_basisMulGL]
    exact hg
  · intro h
    refine ⟨basisChange (cellFrame b u i) (c i), ?_, basisMulGL_basisChange _ _⟩
    rw [mem_upperTriangularGL]
    intro a m hm
    rw [coe_basisChange, hchg]
    exact h hm

section Reg
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

theorem const_mem_regFns (x : k) : (fun _ : Frames k V => x) ∈ regFns k V := by
  convert (regFns k V).algebraMap_mem x
  rfl

theorem toMatrix_entry_mem_regFns (b : Frames k V) (i : ι) (a l : Fin (finrank k (V i))) :
    (fun c : Frames k V => (b i).toMatrix (c i) a l) ∈ regFns k V :=
  Algebra.subset_adjoin (Or.inl ⟨i, (b i).coord a, l, by funext c; simp [Basis.toMatrix_apply]⟩)

theorem det_mem_regFns {m : ℕ} (M : Frames k V → Matrix (Fin m) (Fin m) k)
    (hM : ∀ a c, (fun x => M x a c) ∈ regFns k V) : (fun x => (M x).det) ∈ regFns k V := by
  have : (fun x => (M x).det) = ∑ σ : Equiv.Perm (Fin m),
      (fun _ : Frames k V => ((Equiv.Perm.sign σ : ℤ) : k)) * ∏ a, fun x => M x (σ a) a := by
    funext x
    simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact Subalgebra.sum_mem _ fun σ _ => mul_mem (const_mem_regFns _) (Subalgebra.prod_mem _ fun a _ => hM _ _)
end Reg

theorem leadMinor_toMatrix_mem_regFns (k : Type) [Field k] (ι : Type) (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (b : Frames k V) (i : ι) (m : Fin (finrank k (V i))) :
    (fun c : Frames k V => leadMinor ((b i).toMatrix (c i)) m) ∈ regFns k V :=
  det_mem_regFns (fun c => leadBlock ((b i).toMatrix (c i)) m) fun _ _ => toMatrix_entry_mem_regFns b i _ _

theorem luNum_toMatrix_mem_regFns (k : Type) [Field k] (ι : Type) (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (b : Frames k V) (i : ι) (a m : Fin (finrank k (V i))) :
    (fun c : Frames k V => luNum ((b i).toMatrix (c i)) a m) ∈ regFns k V := by
  have : (fun c : Frames k V => luNum ((b i).toMatrix (c i)) a m) = ∑ l : Fin (m + 1),
      (fun c : Frames k V => (b i).toMatrix (c i) a (Fin.castLE m.isLt l)) *
        fun c => ((leadBlock ((b i).toMatrix (c i)) m).updateCol l (Pi.single (Fin.last m) 1)).det := by
    funext c
    simp [luNum, Finset.sum_apply, Matrix.cramer_apply]
  rw [this]
  refine Subalgebra.sum_mem _ fun l _ => mul_mem (toMatrix_entry_mem_regFns b i _ _) (det_mem_regFns _ fun a' c' => ?_)
  by_cases h : c' = l
  · simp only [Matrix.updateCol_apply, h, if_true]
    exact const_mem_regFns _
  · simp only [Matrix.updateCol_apply, h, if_false]
    exact toMatrix_entry_mem_regFns b i _ _

theorem leadMinor_mul_ne_zero {k : Type} [Field k] {n : ℕ} (L U : Matrix (Fin n) (Fin n) k) (hL : L.BlockTriangular OrderDual.toDual)
    (hL1 : ∀ a, L a a = 1) (hU : U.BlockTriangular id) (hdet : IsUnit (L * U).det) : ∀ m, leadMinor (L * U) m ≠ 0 := by
  intro m
  have hLd : L.det = 1 := by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]
  have hUd : ∀ l, U l l ≠ 0 := by
    have : U.det ≠ 0 := by
      rw [Matrix.det_mul, hLd, one_mul] at hdet
      exact hdet.ne_zero
    rw [Matrix.det_of_upperTriangular hU] at this
    exact fun l => Finset.prod_ne_zero_iff.1 this l (Finset.mem_univ _)
  have hblock : leadBlock (L * U) m = leadBlock L m * leadBlock U m := by
    ext a c
    simp only [leadBlock, Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE m.isLt) (Fin.castLE_injective _) _ _ (fun l hl => ?_) (fun _ => rfl)
    have ha := a.isLt
    have : Fin.castLE m.isLt a < l := by
      rw [Fin.lt_def, Fin.coe_castLE]
      by_contra h
      push_neg at h
      exact hl ⟨⟨l, by omega⟩, Fin.ext (by simp)⟩
    rw [hL (by simpa using this), zero_mul]
  rw [leadMinor, hblock, Matrix.det_mul,
    Matrix.det_of_lowerTriangular (leadBlock L m) (fun a c h => hL (show OrderDual.toDual (Fin.castLE m.isLt c) < OrderDual.toDual (Fin.castLE m.isLt a) by
      rw [OrderDual.toDual_lt_toDual, Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 h))),
    Matrix.det_of_upperTriangular (M := leadBlock U m) (fun a c h => hU (show Fin.castLE m.isLt c < Fin.castLE m.isLt a by
      rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact Fin.lt_def.1 h))]
  simp only [leadBlock, Matrix.submatrix_apply, hL1, Finset.prod_const_one, one_mul]
  exact Finset.prod_ne_zero_iff.2 fun l _ => hUd _

theorem exists_upperTriangular_mul_eq_luLower {k : Type} [Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k) (hΔ : ∀ m, leadMinor P m ≠ 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, X.BlockTriangular id ∧ P * X = luLower P := by
  classical
  let X : Matrix (Fin n) (Fin n) k := fun l m => if h : (l : ℕ) ≤ m then
    (leadBlock P m).cramer (Pi.single (Fin.last m) 1) ⟨l, Nat.lt_succ_of_le h⟩ / leadMinor P m else 0
  refine ⟨X, fun a c hac => ?_, ?_⟩
  · have : ¬ (a : ℕ) ≤ c := not_le.2 (Fin.lt_def.1 hac)
    simp only [X, dif_neg this]
  · ext a m
    have key : (P * X) a m = luNum P a m / leadMinor P m := by
      rw [Matrix.mul_apply, luNum, Finset.sum_div]
      symm
      refine Fintype.sum_of_injective (Fin.castLE m.isLt) (Fin.castLE_injective _) _ _ (fun l hl => ?_) (fun l => ?_)
      · have hm := m.isLt
        have hn : ¬ (l : ℕ) ≤ m := fun h => hl ⟨⟨l, by omega⟩, Fin.ext (by simp)⟩
        simp only [X, dif_neg hn, mul_zero]
      · have hl : ((Fin.castLE m.isLt l : Fin n) : ℕ) ≤ m := by simpa using Nat.lt_succ_iff.1 l.isLt
        simp only [X, dif_pos hl, mul_div_assoc]
        rfl
    rw [key]
    rcases lt_or_ge m a with h | h
    · rw [luLower_apply_of_lt _ h]
    · have hmul := congrFun (Matrix.mulVec_cramer (leadBlock P m) (Pi.single (Fin.last m) 1))
        ⟨a, Nat.lt_succ_of_le h⟩
      have e : luNum P a m = (Matrix.mulVec (leadBlock P m) ((leadBlock P m).cramer (Pi.single (Fin.last m) 1)))
          ⟨a, Nat.lt_succ_of_le h⟩ := rfl
      rw [e, hmul, Pi.smul_apply, smul_eq_mul]
      rcases (show a ≤ m from h).eq_or_lt with rfl | h'
      · have : (⟨a, Nat.lt_succ_of_le h⟩ : Fin (a + 1)) = Fin.last a := Fin.ext rfl
        rw [this, Pi.single_eq_same, mul_one, luLower_apply_self]
        exact div_self (hΔ a)
      · have : (⟨a, Nat.lt_succ_of_le h⟩ : Fin (m + 1)) ≠ Fin.last m := fun h2 =>
          h'.ne (Fin.ext (by simpa [Fin.ext_iff] using h2))
        rw [Pi.single_eq_of_ne this, mul_zero, zero_div, luLower_lowerTriangular _ (by simpa using h')]

section
variable {k : Type} [Field k] {n : ℕ}

theorem eq_of_mul_upperTriangular {L L' T : Matrix (Fin n) (Fin n) k} (hL : L.BlockTriangular OrderDual.toDual)
    (hL1 : ∀ a, L a a = 1) (hL' : L'.BlockTriangular OrderDual.toDual) (hL'1 : ∀ a, L' a a = 1)
    (hT : T.BlockTriangular id) (h : L * T = L') : L = L' := by
  have hdet : IsUnit L.det := by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]
  letI := L.invertibleOfIsUnitDet hdet
  have hT' : T = L⁻¹ * L' := by
    rw [← h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hlow : T.BlockTriangular OrderDual.toDual := hT' ▸ (Matrix.blockTriangular_inv_of_blockTriangular hL).mul hL'
  have hT1 : T = 1 := by
    ext a c
    rcases lt_trichotomy a c with h1 | rfl | h1
    · rw [hlow (by simpa using h1), Matrix.one_apply_ne h1.ne]
    · have := congrFun (congrFun h a) a
      rw [Matrix.mul_apply, Finset.sum_eq_single a (fun l _ hl => ?_) (by simp), hL1, hL'1, one_mul] at this
      · rw [this, Matrix.one_apply_eq]
      · rcases lt_or_gt_of_ne hl with h2 | h2
        · rw [hlow (by simpa using h2), mul_zero]
        · rw [hL (by simpa using h2), zero_mul]
    · rw [hT h1, Matrix.one_apply_ne h1.ne']
  rw [← h, hT1, Matrix.mul_one]

theorem lu_criterion (P L : Matrix (Fin n) (Fin n) k) (hP : IsUnit P.det) (hL : L.BlockTriangular OrderDual.toDual)
    (hL1 : ∀ a, L a a = 1) : (L⁻¹ * P).BlockTriangular id ↔ (∀ m, leadMinor P m ≠ 0) ∧ L = luLower P := by
  have hLdet : IsUnit L.det := by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]
  have hPLU : L * (L⁻¹ * P) = P := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLdet, Matrix.one_mul]
  constructor
  · intro hU
    have hΔ : ∀ m, leadMinor P m ≠ 0 := by
      have := leadMinor_mul_ne_zero L _ hL hL1 hU (by rw [hPLU]; exact hP)
      rwa [hPLU] at this
    refine ⟨hΔ, ?_⟩
    obtain ⟨X, hX, hPX⟩ := exists_upperTriangular_mul_eq_luLower P hΔ
    refine eq_of_mul_upperTriangular hL hL1 (luLower_lowerTriangular P) (luLower_apply_self P) (hU.mul hX) ?_
    rw [← Matrix.mul_assoc, hPLU, hPX]
  · rintro ⟨hΔ, rfl⟩
    obtain ⟨X, hX, hPX⟩ := exists_upperTriangular_mul_eq_luLower P hΔ
    have hXdet : IsUnit X.det := by
      have := congrArg Matrix.det hPX
      rw [Matrix.det_mul] at this
      exact isUnit_of_mul_isUnit_right (this ▸ hLdet)
    letI := X.invertibleOfIsUnitDet hXdet
    have : (luLower P)⁻¹ * P = X⁻¹ := by
      rw [← hPX, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    rw [this]
    exact Matrix.blockTriangular_inv_of_blockTriangular hX
end

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def cellCoord (b c : Frames k V) : AffPts k (CellIdx k V) := fun j =>
  luNum ((b j.1).toMatrix (c j.1)) j.2.1.1 j.2.1.2 / leadMinor ((b j.1).toMatrix (c j.1)) j.2.1.2

theorem uniMat_eq_luLower_iff (b c : Frames k V) (u : AffPts k (CellIdx k V)) :
    (∀ i, uniMat u i = luLower ((b i).toMatrix (c i))) ↔ u = cellCoord b c := by
  constructor
  · intro H
    funext j
    obtain ⟨i, ⟨⟨a, m⟩, h⟩⟩ := j
    have := congrFun (congrFun (H i) a) m
    rwa [uniMat_apply_of_lt u i h, luLower_apply_of_lt _ h] at this
  · rintro rfl i
    ext a m
    rcases lt_trichotomy a m with h | rfl | h
    · rw [uniMat_apply_of_gt _ i h, luLower_lowerTriangular _ (by simpa using h)]
    · rw [uniMat_apply_self, luLower_apply_self]
    · rw [uniMat_apply_of_lt _ i h, luLower_apply_of_lt _ h]
      rfl

theorem flags_eq_cellMap_iff (b c : Frames k V) (u : AffPts k (CellIdx k V)) :
    c.flags = cellMap b u ↔ (∀ i m, leadMinor ((b i).toMatrix (c i)) m ≠ 0) ∧ u = cellCoord b c := by
  have e : c.flags = cellMap b u ↔ ∀ i, c.flags i = cellMap b u i := ⟨fun h _ => h ▸ rfl, fun h => funext h⟩
  rw [← uniMat_eq_luLower_iff, e, ← forall_and]
  refine forall_congr' fun i => ?_
  rw [flags_apply_eq_cellMap_iff, lu_criterion _ _ (Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _))
    (uniMat_blockTriangular u i) (uniMat_apply_self u i), eq_comm (a := uniMat u i)]

section Assembly
variable {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def cellDet (b c : Frames k V) : k :=
  ∏ p : (Σ i, Fin (finrank k (V i))), leadMinor ((b p.1).toMatrix (c p.1)) p.2

theorem cellDet_ne_zero_iff (b c : Frames k V) :
    cellDet b c ≠ 0 ↔ ∀ i m, leadMinor ((b i).toMatrix (c i)) m ≠ 0 := by
  simp [cellDet, Finset.prod_ne_zero_iff, Sigma.forall]

theorem cellDet_mem (b : Frames k V) : (fun c => cellDet b c) ∈ regFns k V := by
  have : (fun c => cellDet b c) = ∏ p : (Σ i, Fin (finrank k (V i))),
      fun c : Frames k V => leadMinor ((b p.1).toMatrix (c p.1)) p.2 := by
    funext c
    simp [cellDet, Finset.prod_apply]
  rw [this]
  exact Subalgebra.prod_mem _ fun p _ => leadMinor_toMatrix_mem_regFns k ι V b p.1 p.2

theorem cellDet_sq_mul_mem (b : Frames k V) (j : CellIdx k V) :
    ((fun c => cellDet b c) ^ 2 * fun c => cellCoord b c j) ∈ regFns k V := by
  classical
  obtain ⟨i, ⟨⟨a, m⟩, h⟩⟩ := j
  let E : Frames k V → k := ∏ p ∈ Finset.univ.erase (⟨i, m⟩ : Σ i, Fin (finrank k (V i))),
    fun c => leadMinor ((b p.1).toMatrix (c p.1)) p.2
  have hE : E ∈ regFns k V := Subalgebra.prod_mem _ fun p _ => leadMinor_toMatrix_mem_regFns k ι V b p.1 p.2
  have : ((fun c => cellDet b c) ^ 2 * fun c => cellCoord b c ⟨i, ⟨⟨a, m⟩, h⟩⟩) =
      (fun c => cellDet b c) * (fun c => luNum ((b i).toMatrix (c i)) a m) * E := by
    funext c
    have hprod : cellDet b c = leadMinor ((b i).toMatrix (c i)) m * E c := by
      simp only [cellDet, E, Finset.prod_apply]
      exact (Finset.mul_prod_erase _ (fun p : (Σ i, Fin (finrank k (V i))) =>
        leadMinor ((b p.1).toMatrix (c p.1)) p.2) (Finset.mem_univ (⟨i, m⟩ : Σ i, Fin (finrank k (V i))))).symm
    simp only [Pi.mul_apply, Pi.pow_apply, cellCoord]
    by_cases h0 : leadMinor ((b i).toMatrix (c i)) m = 0
    · simp [hprod, h0]
    · rw [hprod]; field_simp
  rw [this]
  exact mul_mem (mul_mem (cellDet_mem b) (luNum_toMatrix_mem_regFns k ι V b i a m)) hE

theorem preimage_image_cellMap (b : Frames k V) (O : Set (AffPts k (CellIdx k V))) :
    Frames.flags ⁻¹' (cellMap b '' O) = {c | cellDet b c ≠ 0 ∧ cellCoord b c ∈ O} := by
  ext c
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq, cellDet_ne_zero_iff]
  constructor
  · rintro ⟨u, hu, h⟩
    obtain ⟨h1, rfl⟩ := (flags_eq_cellMap_iff b c u).1 h.symm
    exact ⟨h1, hu⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, ((flags_eq_cellMap_iff b c _).2 ⟨h1, rfl⟩).symm⟩

theorem isOpen_cellCoord_mem (b : Frames k V) {O : Set (AffPts k (CellIdx k V))} (hO : IsOpen O) :
    IsOpen {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ O} := by
  have hO' : GenerateOpen {s | ∃ p : MvPolynomial (CellIdx k V) k, s = {x : AffPts k (CellIdx k V) | MvPolynomial.eval x p ≠ 0}} O := hO
  clear hO
  induction hO' with
  | basic s hs =>
    obtain ⟨q, rfl⟩ := hs
    obtain ⟨N, hN⟩ := exists_pow_mul_eval_mem (regFns k V) _ (fun j c => cellCoord b c j) (pow_mem (cellDet_mem b) 2)
      (cellDet_sq_mul_mem b) q
    have : {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ {x : AffPts k (CellIdx k V) | MvPolynomial.eval x q ≠ 0}} =
        {c | ((fun c => cellDet b c) * (((fun c => cellDet b c) ^ 2) ^ N *
          fun c => MvPolynomial.eval (fun j => cellCoord b c j) q)) c ≠ 0} := by
      ext c
      simp only [Set.mem_setOf_eq, Pi.mul_apply, Pi.pow_apply, mul_ne_zero_iff, ne_eq, pow_eq_zero_iff', not_and,
        not_not]
      tauto
    rw [this]
    exact isOpen_generateFrom_of_mem ⟨_, mul_mem (cellDet_mem b) hN, rfl⟩
  | univ =>
    convert (isClosed_zero (cellDet_mem b)).isOpen_compl using 1
    ext c
    simp
  | inter s t _ _ hs ht =>
    convert hs.inter ht using 1
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  | sUnion S _ hS =>
    have : {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ ⋃₀ S} =
        ⋃ s ∈ S, {c | cellDet b c ≠ 0 ∧ cellCoord b c ∈ s} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_sUnion, Set.mem_iUnion, exists_prop]
      tauto
    rw [this]
    exact isOpen_biUnion hS
end Assembly

theorem isOpenMap_cellMap (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) : IsOpenMap (cellMap b) := by
  intro O hO
  rw [isOpen_coinduced, preimage_image_cellMap]
  exact isOpen_cellCoord_mem b hO

end GlobalTheory.FlagPts

example : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)] (b : Frames k V), IsOpenMap (cellMap b) := GlobalTheory.FlagPts.isOpenMap_cellMap
end
end

open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenMap_cellMap' : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), IsOpenMap (cellMap b) := by
  atlas_forward_decl GlobalTheory.FlagPts.isOpenMap_cellMap
end

section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

theorem card_lowerPairs (d : ℕ) : Fintype.card {p : Fin d × Fin d // p.2 < p.1} = d * (d - 1) / 2 := by
  rw [Fintype.card_subtype, ← Finset.sum_range_id, Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]

theorem card_cellIdx {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] {n : ℕ} (hn : ∀ i, finrank k (V i) = n) :
    Fintype.card (CellIdx k V) = Fintype.card ι * (n * (n - 1) / 2) := by
  have h1 : Fintype.card (CellIdx k V) =
      ∑ i, Fintype.card {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1} := by
    unfold CellIdx
    convert Fintype.card_sigma (α := fun i => {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1})
  rw [h1]
  simp only [card_lowerPairs, hn, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem isOpenEmbedding_cellMap {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) :
    Topology.IsOpenEmbedding (cellMap b) :=
  .of_continuous_injective_isOpenMap (GlobalTheory.T.continuous_cellMap' k ι V b) (GlobalTheory.T.injective_cellMap k ι V b) (GlobalTheory.T.isOpenMap_cellMap' k ι V b)

theorem topologicalKrullDim_flags (k : Type) [Field k] [IsAlgClosed k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (n : ℕ)
    (hn : ∀ i, finrank k (V i) = n) :
    topologicalKrullDim (Flags k V) = (Fintype.card ι * (n * (n - 1) / 2) : ℕ) := by
  have hU : topologicalKrullDim (Set.univ : Set (Flags k V)) = topologicalKrullDim (Flags k V) :=
    (Homeomorph.Set.univ (Flags k V)).isHomeomorph.topologicalKrullDim_eq
  rw [← hU, ← card_cellIdx (k := k) (V := V) hn, ← GlobalTheory.T.topologicalKrullDim_affine_points k (CellIdx k V)]
  refine GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun F _ => ?_
  obtain ⟨b, rfl⟩ := flags_surjective F
  have he := isOpenEmbedding_cellMap b
  refine ⟨Set.range (cellMap b), he.isOpen_range, ⟨0, cellMap_zero b⟩, ?_⟩
  rw [Set.inter_univ]
  exact GlobalTheory.topologicalKrullDim_eq_of_isEmbedding he.isEmbedding rfl

example : ∀ (k : Type) [Field k] [IsAlgClosed k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (n : ℕ), (∀ i, finrank k (V i) = n) →
    topologicalKrullDim (Flags k V) = (Fintype.card ι * (n * (n - 1) / 2) : ℕ) :=
  topologicalKrullDim_flags

end GlobalTheory.FlagPts
end
end
