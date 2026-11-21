import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAtlasRefiningCocycle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasModelComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelOfAtlas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellSpanPreserved
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellCoordinatesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellsOfChartsPolynomial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellAtlasFromLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCoordinatesStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierIndependentSpanIff

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_holds_of_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (t : Step Y i₀) (Z Z' : Mdl Y i₀), (∃ f, IsMap Z' Z f) → t.Holds Z → t.Holds Z' := by
  first | exact @GlobalTheory.LocM.StepMono.holds_mono | exact GlobalTheory.LocM.StepMono.holds_mono | (intros; apply GlobalTheory.LocM.StepMono.holds_mono <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.CellGen

variable {S : Type} [CommRing S] {m a k b N : ℕ}

theorem pair_gvec (D c : Fin m → Fin (N + 1) → S) (h : LeftInv D c) (w : GPm m a b) (x : GVar m a k b → S)
    (j l : Fin m) : ∑ r, D (w.1 j) r * gvec c w x l r = gcell x j l := by
  simp only [gvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ i, ∑ r, D (w.1 j) r * (gcell x i l * c (w.1 i) r) = if j = i then gcell x i l else 0 := by
    intro i
    have h1 : ∑ r, D (w.1 j) r * (gcell x i l * c (w.1 i) r) = gcell x i l * ∑ r, D (w.1 j) r * c (w.1 i) r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [h1, h]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem det_updateCol_one (j : Fin k) (v : Fin k → S) :
    (Matrix.updateCol (1 : Matrix (Fin k) (Fin k) S) j v).det = v j := by
  rw [← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

theorem gcell_castLE (hk : k ≤ m) (x : GVar m a k b → S) (l l' : Fin k) :
    gcell x (Fin.castLE hk l') (Fin.castLE hk l) = (1 : Matrix (Fin k) (Fin k) S) l l' := by
  have h1 : ¬ k ≤ (l' : ℕ) := not_le.2 l'.2
  unfold gcell
  rw [dif_neg (fun h => h1 h.2.2.1), Matrix.one_apply]
  by_cases h : l = l'
  · simp [h]
  · rw [if_neg h, if_neg fun e => h (Fin.castLE_injective hk e).symm]

theorem lform_gxi (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → S) (h : LeftInv D c) (w : GPm m a b) (j : Fin k → Fin m) :
    ∑ q, (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) (lform D (w.1 ∘ j) q) * gxi a b hk c w q =
      (Matrix.of fun l l' => gcell (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) S) (j l')
        (Fin.castLE hk l)).det := by
  have h1 : ∀ q, (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) (lform D (w.1 ∘ j) q) =
      lform (fun z => (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) ∘ D z) (w.1 ∘ j) q := fun q => by
    simp only [lform, map_prod, Function.comp_apply]
  simp only [h1, gxi]
  rw [GlobalTheory.FlagEmb.CauchyBinet.lform_plk]
  congr 1
  ext1 l l'
  exact pair_gvec _ _ (h.map (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S)) w _ (j l') _

theorem lform_gxi_var (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → S) (h : LeftInv D c) (w : GPm m a b) (v : GVar m a k b) :
    ∑ q, (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S)
      (lform D (w.1 ∘ Function.update (Fin.castLE hk) ⟨v.1.2, v.2.2.1⟩ v.1.1) q) * gxi a b hk c w q =
      MvPolynomial.X v := by
  rw [lform_gxi hk D c h w]
  have h1 : (Matrix.of fun l l' => gcell (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) S)
      (Function.update (Fin.castLE hk) ⟨v.1.2, v.2.2.1⟩ v.1.1 l') (Fin.castLE hk l)) =
      Matrix.updateCol (1 : Matrix (Fin k) (Fin k) _) ⟨v.1.2, v.2.2.1⟩
        fun l => gcell MvPolynomial.X v.1.1 (Fin.castLE hk l) := by
    ext1 l l'
    rw [Matrix.of_apply, Matrix.updateCol_apply]
    by_cases hl : l' = ⟨v.1.2, v.2.2.1⟩
    · rw [if_pos hl, hl, Function.update_self]
    · rw [if_neg hl, Function.update_of_ne hl, gcell_castLE]
  rw [h1, det_updateCol_one]
  exact dif_pos v.2

theorem main : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R) (w : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → ∑ q, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D w q) * gxi a b hk c w q = 1 ∧ Function.Surjective (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gxi a b hk c w)) := by
  intro R _ m a k b N hk D c w _ _ h
  refine ⟨?_, fun p => ?_⟩
  · unfold gell
    rw [lform_gxi hk D c h w, ← Matrix.det_one (n := Fin k)]
    congr 1
    ext1 l l'
    exact gcell_castLE hk _ l l'
  · change p ∈ (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gxi a b hk c w)).range
    induction p using MvPolynomial.induction_on with
    | C r => exact ⟨MvPolynomial.C r, by simp⟩
    | add p q hp hq => exact add_mem hp hq
    | mul_X p v hp =>
      refine mul_mem hp ?_
      rw [← lform_gxi_var hk D c h w v]
      exact sum_mem fun q _ => mul_mem ⟨MvPolynomial.C _, MvPolynomial.eval₂Hom_C _ _ _⟩
        ⟨MvPolynomial.X q, MvPolynomial.eval₂Hom_X' _ _ _⟩

end GlobalTheory.GrCl.CellGen
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_coordinate_polynomials_surjective : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R) (w : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → ∑ q, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D w q) * gxi a b hk c w q = 1 ∧ Function.Surjective (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gxi a b hk c w)) := by
  atlas_forward_decl GlobalTheory.GrCl.CellGen.main
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv plE)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.CellLin

variable {R : Type} [CommRing R] {m a k b N : ℕ}

def pmat (hk : k ≤ m) (w : GPm m a b) : Matrix (Fin k) (Fin m) (MvPolynomial (GVar m a k b) R) :=
  fun l i => gcell MvPolynomial.X (w.1⁻¹ i) (Fin.castLE hk l)

theorem gvec_apply (hk : k ≤ m) (c : Fin m → Fin (N + 1) → R) (w : GPm m a b) (l : Fin k) (r : Fin (N + 1)) :
    gvec (fun l => (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) ∘ c l) w
        (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) R) (Fin.castLE hk l) r =
      ∑ i, pmat hk w l i * MvPolynomial.C (c i r) := by
  simp only [gvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, pmat]
  refine ((Equiv.sum_comp w.1 fun i =>
    gcell MvPolynomial.X (w.1⁻¹ i) (Fin.castLE hk l) * MvPolynomial.C (c i r)).symm.trans ?_).symm
  simp

theorem gxi_eq (hk : k ≤ m) (c : Fin m → Fin (N + 1) → R) (w : GPm m a b) (q : Fin (plN N k + 1)) :
    gxi a b hk c w q = ∑ S : Set.powersetCard (Fin m) k, ((pmat hk w).submatrix id (subsetEnum S)).det *
      MvPolynomial.C (plk c (subsetEnum S) q) := by
  let B : Matrix (Fin m) (Fin k) (MvPolynomial (GVar m a k b) R) :=
    Matrix.of fun i l' => MvPolynomial.C (c i (plE N k q l'))
  have h : (Matrix.of fun l l' => gvec (fun l => (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) ∘ c l) w
        (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) R) (Fin.castLE hk l) (plE N k q l')) =
      (pmat (R := R) hk w * B : Matrix (Fin k) (Fin k) (MvPolynomial (GVar m a k b) R)) := by
    ext1 l l'
    rw [Matrix.mul_apply, Matrix.of_apply, gvec_apply]
    rfl
  unfold gxi plk
  rw [h, det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1

theorem sum_gell (hk : k ≤ m) {D c : Fin m → Fin (N + 1) → R} (h : LeftInv D c) (w v : GPm m a b) :
    ∑ q, MvPolynomial.C (gell a b hk D v q) * gxi a b hk c w q =
      ((pmat hk w).submatrix id (v.1 ∘ Fin.castLE hk)).det := by
  have h1 : ∀ q, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D v q) =
      lform (fun i => (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) ∘ D i) (v.1 ∘ Fin.castLE hk) q := by
    intro q
    simp [gell, lform, map_prod]
  simp only [h1, gxi]
  rw [GlobalTheory.FlagEmb.CauchyBinet.lform_plk]
  congr 1
  ext1 l l'
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id, gvec_apply, Function.comp_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ i, ∑ r, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (D (v.1 (Fin.castLE hk l')) r) *
      (pmat hk w l i * MvPolynomial.C (c i r)) = pmat hk w l i *
        MvPolynomial.C (∑ r, D (v.1 (Fin.castLE hk l')) r * c i r) := by
    intro i
    simp only [map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp only [h2, h _ _]
  rw [Finset.sum_eq_single (v.1 (Fin.castLE hk l'))]
  · simp
  · intro i _ hi
    rw [if_neg (Ne.symm hi)]
    simp
  · simp

theorem exists_perm (hk : k ≤ m) (hkb : k ≤ b) (hak : a ≤ k) (f : Fin k → Fin m) (hf : Function.Injective f)
    (h1 : ∀ l : Fin k, (l : ℕ) < a → (f l : ℕ) = l) (h2 : ∀ l, (f l : ℕ) < b) :
    ∃ v : GPm m a b, ∀ l, v.1 (Fin.castLE hk l) = f l := by
  classical
  let p : Fin m → Prop := fun i => (i : ℕ) < k ∨ b ≤ (i : ℕ)
  let g : {i // p i} → Fin m := fun i => if h : (i.1 : ℕ) < k then f ⟨i.1, h⟩ else i.1
  have hg : Function.Injective g := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [g] at hij
    split_ifs at hij with h3 h4 h4
    · have := hf hij
      simp only [Fin.mk.injEq] at this
      exact Subtype.ext (Fin.ext this)
    · have h5 := h2 ⟨i, h3⟩
      rw [hij] at h5
      have := hj.resolve_left h4
      omega
    · have h5 := h2 ⟨j, h4⟩
      rw [← hij] at h5
      have := hi.resolve_left h3
      omega
    · exact Subtype.ext hij
  let e : {i // p i} ≃ {y // y ∈ Set.range g} := Equiv.ofInjective g hg
  have hv : ∀ i (hi : p i), e.extendSubtype i = g ⟨i, hi⟩ := fun i hi => by
    rw [Equiv.extendSubtype_apply_of_mem e i hi]
    rfl
  refine ⟨⟨e.extendSubtype, fun i hi => ?_⟩, fun l => ?_⟩
  · rcases hi with hi | hi
    · have hik : (i : ℕ) < k := by omega
      rw [hv i (Or.inl hik)]
      simp only [g, dif_pos hik]
      exact Fin.ext (h1 ⟨i, hik⟩ hi)
    · have hik : ¬ (i : ℕ) < k := by omega
      rw [hv i (Or.inr hi)]
      simp only [g, dif_neg hik]
  · have hl : ((Fin.castLE hk l : Fin m) : ℕ) < k := l.2
    change e.extendSubtype (Fin.castLE hk l) = f l
    rw [hv _ (Or.inl hl)]
    simp only [g, dif_pos hl]
    rfl

theorem enum_init (hk : k ≤ m) (hak : a ≤ k) (f : Fin k → Fin m) (hf : StrictMono f)
    (h : ∀ i : Fin m, (i : ℕ) < a → i ∈ Set.range f) (n : ℕ) : ∀ (hn : n < k), n < a → (f ⟨n, hn⟩ : ℕ) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hna
    obtain ⟨l', hl'⟩ := h ⟨n, by omega⟩ hna
    have h1 : ¬ (l' : ℕ) < n := fun hlt => by
      have := ih l' hlt l'.2 (by omega)
      have h3 : f ⟨l', l'.2⟩ = f l' := rfl
      rw [h3, hl'] at this
      simp only at this
      omega
    rcases Nat.lt_or_ge n l' with h2 | h2
    · have h3 : f ⟨n, hn⟩ < f l' := hf (by simpa [Fin.lt_def] using h2)
      rw [hl'] at h3
      have h4 : (f ⟨n, hn⟩ : ℕ) < n := h3
      have h5 := hf.injective (Fin.ext (ih _ h4 (by omega) (by omega)))
      simp only [Fin.mk.injEq] at h5
      omega
    · have : (⟨n, hn⟩ : Fin k) = l' := Fin.ext (by simp; omega)
      rw [this, hl']

theorem det_eq_zero_of_lt (hk : k ≤ m) (hak : a ≤ k) (w : GPm m a b) (f : Fin k → Fin m) (i : Fin m) (hi : (i : ℕ) < a)
    (hf : i ∉ Set.range f) : ((pmat (R := R) hk w).submatrix id f).det = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨i, by omega⟩ fun l' => ?_
  simp only [Matrix.submatrix_apply, id, pmat, gcell]
  rw [dif_neg (fun h => by have := h.1; simp at this; omega), if_neg]
  intro he
  apply hf
  refine ⟨l', ?_⟩
  have h1 : Fin.castLE hk (⟨i, by omega⟩ : Fin k) = i := rfl
  rw [h1, Equiv.Perm.inv_eq_iff_eq, w.2 i (Or.inl hi)] at he
  exact he

theorem det_eq_zero_of_ge (hk : k ≤ m) (hkb : k ≤ b) (w : GPm m a b) (f : Fin k → Fin m) (l' : Fin k)
    (hi : b ≤ (f l' : ℕ)) : ((pmat (R := R) hk w).submatrix id f).det = 0 := by
  refine Matrix.det_eq_zero_of_column_eq_zero l' fun l => ?_
  have h1 : w.1⁻¹ (f l') = f l' := by
    rw [Equiv.Perm.inv_eq_iff_eq, w.2 _ (Or.inr hi)]
  simp only [Matrix.submatrix_apply, id, pmat, gcell, h1]
  rw [dif_neg (fun h => by have := h.2.2.2; omega), if_neg]
  intro he
  have h2 := congrArg Fin.val he
  have h3 := l.2
  simp only [Fin.val_castLE] at h2
  omega

theorem main : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R), a ≤ k → k ≤ b → LeftInv D c → ∀ q, ∃ (T : Type) (_ : Fintype T) (jj : T → GPm m a b) (e : T → R), ∀ w' : GPm m a b, gxi a b hk c w' q = ∑ t, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (e t) * ∑ q', (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D (jj t) q') * gxi a b hk c w' q' := by
  intro R _ m a k b N hk D c hak hkb h q
  classical
  let admitted : Set.powersetCard (Fin m) k → Prop := fun S =>
    (∀ i : Fin m, (i : ℕ) < a → i ∈ Set.range (subsetEnum S)) ∧ ∀ l, (subsetEnum S l).val < b
  have hex : ∀ S : {S // admitted S}, ∃ v : GPm m a b, ∀ l, v.1 (Fin.castLE hk l) = subsetEnum S.1 l := fun S =>
    exists_perm hk hkb hak _ (subsetEnum_injective S.1)
      (fun l hl => enum_init hk hak _ (S.1.1.orderEmbOfFin S.1.2).strictMono S.2.1 l l.2 hl) S.2.2
  choose jj hjj using hex
  refine ⟨{S // admitted S}, inferInstance, jj, fun S => plk c (subsetEnum S.1) q, fun w => ?_⟩
  have h1 : ∀ S, (jj S).1 ∘ Fin.castLE hk = subsetEnum S.1 := fun S => funext (hjj S)
  simp only [sum_gell hk h, h1]
  rw [gxi_eq, ← Finset.sum_subtype (Finset.univ.filter admitted) (by simp)
    (fun S => MvPolynomial.C (plk c (subsetEnum S) q) * ((pmat hk w).submatrix id (subsetEnum S)).det),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with hS
  · exact mul_comm _ _
  · rw [not_and_or] at hS
    rcases hS with hS | hS
    · push Not at hS
      obtain ⟨i, hi, hf⟩ := hS
      rw [det_eq_zero_of_lt hk hak w _ i hi hf, zero_mul]
    · push Not at hS
      obtain ⟨l, hl⟩ := hS
      rw [det_eq_zero_of_ge hk hkb w _ l hl, zero_mul]

end GlobalTheory.GrCl.CellLin
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_coordinate_linear_relation : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R), a ≤ k → k ≤ b → LeftInv D c → ∀ q, ∃ (T : Type) (_ : Fintype T) (jj : T → GPm m a b) (e : T → R), ∀ w' : GPm m a b, gxi a b hk c w' q = ∑ t, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (e t) * ∑ q', (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D (jj t) q') * gxi a b hk c w' q' := by
  atlas_forward_decl GlobalTheory.GrCl.CellLin.main
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmann_cell_span_preserved : ∀ (S : Type) [CommRing S] (m a k b : ℕ) (Q : Type) [AddCommGroup Q] [Module S Q] (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S), a ≤ k → k ≤ b → (LinearIndependent S c → LinearIndependent S (gvec c w x)) ∧ Submodule.span S (Set.range (gvec c w x)) = Submodule.span S (Set.range c) ∧ ∀ e : ℕ, e ≤ a ∨ b ≤ e → initSpan S (gvec c w x) e = initSpan S c e := by
  first | exact @GlobalTheory.GrCl.gvec_frame | exact GlobalTheory.GrCl.gvec_frame | (intros; apply GlobalTheory.GrCl.gvec_frame <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmann_cell_coordinates_exist : ∀ (K : Type) [Field K] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → K) (u : Fin k → Fin (N + 1) → K), a ≤ k → k ≤ b → LeftInv D c → LinearIndependent K u → initSpan K c a ≤ Submodule.span K (Set.range u) → Submodule.span K (Set.range u) ≤ initSpan K c b → (∃ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q ≠ 0) ∧ ∀ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q ≠ 0 → ∃ x : GVar m a k b → K, Submodule.span K (Set.range u) = initSpan K (gvec c w x) k := by
  first | exact @GlobalTheory.GrCl.Normal.main | exact GlobalTheory.GrCl.Normal.main | (intros; apply GlobalTheory.GrCl.Normal.main <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrCl.CellGlue

theorem linearIndependent_of_leftInv {K : Type} [Field K] {m M : ℕ} {D c : Fin m → Fin M → K} (h : LeftInv D c) :
    LinearIndependent K c := by
  rw [Fintype.linearIndependent_iff]
  intro g hg z
  have e := congrArg (fun v : Fin M → K => ∑ r, D z r * v r) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    Finset.mul_sum] at e
  rw [Finset.sum_comm] at e
  have key : ∀ i, ∑ r, D z r * (g i * c i r) = if z = i then g i else 0 := fun i => by
    have e1 : ∑ r, D z r * (g i * c i r) = g i * ∑ r, D z r * c i r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [e1, h z i]
    split_ifs <;> simp
  simpa [key] using e

theorem span_comp_castLE {S : Type} [CommRing S] {Q : Type} [AddCommGroup Q] [Module S Q] {m k : ℕ} (hk : k ≤ m)
    (v : Fin m → Q) : Submodule.span S (Set.range (v ∘ Fin.castLE hk)) = initSpan S v k := by
  unfold initSpan
  congr 1
  ext y
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Fin.castLE hk l, l.2, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩

theorem map_gell {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {m a k b N : ℕ} (hk : k ≤ m)
    (D : Fin m → Fin (N + 1) → S) (w : GPm m a b) (q : Fin (plN N k + 1)) :
    φ (gell a b hk D w q) = gell a b hk (fun l => φ ∘ D l) w q := by
  simp only [gell, lform, map_prod, Function.comp_apply]

theorem comp_gxi {R K : Type} [CommRing R] [CommRing K] {m a k b N : ℕ} (hk : k ≤ m) (c : Fin m → Fin (N + 1) → R)
    (w : GPm m a b) (ψ : MvPolynomial (GVar m a k b) R →+* K) :
    ψ ∘ gxi a b hk c w =
      plk (gvec (fun l => (ψ.comp MvPolynomial.C) ∘ c l) w (ψ ∘ MvPolynomial.X) ∘ Fin.castLE hk) id := by
  unfold gxi
  rw [GlobalTheory.FlagEmb.map_plk]
  simp only [comp_gvec]
  rfl

theorem mem_cell_of_initSpan_eq : ∀ (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (m a k b N : ℕ) (hk : k ≤ m)
    (D c : Fin m → Fin (N + 1) → R) (D' c' : Fin m → Fin (N + 1) → R') (φ : R →+* K)
    (ψ' : MvPolynomial (GVar m a k b) R' →+* K) (w' : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → LeftInv D' c' →
    (∀ e : ℕ, e = a ∨ e = b →
      initSpan K (fun l => φ ∘ c l) e = initSpan K (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) e) →
    (∃ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0) ∧
      ∀ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0 →
        ∃ (ψ : MvPolynomial (GVar m a k b) R →+* K) (u : Kˣ),
          ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ gxi a b hk c' w' = (u : K) • (ψ ∘ gxi a b hk c w) := by
  intro K R R' _ _ _ m a k b N hk D c D' c' φ ψ' w' hak hkb hDc hDc' hab
  have hcK : LinearIndependent K (fun l => φ ∘ c l) := linearIndependent_of_leftInv (hDc.map φ)
  have hcK' : LinearIndependent K (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) :=
    linearIndependent_of_leftInv (hDc'.map (ψ'.comp MvPolynomial.C))
  obtain ⟨hGi, -, hGe⟩ := GlobalTheory.T.grassmann_cell_span_preserved K m a k b (Fin (N + 1) → K) (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w'
    (ψ' ∘ MvPolynomial.X) hak hkb
  have hUi := (hGi hcK').comp _ (Fin.castLE_injective hk)
  have hlo : initSpan K (fun l => φ ∘ c l) a ≤ Submodule.span K (Set.range
      (gvec (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w' (ψ' ∘ MvPolynomial.X) ∘ Fin.castLE hk)) := by
    rw [hab a (Or.inl rfl), ← hGe a (Or.inl le_rfl), span_comp_castLE]
    exact GlobalTheory.FlagMod.initSpan_mono _ hak
  have hhi : Submodule.span K (Set.range
      (gvec (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w' (ψ' ∘ MvPolynomial.X) ∘ Fin.castLE hk)) ≤
        initSpan K (fun l => φ ∘ c l) b := by
    rw [hab b (Or.inr rfl), ← hGe b (Or.inr le_rfl), span_comp_castLE]
    exact GlobalTheory.FlagMod.initSpan_mono _ hkb
  obtain ⟨hex, hcell⟩ := GlobalTheory.T.grassmann_cell_coordinates_exist K m a k b N hk (fun l => φ ∘ D l) (fun l => φ ∘ c l) _ hak hkb (hDc.map φ) hUi
    hlo hhi
  have hsum : ∀ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) =
      ∑ q, gell a b hk (fun l => φ ∘ D l) w q *
        plk (gvec (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w' (ψ' ∘ MvPolynomial.X) ∘ Fin.castLE hk) id q :=
    fun w => Finset.sum_congr rfl fun q _ => by rw [map_gell, ← comp_gxi]; rfl
  refine ⟨?_, fun w hw => ?_⟩
  · obtain ⟨w, hw⟩ := hex
    exact ⟨w, by rwa [hsum]⟩
  · rw [hsum] at hw
    obtain ⟨x, hx⟩ := hcell w hw
    have hC : (MvPolynomial.eval₂Hom φ x).comp MvPolynomial.C = φ := by
      ext r; simp
    have hX : MvPolynomial.eval₂Hom φ x ∘ MvPolynomial.X = x := by
      funext v; simp
    obtain ⟨hVi, -, -⟩ := GlobalTheory.T.grassmann_cell_span_preserved K m a k b (Fin (N + 1) → K) (fun l => φ ∘ c l) w x hak hkb
    have hVi' := (hVi hcK).comp _ (Fin.castLE_injective hk)
    obtain ⟨r, hr⟩ := ((GlobalTheory.T.plucker_nonzero_iff_independent K N k _ _).2 hVi').1 ⟨hUi, by rw [hx, span_comp_castLE]⟩
    refine ⟨MvPolynomial.eval₂Hom φ x, r, hC, ?_⟩
    rw [comp_gxi, comp_gxi, hC, hX]
    exact hr

end GlobalTheory.GrCl.CellGlue
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_coordinates_base_change : ∀ (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R) (D' c' : Fin m → Fin (N + 1) → R') (φ : R →+* K) (ψ' : MvPolynomial (GVar m a k b) R' →+* K) (w' : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → LeftInv D' c' → (∀ e : ℕ, e = a ∨ e = b → initSpan K (fun l => φ ∘ c l) e = initSpan K (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) e) → (∃ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0) ∧ ∀ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0 → ∃ (ψ : MvPolynomial (GVar m a k b) R →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ gxi a b hk c' w' = (u : K) • (ψ ∘ gxi a b hk c w) := by
  atlas_forward_decl GlobalTheory.GrCl.CellGlue.mem_cell_of_initSpan_eq
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.PlanarMap

open GlobalTheory.FlagEmb (plE)

section Lin

variable {N k : ℕ}

def rowOf {S : Type} (z : Fin (plN N k + 1) → S) (r : Fin k → Fin (N + 1)) (l : Fin k) (s : Fin (N + 1)) : S :=
  z ((plE N k).symm (Function.update r l s))

theorem plk_update {S : Type} [CommRing S] (v : Fin k → Fin (N + 1) → S) (r : Fin k → Fin (N + 1)) (l : Fin k)
    (s : Fin (N + 1)) : rowOf (plk v id) r l s = (Matrix.of fun a b => v a (r b)).cramer (fun a => v a s) l := by
  rw [Matrix.cramer_apply]
  simp only [rowOf, plk, Equiv.apply_symm_apply, id]
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.updateCol_apply, Function.update_apply]
  split_ifs <;> rfl

theorem exists_mat {K : Type} [Field K] (v : Fin k → Fin (N + 1) → K) (z : Fin (plN N k + 1) → K) (u : Kˣ)
    (hz : z = u • plk v id) (i : Fin (plN N k + 1)) (hi : z i = 1) :
    ∃ M M' : Matrix (Fin k) (Fin k) K, M' * M = 1 ∧
      (∀ a s, v a s = ∑ l, M a l * rowOf z (plE N k i) l s) ∧
      (∀ l s, rowOf z (plE N k i) l s = ∑ a, M' l a * v a s) ∧
      ∀ l l', rowOf z (plE N k i) l (plE N k i l') = if l = l' then 1 else 0 := by
  classical
  set r := plE N k i with hr
  set M : Matrix (Fin k) (Fin k) K := Matrix.of fun a b => v a (r b) with hM
  have hdet : (u : K) * M.det = 1 := by
    rw [← hi, hz]
    rfl
  have hrow : ∀ l s, rowOf z r l s = (u : K) * M.cramer (fun a => v a s) l := fun l s => by
    rw [← plk_update, hz]
    rfl
  have h1 : ∀ a s, v a s = ∑ l, M a l * rowOf z r l s := fun a s => by
    have h2 := congrFun (Matrix.mulVec_cramer M fun a => v a s) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
    simp only [hrow]
    calc v a s = (u : K) * (M.det * v a s) := by rw [← mul_assoc, hdet, one_mul]
      _ = _ := by
        rw [← h2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
  have hu : IsUnit M.det := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hdet)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hu
  have h3 : ∀ l s, rowOf z r l s = ∑ a, M⁻¹ l a * v a s := fun l s => by
    have : (Matrix.of fun l s => rowOf z r l s) = M⁻¹ * Matrix.of v := by
      rw [show Matrix.of v = M * Matrix.of (fun l s => rowOf z r l s) from by
        ext a s; simpa [Matrix.mul_apply] using h1 a s, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    simpa [Matrix.mul_apply] using congrFun (congrFun this l) s
  refine ⟨M, M⁻¹, hinv, h1, h3, fun l l' => ?_⟩
  rw [h3]
  have := congrFun (congrFun hinv l) l'
  simpa [Matrix.mul_apply, Matrix.one_apply, hM] using this

theorem exists_complete {R κ : Type} [CommRing R] [Field κ] (ρ : R →+* κ) {n : ℕ} (hk : k ≤ n) (η D : Fin k → Fin n → R)
    (hD : ∀ l l', ∑ j, D l' j * η l j = if l = l' then 1 else 0) :
    ∃ B : Matrix (Fin n) (Fin n) R, (∀ l j, B j (Fin.castLE hk l) = η l j) ∧ ρ B.det ≠ 0 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  let vR : Fin k ⊕ Fin (k + m) → Fin (k + m) → R := Sum.elim η fun j => Pi.single j 1
  let v : Fin k ⊕ Fin (k + m) → Fin (k + m) → κ := fun c => ρ ∘ vR c
  have hin : LinearIndependent κ (v ∘ Sum.inl) := by
    refine Fintype.linearIndependent_iff.2 fun g hg l' => ?_
    have h1 := congrArg (fun y : Fin (k + m) → κ => ∑ j, ρ (D l' j) * y j) hg
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at h1
    rw [Finset.sum_comm] at h1
    have h2 : ∀ l, ∑ j, ρ (D l' j) * (g l * (v ∘ Sum.inl) l j) = g l * ρ (if l = l' then 1 else 0) := fun l => by
      rw [← hD l l', map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [v, vR, Function.comp_apply, Sum.elim_inl, map_mul]
      ring
    simp only [h2] at h1
    simpa using h1
  obtain ⟨b, -, hsb, hsp, hb⟩ := exists_linearIndepOn_extension (K := κ) (v := v) (s := Set.range Sum.inl)
    (t := Set.univ) ((linearIndepOn_range_iff Sum.inl_injective v).2 hin) (Set.subset_univ _)
  let J : Set (Fin (k + m)) := {j | Sum.inr j ∈ b}
  let w : Fin k ⊕ J → Fin k ⊕ Fin (k + m) := Sum.elim Sum.inl fun j => Sum.inr j.1
  have hw : Function.Injective w := by
    rintro (a | a) (c | c) h
    · exact congrArg _ (Sum.inl_injective h)
    · exact (Sum.inl_ne_inr h).elim
    · exact (Sum.inr_ne_inl h).elim
    · exact congrArg _ (Subtype.ext (Sum.inr_injective h))
  have hrange : Set.range w = b := by
    ext c
    constructor
    · rintro ⟨a | a, rfl⟩
      · exact hsb ⟨a, rfl⟩
      · exact a.2
    · intro hc
      rcases c with c | c
      · exact ⟨Sum.inl c, rfl⟩
      · exact ⟨Sum.inr ⟨c, hc⟩, rfl⟩
  have hli : LinearIndependent κ (v ∘ w) := (linearIndepOn_range_iff hw v).1 (hrange ▸ hb)
  have hsp' : ⊤ ≤ Submodule.span κ (Set.range (v ∘ w)) := by
    rw [Set.range_comp, hrange, ← (Pi.basisFun κ (Fin (k + m))).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine hsp ⟨Sum.inr j, Set.mem_univ _, ?_⟩
    funext i
    simp [v, vR, Pi.single_apply, apply_ite ρ]
  have := Fintype.ofFinite J
  have hcard : Fintype.card J = m := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp')
    simp only [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
    omega
  let T : Fin (k + m) ≃ Fin k ⊕ J :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hcard).symm)
  refine ⟨Matrix.of fun j c => vR (w (T c)) j, fun l j => ?_, ?_⟩
  · have : T (Fin.castLE hk l) = Sum.inl l := by
      simp only [T, Equiv.trans_apply]
      rw [show Fin.castLE hk l = Fin.castAdd m l from rfl, finSumFinEquiv_symm_apply_castAdd]
      rfl
    simp [this, w, vR]
  · have h1 : LinearIndependent κ ((Matrix.of fun j c => vR (w (T c)) j).map ρ).col := hli.comp T T.injective
    have h2 := Matrix.linearIndependent_cols_iff_isUnit.1 h1
    have h3 := (Matrix.isUnit_iff_isUnit_det _).1 h2
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h3
    exact h3.ne_zero

end Lin

section Geom

open GlobalTheory.ProjSpace GlobalTheory.FlagMod LineOfMap

variable {O : Type} [CommRing O] {Z Z' : Scheme.{0}} {C : Coc Z} {N k : ℕ}

theorem exists_unit_of_car (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) {U : Z'.Opens}
    {i : Fin (plN N k + 1)} (hi : U ≤ q ⁻¹ᵁ chart O _ i) {K : Type} [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U)
    {α : C.A} (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) {ξ : Fin k → Fin (C.n α) → K} (hc : Car Em f q w α h ξ) :
    ∃ u : Kˣ, (fun j => ev w U hw (pullRatio q U i hi j)) =
      u • plk (fun l => ((Em.A α).map (ev (w ≫ f) _ h)).mulVec (ξ l)) id := by
  obtain ⟨g, hv, e⟩ := hc
  obtain ⟨hv', e'⟩ := comp_eq_pt q hi w hw g (by rw [e, pt_str])
  exact (pt_eq_pt_iff g hv hv').1 (e.symm.trans e')

theorem span_of_rows {K : Type} [Field K] {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (T : V →ₗ[K] V') (T' : V' →ₗ[K] V) (hT : ∀ y, T' (T y) = y) (ξ : Fin k → V) (n : Fin k → V')
    (M M' : Matrix (Fin k) (Fin k) K) (h1 : ∀ a, T (ξ a) = ∑ l, M a l • n l) (h2 : ∀ l, n l = ∑ a, M' l a • T (ξ a)) :
    (∀ a, ξ a = ∑ l, M a l • T' (n l)) ∧ ∀ l, T (T' (n l)) = n l := by
  refine ⟨fun a => ?_, fun l => ?_⟩
  · rw [← hT (ξ a), h1, map_sum]
    exact Finset.sum_congr rfl fun l _ => map_smul _ _ _
  · have : n l = T (∑ a, M' l a • ξ a) := by simp only [map_sum, map_smul, ← h2]
    rw [this, hT]

theorem planar_of_generic : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (Ω : Set Z'), IsReduced Z' → Dense Ω → (∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), ∃ ξ, Car Em f q w α h ξ) → Planar Em f q := by
  intro O _ Z Z' C N k Em f q Ω hred hΩ H x
  classical
  obtain ⟨α, hα⟩ := C.cover (f x)
  obtain ⟨i, hi⟩ := exists_mem_chart O _ (q x)
  obtain ⟨A', hA'⟩ := Em.linv α
  let U : Z'.Opens := f ⁻¹ᵁ C.B α ⊓ q ⁻¹ᵁ chart O _ i
  have hxU : x ∈ U := ⟨hα, hi⟩
  by_cases hk : k ≤ C.n α
  swap
  · obtain ⟨_, ⟨B, hB, rfl⟩, hxB, hle⟩ := Z'.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    exact ⟨B, hB, α, 1, hxB, fun y hy => (hle hy).1, fun K _ w hw h ξ _ l j hj => absurd j.2 (by omega)⟩
  let φ : Γ(Z, C.B α) →+* Γ(Z', U) := (f.appLE (C.B α) U inf_le_left).hom
  let ζ : Fin (plN N k + 1) → Γ(Z', U) := pullRatio q U i inf_le_right
  let r := plE N k i
  let n : Fin k → Fin (N + 1) → Γ(Z', U) := rowOf ζ r
  let η : Fin k → Fin (C.n α) → Γ(Z', U) := fun l => (A'.map φ).mulVec (n l)
  have hev : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) {m n : ℕ}
      (M : Matrix (Fin m) (Fin n) Γ(Z, C.B α)) (v : Fin n → Γ(Z', U)),
      (fun j => ev w U hw ((M.map φ).mulVec v j)) =
        (M.map (ev (w ≫ f) _ (le_preimage_map f inf_le_left hw))).mulVec fun j => ev w U hw (v j) := by
    intro K _ w hw m n M v
    funext j
    rw [RingHom.map_mulVec, Matrix.map_map]
    congr 2
    exact funext fun a => ev_appLE w f _ hw _ a

  have pw : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α)
      (ξ : Fin k → Fin (C.n α) → K), Car Em f q w α h ξ →
      ∃ M : Matrix (Fin k) (Fin k) K, (∀ a, ξ a = ∑ l, M a l • fun j => ev w U hw (η l j)) ∧
        (∀ l, ((Em.A α).map (ev (w ≫ f) _ h)).mulVec (fun j => ev w U hw (η l j)) = fun s => ev w U hw (n l s)) ∧
        ∀ l l', ev w U hw (n l (r l')) = if l = l' then 1 else 0 := by
    intro K _ w hw h ξ hc
    obtain ⟨u, hu⟩ := exists_unit_of_car Em f q inf_le_right w hw h hc
    obtain ⟨M, M', -, h1, h2, h3⟩ := exists_mat _ _ u hu i (by
      show ev w U hw (ζ i) = 1
      rw [show ζ i = 1 from pullRatio_self, map_one])
    have hη : ∀ l, (fun j => ev w U hw (η l j)) =
        (A'.map (ev (w ≫ f) _ h)).mulVec fun s => ev w U hw (n l s) := fun l => hev K w hw A' (n l)
    have hl : ∀ y, (A'.map (ev (w ≫ f) _ h)).mulVecLin (((Em.A α).map (ev (w ≫ f) _ h)).mulVecLin y) = y := fun y => by
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hA',
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    obtain ⟨s1, s2⟩ := span_of_rows _ _ hl ξ (fun l s => ev w U hw (n l s)) M M'
      (fun a => funext fun s => by rw [Finset.sum_apply]; exact h1 a s)
      (fun l => funext fun s => by rw [Finset.sum_apply]; exact h2 l s)
    refine ⟨M, fun a => ?_, fun l => ?_, h3⟩
    · simpa only [hη, Matrix.mulVecLin_apply] using s1 a
    · rw [hη]
      exact s2 l
  have E1 : ∀ l, ((Em.A α).map φ).mulVec (η l) = n l := fun l => by
    funext s
    refine sub_eq_zero.1 (eq_zero_of_dense hΩ _ fun K _ w hwΩ hw => ?_)
    have h := le_preimage_map f (inf_le_left : U ≤ _) hw
    obtain ⟨ξ, hξ⟩ := H K w hwΩ α h
    obtain ⟨M, -, h2, -⟩ := pw K w hw h ξ hξ
    rw [map_sub, sub_eq_zero]
    exact (congrFun (hev K w hw (Em.A α) (η l)) s).trans (congrFun (h2 l) s)
  have E2 : ∀ l l', n l (r l') = if l = l' then 1 else 0 := fun l l' => by
    refine sub_eq_zero.1 (eq_zero_of_dense hΩ _ fun K _ w hwΩ hw => ?_)
    have h := le_preimage_map f (inf_le_left : U ≤ _) hw
    obtain ⟨ξ, hξ⟩ := H K w hwΩ α h
    obtain ⟨M, -, -, h3⟩ := pw K w hw h ξ hξ
    rw [map_sub, sub_eq_zero, h3, apply_ite (ev w U hw), map_one, map_zero]
  have hD : ∀ l l', ∑ j, ((Em.A α).map φ) (r l') j * η l j = if l = l' then 1 else 0 := fun l l' =>
    (congrFun (E1 l) (r l')).trans (E2 l l')
  have hwx := residue_le hxU
  obtain ⟨Bm, hB1, hB2⟩ := exists_complete (ev _ U hwx) hk η (fun l' => ((Em.A α).map φ) (r l')) hD
  have hxb : x ∈ Z'.basicOpen Bm.det := by
    have := mem_basicOpen_of_isUnit_ev _ U hwx _ (Ne.isUnit hB2) (IsLocalRing.closedPoint _)
    exact (Scheme.fromSpecResidueField_apply x _) ▸ this
  obtain ⟨_, ⟨B, hB, rfl⟩, hxB, hle⟩ := Z'.isBasis_affineOpens.exists_subset_of_mem_open hxb (Z'.basicOpen Bm.det).isOpen
  have hBU : B ≤ U := fun y hy => Z'.basicOpen_le _ (hle hy)
  let res : Γ(Z', U) →+* Γ(Z', B) := (Z'.presheaf.map (homOfLE hBU).op).hom
  have hu : IsUnit (Bm.map res).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_of_basicOpen_eq _ ((Scheme.basicOpen_res _ _ _).trans (inf_eq_left.2 hle))
  let b : GL (Fin (C.n α)) Γ(Z', B) := Matrix.nonsingInvUnit _ hu
  refine ⟨B, hB, α, b⁻¹, hxB, hBU.trans inf_le_left, fun K _ w hw h ξ hc l j hj => ?_⟩
  have hwU := le_preimage_mono hBU hw
  obtain ⟨M, h1, -, -⟩ := pw K w hwU h ξ hc
  have h0 : ∀ l', ∑ i', ev w B hw ((b⁻¹ : GL (Fin (C.n α)) Γ(Z', B)).1 j i') * ev w U hwU (η l' i') = 0 := fun l' => by
    have e0 : (b⁻¹ : GL (Fin (C.n α)) Γ(Z', B)).1 * Bm.map res = 1 := b.inv_mul
    have e1 := congrArg (ev w B hw) (congrFun (congrFun e0 j) (Fin.castLE hk l'))
    have hne : j ≠ Fin.castLE hk l' := fun e => by
      have := congrArg Fin.val e
      have := l'.2
      simp only [Fin.val_castLE] at *
      omega
    rw [Matrix.one_apply_ne hne, map_zero, Matrix.mul_apply, map_sum] at e1
    refine Eq.trans (Finset.sum_congr rfl fun i' _ => ?_) e1
    rw [map_mul, Matrix.map_apply, hB1]
    exact congrArg _ (ev_res w hBU hw hwU _).symm
  rw [h1 l]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l' _ => ?_
  rw [← mul_zero (M l l'), ← h0 l', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i' _ => mul_left_comm _ _ _

end Geom

end GlobalTheory.GrCl.PlanarMap
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.planar_of_dense_carriers : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (Ω : Set Z'), IsReduced Z' → Dense Ω → (∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), ∃ ξ, Car Em f q w α h ξ) → Planar Em f q := by
  atlas_forward_decl GlobalTheory.GrCl.PlanarMap.planar_of_generic
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrCl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X}

def LCrd.frvecEmbL (D : LCrd M π) (α : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) :
    TanM (z ≫ π) M.t.G →ₗ[S] (Fin (D.N + 1) → S) :=
  (Matrix.mulVecLin ((D.Em.A α).map (ev z _ h))).comp (D.crd α S z h)

theorem LCrd.frvec_emb_tanPull (D : LCrd M π) (α : D.C.A) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (h' : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ D.C.B α)
    (e : spMap φ ≫ z ≫ π = (spMap φ ≫ z) ≫ π) (v : TanM (z ≫ π) M.t.G) :
    D.emb α (spMap φ ≫ z) h' (tanPull φ e v) = φ ∘ D.emb α z h v := by
  unfold LCrd.emb
  rw [D.bc α S S' φ z _ rfl h h' e v, FlagMod.ev_spMap φ z _ h h']
  funext r
  rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_map]
  rfl

theorem LCrd.frvec_exists_emb_eq_smul (D : LCrd M π) (α β : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (hα : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ D.C.B β) :
    ∃ u : Sˣ, ∀ v, D.emb α z hα v = (u : S) • D.emb β z hβ v := by
  obtain ⟨u, hu⟩ := D.Em.compat α β S z hα hβ
  refine ⟨u, fun v => ?_⟩
  unfold LCrd.emb
  rw [← D.tr α β S z hα hβ v, Matrix.mulVec_mulVec]
  rw [hu]
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem LCrd.frvec_emb_injective (D : LCrd M π) (α : D.C.A) {K : Type} [Field K] (z : Sp K ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α)
    (hz : Set.range z ⊆ π ⁻¹' Set.range M.j) : Function.Injective (D.frvecEmbL α z h) := by
  obtain ⟨A', hA'⟩ := D.Em.linv α
  have h1 : A'.map (ev z _ h) * (D.Em.A α).map (ev z _ h) = 1 := by
    rw [← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _)]
  intro x y hxy
  simp only [LCrd.frvecEmbL, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply] at hxy
  have := congrArg (fun w => (A'.map (ev z _ h)).mulVec w) hxy
  simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
  exact D.inj α K z h hz this

theorem frvec_initSpan_map {K P Q : Type} [Field K] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q] {m : ℕ}
    (F : P →ₗ[K] Q) (v : Fin m → P) (e : ℕ) : initSpan K (fun i => F (v i)) e = (initSpan K v e).map F := by
  rw [initSpan, initSpan, Submodule.map_span, Set.image_image]

theorem frvec_initSpan_smul {K Q : Type} [Field K] [AddCommGroup Q] [Module K Q] {m : ℕ}
    (u : Kˣ) (v : Fin m → Q) (e : ℕ) : initSpan K (fun i => (u : K) • v i) e = initSpan K v e := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, hj, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rintro _ ⟨j, hj, rfl⟩
    have : v j = ((u⁻¹ : Kˣ) : K) • ((u : K) • v j) := by rw [smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

theorem frvec_initSpan_top {K Q : Type} [Field K] [AddCommGroup Q] [Module K Q] {m : ℕ}
    (v : Fin m → Q) : initSpan K v m = Submodule.span K (Set.range v) := by
  have : {j : Fin m | (j : ℕ) < m} = Set.univ := Set.eq_univ_of_forall fun j => j.2
  rw [initSpan, this, Set.image_univ]

theorem exists_isFrVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (D : LCrd M π) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A), (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ (cv Dv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a), IsFrVec D A σ α cv ∧ (∀ a, LeftInv (Dv a) (cv a)) ∧ ∀ (K : Type) [Field K] (a a' : A.ch.ι) (φ : A.ch.R a →+* K) (φ' : A.ch.R a' →+* K), spMap φ ≫ A.ch.χ a = spMap φ' ≫ A.ch.χ a' → ∀ e : ℕ, e ∈ ty σ ∨ e = 0 ∨ e = Dw.mult σ → initSpan K (fun i => φ ∘ cv a i) e = initSpan K (fun i => φ' ∘ cv a' i) e := by
  intro E _ _ _ H Dw l Xo c V M X π ty A D σ α hα
  have hu : ∀ a, ∃ u : TVecs Dw M.t (A.ch.χ a ≫ π), up u = A.fr a :=
    fun a => exists_up fun σ i => ((A.frame a).1 σ i).1
  choose u₀ hu₀ using hu
  let cv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a :=
    fun a i => D.emb (α a) (A.ch.χ a) (hα a) (u₀ a σ i)
  have key : IsFrVec D A σ α cv := by
    intro a S _ φ z ez h u hup i
    subst ez
    have e' : spMap φ ≫ A.ch.χ a ≫ π = (spMap φ ≫ A.ch.χ a) ≫ π := (Category.assoc _ _ _).symm
    have hu : u = fun σ i => tanPull φ e' (u₀ a σ i) := by
      apply up_injective
      rw [up_tanPull, hu₀, hup]
    rw [hu]
    exact (D.frvec_emb_tanPull (α a) φ (A.ch.χ a) (hα a) h e' (u₀ a σ i)).symm
  have li : ∀ (a : A.ch.ι) (K : Type) [Field K] (φ : A.ch.R a →+* K),
      LinearIndependent K fun i => φ ∘ cv a i := by
    intro a K _ φ
    have h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a) := FlagMod.le_preimage_comp _ (hα a)
    obtain ⟨u, hu⟩ := A.exists_up_fr (rfl : spMap φ ≫ A.ch.χ a = _)
    have hf := A.isFrame_bc (rfl : spMap φ ≫ A.ch.χ a = _)
    rw [← hu] at hf
    have hr : Set.range (spMap φ ≫ A.ch.χ a) ⊆ π ⁻¹' Set.range M.j := by
      rw [← A.cover]
      exact A.ch.range_subset rfl
    have := ((isFrame_up_iff _ _).1 hf σ).1.map' (D.frvecEmbL (α a) _ h)
      (LinearMap.ker_eq_bot.2 (D.frvec_emb_injective (α a) _ h hr))
    have e : (fun i => φ ∘ cv a i) = D.frvecEmbL (α a) _ h ∘ u σ := funext fun i => key a K φ _ rfl h u hu i
    rw [e]
    exact this
  have hD : ∀ a, ∃ Dv : Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a, LeftInv Dv (cv a) := by
    intro a
    obtain ⟨Q, hQ⟩ := GlobalTheory.matrix_exists_left_inverse_of_forall_field (A.ch.R a) (D.N + 1) (Dw.mult σ)
      (Matrix.of fun r i => cv a i r) fun K _ φ => by
        rw [Matrix.mulVec_injective_iff]
        exact li a K φ
    refine ⟨fun z r => Q z r, fun z z' => ?_⟩
    have := congrFun (congrFun hQ z) z'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.of_apply] at this
    convert this
  choose Dv hDv using hD
  refine ⟨cv, Dv, key, hDv, fun K _ a a' φ φ' hz e he => ?_⟩
  have h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a) := FlagMod.le_preimage_comp _ (hα a)
  have h' : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a') := by
    rw [hz]; exact FlagMod.le_preimage_comp _ (hα a')
  obtain ⟨u, hu⟩ := A.exists_up_fr (rfl : spMap φ ≫ A.ch.χ a = _)
  obtain ⟨u', hu'⟩ := A.exists_up_fr hz.symm
  obtain ⟨s, hs⟩ := D.frvec_exists_emb_eq_smul (α a') (α a) _ h' h
  have e1 : (fun i => φ ∘ cv a i) = fun i => D.frvecEmbL (α a) _ h (u σ i) :=
    funext fun i => key a K φ _ rfl h u hu i
  have e2 : (fun i => φ' ∘ cv a' i) = fun i => (s : K) • D.frvecEmbL (α a) _ h (u' σ i) :=
    funext fun i => (key a' K φ' _ hz.symm h' u' hu' i).trans (hs _)
  rw [e1, e2, frvec_initSpan_smul, frvec_initSpan_map, frvec_initSpan_map]
  congr 1
  rcases he with he | rfl | rfl
  · have f1 := A.flagAt_fr (rfl : spMap φ ≫ A.ch.χ a = _)
    have f2 := A.flagAt_fr hz.symm
    rw [← hu] at f1
    rw [← hu'] at f2
    exact Atlas.FlagAt.initSpan_eq f1 f2 σ he
  · simp [initSpan]
  · have f1 := A.isFrame_bc (rfl : spMap φ ≫ A.ch.χ a = _)
    have f2 := A.isFrame_bc hz.symm
    rw [← hu] at f1
    rw [← hu', ← A.alg_eq rfl hz.symm] at f2
    rw [frvec_initSpan_top, frvec_initSpan_top, ((isFrame_up_iff _ _).1 f1 σ).2, ((isFrame_up_iff _ _).1 f2 σ).2]

end GlobalTheory.GrCl
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_lattice_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (D : LCrd M π) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A), (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ (cv Dv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a), IsFrVec D A σ α cv ∧ (∀ a, LeftInv (Dv a) (cv a)) ∧ ∀ (K : Type) [Field K] (a a' : A.ch.ι) (φ : A.ch.R a →+* K) (φ' : A.ch.R a' →+* K), spMap φ ≫ A.ch.χ a = spMap φ' ≫ A.ch.χ a' → ∀ e : ℕ, e ∈ ty σ ∨ e = 0 ∨ e = Dw.mult σ → initSpan K (fun i => φ ∘ cv a i) e = initSpan K (fun i => φ' ∘ cv a' i) e := by
  atlas_forward_decl GlobalTheory.GrCl.exists_isFrVec
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_coordinates_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X), IsMap Z t.B g → ∃ D : LCrd (Y Z.i) Z.π, IsLat t Z g D := by
  first | exact @GlobalTheory.GrCl.exists_lCrd_isLat | exact GlobalTheory.GrCl.exists_lCrd_isLat | (intros; apply GlobalTheory.GrCl.exists_lCrd_isLat <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan ev_appLE ev_spMap_tau tau tau_le le_preimage_comp le_preimage_map le_preimage_mono)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
open GlobalTheory.LocM.MapComp GlobalTheory.LocM.CommonMod GlobalTheory.LocM.StepMono

namespace GlobalTheory.GrCl.RowCombination

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_comb {Z₁ Z B : Mdl Y i₀} {g : Z.X ⟶ B.X} (hg : IsMap Z B g) {X' : Scheme.{0}} {f : X' ⟶ Z.X}
    {ty' : (E →+* ℂ) → Finset ℕ} {A' : Atlas (Y Z.i) (f ≫ Z.π) ty'} {h : Z₁.X ⟶ X'} (hm : MapsTo Z₁ A' h)
    (hf : IsMap Z₁ Z (h ≫ f)) {σ : E →+* ℂ} {r : ℕ} (hr : r ∈ Z₁.ty σ) {K : Type} [Field K] {w : Sp K ⟶ Z₁.X}
    {v : Sp (DualNumber K) ⟶ B.t.G.left} (hs : InStep Z₁ B σ r w v) :
    ∃ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ)
      (u : TVecs Dw (Y Z.i).t (((w ≫ h) ≫ f) ≫ Z.π)) (cf : Fin (Dw.mult σ) → K),
      LocM.IsTrans B.i Z.i τ mu ∧ Set.range ((w ≫ h) ≫ f) ⊆ Z.opn ∧ A'.FlagAt (w ≫ h) (up u) ∧
        (∀ j : Fin (Dw.mult σ), r ≤ (j : ℕ) → cf j = 0) ∧
        v ≫ B.tMap.φ = (tv (∑ j, cf j • u σ j)).left ≫ mu.φ := by
  obtain ⟨τ₁, mu₁, u₁, i, t₁, fu₁, hi, hv⟩ := hs
  have hw := range_subset_opn Z₁ fu₁
  obtain ⟨τ, mu, u, t, e, fu, fu'⟩ := hm K w hw
  have hz : Set.range ((w ≫ h) ≫ f) ⊆ Z.opn := by
    rintro _ ⟨x, rfl⟩
    have := map_mem_opn hf (hw ⟨x, rfl⟩)
    simpa only [Scheme.Hom.comp_apply] using this
  obtain ⟨τ₀, mu₀, -, t₀, -⟩ := hg.2 K _ hz
  obtain ⟨mu', hmu'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mu₀ mu
  have t' := isTrans_comp hg.1.1 hf.1.1 t₀ t mu' hmu'
  obtain ⟨-, hmu⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ _ _ mu₁ mu' (hg.1.2.1.trans hf.1.2.1) t₁ t'
  obtain ⟨c, gu, gu₁, hsf⟩ := flagAt_two Z₁ fu fu₁
  obtain ⟨cf, hcf, hc⟩ := hsf σ r hr i hi
  have e' : (w ≫ Z₁.π) ≫ τ = ((w ≫ h) ≫ f) ≫ Z.π := by
    rw [Category.assoc, ← e]; simp only [Category.assoc]
  have hc' := comb_push mu hc
  rw [e'] at hc'
  obtain ⟨U, hU⟩ := exists_up (Dw := Dw) (u := fun σ j => u σ j ≫ mu.φ)
    fun σ j => isTan_push mu _ e' (gu.1 σ j).1
  have hcomb : tanOf (isTan_push mu _ e' (gu₁.1 σ i).1) = ∑ j, cf j • U σ j := by
    refine (isComb_iff (U σ) cf _).1 ?_
    have : (fun j => (tv (U σ j)).left) = fun j => u σ j ≫ mu.φ := congrFun hU σ
    rw [this]
    exact hc'
  obtain ⟨a, φ, ha, -⟩ := fu₁
  obtain ⟨y, hy, -⟩ := exists_lift_chart Z₁ ha
  refine ⟨τ₀, mu₀, U, cf, t₀, hz, hU ▸ fu', hcf, hv.trans ?_⟩
  rw [← hcomb, left_tanOf, hmu K y _ _ _ (by rw [hy]; exact (gu₁.1 σ i).1.1), hmu', Category.assoc]

theorem row_comb {K N : Type} [Field K] [AddCommGroup N] [Module K N] {m n r : ℕ} (hr : r ≤ m) (L : N →ₗ[K] (Fin n → K))
    (a : Fin n → K) (u : Fin m → N) (cf : Fin m → K) (hcf : ∀ j : Fin m, r ≤ (j : ℕ) → cf j = 0)
    (ha : ∀ l : Fin r, ∑ i, a i * L (u (Fin.castLE hr l)) i = 0) : ∑ i, a i * L (∑ j, cf j • u j) i = 0 := by
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ (j : ℕ)
  · simp [hcf j hj]
  · have := ha ⟨j, by omega⟩
    simp only [mul_left_comm _ (cf j), ← Finset.mul_sum]
    exact mul_eq_zero_of_right _ this

theorem holds_of_planar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → Planar D.Em f q → ∀ (Z₁ : Mdl Y i₀) (h : Z₁.X ⟶ X'), MapsTo Z₁ A' h → IsMap Z₁ Z (h ≫ f) → t.k ∈ Z₁.ty t.σ → t.Holds Z₁ := by
  intro E _ _ _ H Dw Xo p W Y i₀ _ _ t Z g D hg hL A X' f q ty' A' _ hG hP Z₁ h hm hf hk
  refine ⟨hk, (h ≫ f) ≫ g, isMap_comp hf hg, fun x => ?_⟩
  obtain ⟨U, -, α, a, hx, hUα, H₁⟩ := hP (h x)
  obtain ⟨V, m, hαV, hfr, H₂⟩ := hL α
  obtain ⟨_, ⟨U', hU', rfl⟩, hx', hle⟩ := Z₁.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((h ⁻¹ᵁ U : Z₁.X.Opens) : Set Z₁.X) from hx) (h ⁻¹ᵁ U).2
  have e : U' ≤ h ⁻¹ᵁ U := hle
  refine ⟨U', hU', V, _, m, Matrix.GeneralLinearGroup.map (h.appLE U U' e).hom a, hx',
    fun y hy => hαV (hUα (e hy)), hfr, fun K _ φ v hv hh hs j hj => ?_⟩
  have h₀ : ⊤ ≤ (spMap φ ≫ tau hU') ⁻¹ᵁ U' := le_preimage_comp _ (tau_le hU' le_rfl)
  have eφ := ev_spMap_tau hU' φ h₀
  change IsTanAtG t.B.t ((spMap φ ≫ tau hU') ≫ _) v at hv
  change InStep Z₁ t.B t.σ t.k (spMap φ ≫ tau hU') v at hs
  change ⊤ ≤ ((spMap φ ≫ tau hU') ≫ _) ⁻¹ᵁ V at hh
  change ∑ l, φ ((h.appLE U U' e).hom (a j l)) * tanEv t.B.t hv hh _ = 0
  generalize spMap φ ≫ tau hU' = w at h₀ eφ hv hs hh
  subst eφ
  have h₁ : ⊤ ≤ (w ≫ h) ⁻¹ᵁ U := le_preimage_map h e h₀
  have h₂ : ⊤ ≤ ((w ≫ h) ≫ f) ⁻¹ᵁ D.C.B α := le_preimage_map f hUα h₁
  obtain ⟨τ, mu, u, cf, tr, hz, fu, hcf, hvv⟩ := exists_comb hg hm hf hk hs
  have eq : w ≫ (h ≫ f) ≫ g = ((w ≫ h) ≫ f) ≫ g := by simp only [Category.assoc]
  obtain ⟨hv', hh', he⟩ := tanEv_congr t.B.t eq hv hh
  have key := row_comb t.le (D.crd α K _ h₂) (fun i => ev (w ≫ h) U h₁ (a j i)) (u t.σ) cf hcf
    fun l => H₁ K _ h₁ h₂ _ (((hG K _ u).1 fu).2 α h₂) l j hj
  refine (Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (ev_appLE w h e h₀ h₁ _) ?_).trans key
  exact (he _).trans (H₂ τ mu tr K _ h₂ hz _ v hv' hh' hvv l).symm

end GlobalTheory.GrCl.RowCombination
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_atlas_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → Planar D.Em f q → ∀ (Z₁ : Mdl Y i₀) (h : Z₁.X ⟶ X'), MapsTo Z₁ A' h → IsMap Z₁ Z (h ≫ f) → t.k ∈ Z₁.ty t.σ → t.Holds Z₁ := by
  atlas_forward_decl GlobalTheory.GrCl.RowCombination.holds_of_planar
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.GrCl.Annih

theorem exists_trans {X : Scheme.{0}} {F : X.Modules} {V₁ V₂ : X.Opens} {n₁ n₂ : ℕ} {m₁ : Fin n₁ → Γ(F, V₁)}
    {m₂ : Fin n₂ → Γ(F, V₂)} (h₁ : VB.IsFrame m₁) (h₂ : VB.IsFrame m₂) :
    ∃ (T : Matrix (Fin n₁) (Fin n₂) Γ(X, V₁ ⊓ V₂)) (T' : Matrix (Fin n₂) (Fin n₁) Γ(X, V₁ ⊓ V₂)),
      T * T' = 1 ∧ T' * T = 1 ∧ ∀ l, resM F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) (m₁ l) =
        ∑ i, T l i • resM F (inf_le_right : V₁ ⊓ V₂ ≤ V₂) (m₂ i) := by
  let b₁ := h₁.basis (inf_le_left : V₁ ⊓ V₂ ≤ V₁)
  let b₂ := h₂.basis (inf_le_right : V₁ ⊓ V₂ ≤ V₂)
  refine ⟨(b₂.toMatrix b₁).transpose, (b₁.toMatrix b₂).transpose, ?_, ?_, fun l => ?_⟩
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · have := b₂.sum_toMatrix_smul_self b₁ l
    simp only [b₁, b₂, VB.IsFrame.basis_apply] at this
    exact this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem tanEv_trans {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
    {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) {F : X.Modules} (θ : F ⟶ GlobalTheory.LieVB.omega t.G)
    {V₁ V₂ : X.Opens} {n : ℕ} {s : Γ(F, V₁)} {m : Fin n → Γ(F, V₂)} {c : Fin n → Γ(X, V₁ ⊓ V₂)}
    (e : resM F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) s = ∑ i, c i • resM F (inf_le_right : V₁ ⊓ V₂ ≤ V₂) (m i))
    (h₁ : ⊤ ≤ x ⁻¹ᵁ V₁) (h₂ : ⊤ ≤ x ⁻¹ᵁ V₂) (h : ⊤ ≤ x ⁻¹ᵁ (V₁ ⊓ V₂)) :
    tanEv t hv h₁ (θ.app V₁ s) = ∑ i, ev x _ h (c i) * tanEv t hv h₂ (θ.app V₂ (m i)) := by
  let L : Γ(GlobalTheory.LieVB.omega t.G, V₁ ⊓ V₂) →+ k := AddMonoidHom.mk' (tanEv t hv h) (tanEv_add t hv h)
  have e₁ : tanEv t hv h₁ (θ.app V₁ s) = L (θ.app _ (resM F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) s)) := by
    rw [app_resM]
    exact (tanEv_resM t hv h inf_le_left _).symm
  rw [e₁, e, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, app_resM]
  refine (tanEv_smul t hv h _ _).trans ?_
  rw [tanEv_resM t hv h inf_le_right]
  rfl

theorem annih : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z₁.X) (α : D.C.A), ⊤ ≤ (z ≫ g₀) ⁻¹ᵁ D.C.B α → ∃ (n' : ℕ) (a : Matrix (Fin n') (Fin (D.C.n α)) R) (a' : Matrix (Fin (D.C.n α)) (Fin n') R), a * a' = 1 ∧ a' * a = 1 ∧ ∀ (τ : (Y Z₁.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z₁.i).t (Y Z.i).t τ) (u : Vecs Dw (Y Z₁.i).t K), LocM.IsTrans Z.i Z₁.i τ mu → Z₁.FlagAt (spMap (algebraMap R K) ≫ z) u → ∀ (y : Sp K ⟶ Z.X), y = spMap (algebraMap R K) ≫ z ≫ g₀ → ∀ (hy : ⊤ ≤ y ⁻¹ᵁ D.C.B α) (v : TanM (y ≫ Z.π) (Y Z.i).t.G) (i : Fin (Dw.mult t.σ)), (i : ℕ) < t.k → (tv v).left = u t.σ i ≫ mu.φ → ∀ j : Fin n', t.k ≤ (j : ℕ) → ∑ l, algebraMap R K (a j l) * D.crd α K y hy v l = 0 := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW t Z g D hg hL Z₁ g₀ hg₀ ⟨_, g₁, hg₁, hH⟩ R K _ _ _ _ z α hα
  obtain rfl : g₁ = g₀ ≫ g := MapUniq.isMap_unique E H Dw Xo p W Y i₀ hp hW _ _ _ _ hg₁ (MapComp.isMap_comp hg₀ hg)
  obtain ⟨U, hU, V₁, n', m₁, a₁, hx, hUV, hm₁, hA⟩ := hH (z (IsLocalRing.closedPoint R))
  have hzU : ⊤ ≤ z ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of R) z hx).ge
  obtain ⟨V, m, hV, hm, hc⟩ := hL α
  obtain ⟨T, T', hT, hT', hTm⟩ := exists_trans hm₁ hm
  have hz₁ : ⊤ ≤ (z ≫ g₀ ≫ g) ⁻¹ᵁ V₁ := FlagMod.le_preimage_map _ hUV hzU
  have hz₂ : ⊤ ≤ (z ≫ g₀ ≫ g) ⁻¹ᵁ V := by
    rw [← Category.assoc]
    exact FlagMod.le_preimage_map _ hV hα
  have hz := FlagMod.le_preimage_inf hz₁ hz₂
  refine ⟨n', a₁.1.map (ev z U hzU) * T.map (ev _ _ hz), T'.map (ev _ _ hz) * (a₁⁻¹).1.map (ev z U hzU), ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (T.map _), ← Matrix.map_mul, hT, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((a₁⁻¹).1.map _), ← Matrix.map_mul, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.map_mul, hT',
      Matrix.map_one _ (map_zero _) (map_one _)]
  intro τ mu u hτ hu y ey hy v i hi hv j hj
  have hyo : Set.range y ⊆ Z.opn := by
    rintro _ ⟨q, rfl⟩
    rw [ey, ← Category.assoc, Scheme.Hom.comp_apply]
    exact CommonMod.map_mem_opn hg₀ (MapComp.range_subset_opn Z₁ hu ⟨q, rfl⟩)
  obtain ⟨τ₀, mu₀, -, hτ₀, e₀, -⟩ := hg.2 K y hyo
  have e₀' : (y ≫ Z.π) ≫ τ₀ = (y ≫ g) ≫ t.B.π := (Category.assoc _ _ _).trans e₀.symm
  obtain ⟨v', ev'⟩ := (pushE t.B.tMap (y ≫ g) rfl).surjective (pushE mu₀ _ e₀' v)
  have hv' : (tv v').left ≫ t.B.tMap.φ = (tv v).left ≫ mu₀.φ := congrArg (fun q => (tv q).left) ev'
  obtain ⟨mu', hmu'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mu₀ mu
  have ew : spMap ((algebraMap R K).comp (ev z U hzU)) ≫ hU.fromSpec = spMap (algebraMap R K) ≫ z := by
    rw [← MapComp.sp_comp, Category.assoc, FlagMod.spMap_ev]
  have eyg : y ≫ g = spMap (algebraMap R K) ≫ z ≫ g₀ ≫ g := by simp only [ey, Category.assoc]
  have hyV : ⊤ ≤ (y ≫ g) ⁻¹ᵁ (V₁ ⊓ V) := eyg ▸ FlagMod.le_preimage_comp _ hz
  have hy₁ : ⊤ ≤ (y ≫ g) ⁻¹ᵁ V₁ := FlagMod.le_preimage_mono inf_le_left hyV
  have hy₂ : ⊤ ≤ (y ≫ g) ⁻¹ᵁ V := FlagMod.le_preimage_mono inf_le_right hyV
  have key := hA K ((algebraMap R K).comp (ev z U hzU)) (tv v').left
  rw [ew, Category.assoc, ← eyg] at key
  replace key := key (isTan_tv v') hy₁ ⟨τ ≫ τ₀, mu', u, i,
    MapComp.isTrans_comp hg.1.1 hg₀.1.1 hτ₀ hτ mu' hmu', hu, hi, by rw [hv', hv, hmu', Category.assoc]⟩ j hj
  have eev : ev (y ≫ g) _ hyV = (algebraMap R K).comp (ev _ _ hz) :=
    (FlagMod.ev_congr eyg _ _ (FlagMod.le_preimage_comp _ hz)).trans (FlagMod.ev_spMap _ _ _ _ _)
  rw [← key]
  simp only [hc τ₀ mu₀ hτ₀ K y hy hyo v _ (isTan_tv v') hy₂ hv', Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul,
    Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tanEv_trans t.B.t (isTan_tv v') t.L.N.incl (hTm l) hy₁ hy₂ hyV, eev, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

end GlobalTheory.GrCl.Annih
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_holds_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z₁.X) (α : D.C.A), ⊤ ≤ (z ≫ g₀) ⁻¹ᵁ D.C.B α → ∃ (n' : ℕ) (a : Matrix (Fin n') (Fin (D.C.n α)) R) (a' : Matrix (Fin (D.C.n α)) (Fin n') R), a * a' = 1 ∧ a' * a = 1 ∧ ∀ (τ : (Y Z₁.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z₁.i).t (Y Z.i).t τ) (u : Vecs Dw (Y Z₁.i).t K), LocM.IsTrans Z.i Z₁.i τ mu → Z₁.FlagAt (spMap (algebraMap R K) ≫ z) u → ∀ (y : Sp K ⟶ Z.X), y = spMap (algebraMap R K) ≫ z ≫ g₀ → ∀ (hy : ⊤ ≤ y ⁻¹ᵁ D.C.B α) (v : TanM (y ≫ Z.π) (Y Z.i).t.G) (i : Fin (Dw.mult t.σ)), (i : ℕ) < t.k → (tv v).left = u t.σ i ≫ mu.φ → ∀ j : Fin n', t.k ≤ (j : ℕ) → ∑ l, algebraMap R K (a j l) * D.crd α K y hy v l = 0 := by
  atlas_forward_decl GlobalTheory.GrCl.Annih.annih
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_independent_span_iff : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (K : Type) [Field K] (w : Sp K ⟶ Z') (β : C.A) (hβ : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B β) (ξ : Fin k → Fin (C.n β) → K), Car Em f q w β hβ ξ → LinearIndependent K ξ ∧ (∀ ξ' : Fin k → Fin (C.n β) → K, Car Em f q w β hβ ξ' ↔ LinearIndependent K ξ' ∧ Submodule.span K (Set.range ξ') = Submodule.span K (Set.range ξ)) ∧ ∀ (α : C.A) (hα : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), Car Em f q w α hα fun l => (C.tr α β (w ≫ f) hα hβ).mulVec (ξ l) := by
  first | exact @GlobalTheory.GrCl.car_span | exact GlobalTheory.GrCl.car_span | (intros; apply GlobalTheory.GrCl.car_span <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.IntPt

section Lin

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem span_cols {n k : ℕ} (hk : k ≤ n) (a a' : Matrix (Fin n) (Fin n) R) (h2 : a' * a = 1)
    (ξ : Fin k → Fin n → K) (hξ : LinearIndependent K ξ)
    (h0 : ∀ (l : Fin k) (j : Fin n), k ≤ (j : ℕ) → ∑ i, algebraMap R K (a j i) * ξ l i = 0) :
    LinearIndependent K (fun (l : Fin k) => algebraMap R K ∘ fun i => a' i (Fin.castLE hk l)) ∧
      Submodule.span K (Set.range fun (l : Fin k) => algebraMap R K ∘ fun i => a' i (Fin.castLE hk l)) =
        Submodule.span K (Set.range ξ) := by
  set φ := algebraMap R K with hφ
  set c : Fin k → Fin n → K := fun l => φ ∘ fun i => a' i (Fin.castLE hk l) with hc
  have hmap : a'.map φ * a.map φ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hmem : ∀ l, ξ l ∈ Submodule.span K (Set.range c) := fun l => by
    have e : ξ l = ∑ j : Fin n, (∑ i, φ (a j i) * ξ l i) • (fun r => φ (a' r j)) := by
      have := Matrix.mulVec_mulVec (ξ l) (a'.map φ) (a.map φ)
      rw [hmap, Matrix.one_mulVec] at this
      refine this.symm.trans ?_
      funext r
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : k ≤ (j : ℕ)
    · rw [h0 l j hj, zero_smul]
      exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, not_le.1 hj⟩, ?_⟩)
      rfl
  have hle : Submodule.span K (Set.range ξ) ≤ Submodule.span K (Set.range c) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hmem)
  have hf : Module.finrank K (Submodule.span K (Set.range ξ)) = k := by
    simpa using finrank_span_eq_card hξ
  have hc' : Module.finrank K (Submodule.span K (Set.range c)) ≤ k := by
    simpa [Set.finrank] using finrank_range_le_card (R := K) c
  have heq : Submodule.span K (Set.range ξ) = Submodule.span K (Set.range c) :=
    Submodule.eq_of_le_of_finrank_le hle (hc'.trans hf.ge)
  refine ⟨linearIndependent_iff_card_eq_finrank_span.2 ?_, heq.symm⟩
  rw [Set.finrank, ← heq, hf]
  simp

theorem unimod {M k n : ℕ} (hk : k ≤ n) (A : Matrix (Fin (M + 1)) (Fin n) R) (A' : Matrix (Fin n) (Fin (M + 1)) R)
    (hA : A' * A = 1) (a a' : Matrix (Fin n) (Fin n) R) (h1 : a * a' = 1) :
    Ideal.span (Set.range (plk (fun l : Fin k => A.mulVec fun i => a' i (Fin.castLE hk l)) id)) = ⊤ := by
  have h := GlobalTheory.FlagEmb.CauchyBinet.lform_plk R M k (Fin k) (Fin n) (fun j r => (a * A') j r)
    (fun l : Fin k => A.mulVec fun i => a' i (Fin.castLE hk l)) (Fin.castLE hk) id
  have hm : (Matrix.of fun l l' : Fin k => ∑ r, (a * A') (Fin.castLE hk l') r *
      (A.mulVec fun i => a' i (Fin.castLE hk (id l))) r) = 1 := by
    ext l l'
    have e : ∑ r, (a * A') (Fin.castLE hk l') r * (A.mulVec fun i => a' i (Fin.castLE hk (id l))) r =
        (a * a') (Fin.castLE hk l') (Fin.castLE hk l) := by
      have : (a * A').mulVec (A.mulVec fun i => a' i (Fin.castLE hk (id l))) =
          a.mulVec fun i => a' i (Fin.castLE hk (id l)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hA, Matrix.mul_one]
      exact congrFun this (Fin.castLE hk l')
    rw [Matrix.of_apply, e, h1, Matrix.one_apply, Matrix.one_apply]
    by_cases hl : l = l'
    · simp [hl]
    · rw [if_neg (fun e => hl (Fin.castLE_injective hk e).symm), if_neg hl]
  rw [hm, Matrix.det_one] at h
  rw [Ideal.eq_top_iff_one, ← h]
  exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)

end Lin

theorem main : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)), q ≫ PSpace.str O _ = f ≫ s → ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z) (α : C.A) (_ : ⊤ ≤ z ⁻¹ᵁ C.B α) (n' : ℕ) (a : Matrix (Fin n') (Fin (C.n α)) R) (a' : Matrix (Fin (C.n α)) (Fin n') R) (y : Sp K ⟶ Z') (hy : ⊤ ≤ (y ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K), a * a' = 1 → a' * a = 1 → y ≫ f = spMap (algebraMap R K) ≫ z → Car Em f q y α hy ξ → (∀ (l : Fin k) (j : Fin n'), k ≤ (j : ℕ) → ∑ i, algebraMap R K (a j i) * ξ l i = 0) → ∃ y₀ : Sp R ⟶ PSpace O (plN N k), y₀ ≫ PSpace.str O _ = z ≫ s ∧ y ≫ q = spMap (algebraMap R K) ≫ y₀ := by
  intro O _ Z Z' s C N k Em f q hq R K _ _ _ z α hz n' a a' y hy ξ h1 h2 hyz hcar h0
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  obtain rfl : n' = C.n α := by simpa using Matrix.square_of_invertible a a' h1 h2
  obtain ⟨hli, hiff, -⟩ := GlobalTheory.T.carrier_independent_span_iff O Z Z' C N k Em f q K y α hy ξ hcar
  have hk : k ≤ C.n α := by simpa using hli.fintype_card_le_finrank
  obtain ⟨l1, l2⟩ := span_cols hk a a' h2 ξ hli h0
  obtain ⟨g, hv, e⟩ := (hiff _).2 ⟨l1, l2⟩
  obtain ⟨A', hA'⟩ := Em.linv α
  set φ := algebraMap R K with hφ
  let g₀ : O →+* R := (Spec.preimage (z ≫ s)).hom
  have hg₀ : spMap g₀ = z ≫ s := Spec.map_preimage (z ≫ s)
  have hAz : A'.map (ev z _ hz) * (Em.A α).map (ev z _ hz) = 1 := by
    rw [← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _)]
  have hu := unimod hk _ _ hAz a a' h1
  refine ⟨pt g₀ _ hu, by rw [GlobalTheory.ProjSpace.pt_str, hg₀], ?_⟩
  have hg : g = φ.comp g₀ := by
    have h5 : spMap (φ.comp g₀) = spMap φ ≫ spMap g₀ := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have h3 : spMap g = spMap (φ.comp g₀) := by
      have h4 := congrArg (· ≫ PSpace.str O _) e
      simp only [Category.assoc, GlobalTheory.ProjSpace.pt_str, hq] at h4
      rw [← h4, ← Category.assoc, hyz, Category.assoc, h5, hg₀]
    exact congrArg (·.hom) (Spec.map_injective h3)
  have hev : ev (y ≫ f) _ hy = φ.comp (ev z _ hz) :=
    (GlobalTheory.FlagMod.ev_congr hyz _ hy (hyz ▸ hy)).trans (GlobalTheory.FlagMod.ev_spMap φ z _ hz _)
  have hp : plk (fun l : Fin k => ((Em.A α).map (ev (y ≫ f) _ hy)).mulVec (φ ∘ fun i => a' i (Fin.castLE hk l))) id =
      φ ∘ plk (fun l : Fin k => ((Em.A α).map (ev z _ hz)).mulVec fun i => a' i (Fin.castLE hk l)) id := by
    rw [GlobalTheory.FlagEmb.map_plk]
    congr 1
    funext l
    funext r
    have hm : (Em.A α).map (φ.comp (ev z _ hz)) = ((Em.A α).map (ev z _ hz)).map φ := by
      rw [Matrix.map_map]
      rfl
    rw [hev, hm]
    exact (RingHom.map_mulVec φ ((Em.A α).map (ev z _ hz)) _ r).symm
  have hpt : ∀ (c : O →+* K) (v w : Fin (plN N k + 1) → K) (hv : Ideal.span (Set.range v) = ⊤)
      (hw : Ideal.span (Set.range w) = ⊤), v = w → pt c v hv = pt c w hw := by
    rintro c v w hv hw rfl
    rfl
  rw [e, GlobalTheory.ProjSpace.spMap_pt]
  subst hg
  exact hpt _ _ _ _ _ hp

end GlobalTheory.GrCl.IntPt
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_matrix_transfer : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)), q ≫ PSpace.str O _ = f ≫ s → ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z) (α : C.A) (_ : ⊤ ≤ z ⁻¹ᵁ C.B α) (n' : ℕ) (a : Matrix (Fin n') (Fin (C.n α)) R) (a' : Matrix (Fin (C.n α)) (Fin n') R) (y : Sp K ⟶ Z') (hy : ⊤ ≤ (y ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K), a * a' = 1 → a' * a = 1 → y ≫ f = spMap (algebraMap R K) ≫ z → Car Em f q y α hy ξ → (∀ (l : Fin k) (j : Fin n'), k ≤ (j : ℕ) → ∑ i, algebraMap R K (a j i) * ξ l i = 0) → ∃ y₀ : Sp R ⟶ PSpace O (plN N k), y₀ ≫ PSpace.str O _ = z ≫ s ∧ y ≫ q = spMap (algebraMap R K) ≫ y₀ := by
  atlas_forward_decl GlobalTheory.GrCl.IntPt.main
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

theorem locMaps_of_grel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → q ≫ PSpace.str _ _ = f ≫ Z.π ≫ (Y Z.i).s → Lifts (Z.π ≫ (Y Z.i).s) f q → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → LocMaps Z₁ A' := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hpW t Z g D hg hL A X' f q ty' A' hA hR hq hLift Z₁ g₀ hg₀ hH K _ w hw
  obtain ⟨τ, mu, u, hT, hπ, hZ₁, hZ⟩ := ((isMap_iff _ _ _).1 hg₀).2 K w hw
  have hAZ : A.FlagAt (w ≫ g₀) (fun σ j => u σ j ≫ mu.φ) := (hA K _ _).2 hZ
  obtain ⟨y, hyπ, hA'y⟩ := Atlas.FlagAt.exists_point hAZ A'
  have htan : ∀ σ i, IsTanAtG (Y Z.i).t ((y ≫ f) ≫ Z.π) (u σ i ≫ mu.φ) := by
    obtain ⟨a, φ, -, hf, -⟩ := id hA'y
    rw [Category.assoc]
    exact fun σ i => (hf.1 σ i).1
  obtain ⟨U, hU⟩ := exists_up htan
  have hR' := (hR K y U).1 (hU ▸ hA'y)
  have hyf : y ≫ f = w ≫ g₀ := Atlas.FlagAt.point_eq (hU ▸ hR'.1) hAZ (by rw [Category.assoc, hyπ])
  refine ⟨y, ⟨τ, mu, u, hT, hyπ.trans hπ, hZ₁, hA'y⟩, ?_⟩
  intro R _ _ _ _ _ _ z hz
  obtain ⟨α, hα₀⟩ := D.C.cover ((z ≫ g₀) (IsLocalRing.closedPoint R))
  have hα : ⊤ ≤ (z ≫ g₀) ⁻¹ᵁ D.C.B α :=
    ((IsLocalRing.closed_point_mem_iff (U := (z ≫ g₀) ⁻¹ᵁ D.C.B α)).1 hα₀).ge
  have hyz : y ≫ f = spMap (algebraMap R K) ≫ z ≫ g₀ := by rw [hyf, ← hz, Category.assoc]
  have hy : ⊤ ≤ (y ≫ f) ⁻¹ᵁ D.C.B α := by
    rw [hyz]
    exact GlobalTheory.FlagMod.le_preimage_map (z ≫ g₀) hα le_top
  obtain ⟨n', a, a', h₁, h₂, hann⟩ := GlobalTheory.T.lattice_step_holds_pullback E H Dw Xo p W Y i₀ hp hpW t Z g D hg hL Z₁ g₀ hg₀ hH R K z α hα
  obtain ⟨y₀, hy₀, hyq⟩ := GlobalTheory.T.carrier_matrix_transfer _ Z.X X' (Z.π ≫ (Y Z.i).s) D.C D.N t.k D.Em f q hq R K (z ≫ g₀) α hα n' a a' y hy _
    h₁ h₂ hyz (hR'.2 α hy) fun l j hj =>
      hann τ mu u hT (hz ▸ hZ₁) (y ≫ f) hyz hy (U t.σ (Fin.castLE t.le l)) (Fin.castLE t.le l) l.2
        (congrFun (congrFun hU t.σ) (Fin.castLE t.le l)) j hj
  exact hLift R K (z ≫ g₀) y₀ y hy₀ hyz hyq

end GlobalTheory.GrCl
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_atlas_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → q ≫ PSpace.str _ _ = f ≫ Z.π ≫ (Y Z.i).s → Lifts (Z.π ≫ (Y Z.i).s) f q → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → LocMaps Z₁ A' := by
  atlas_forward_decl GlobalTheory.GrCl.locMaps_of_grel
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_gap (s : Finset ℕ) {k m : ℕ} (hk : k ≤ m) : ∃ a b, a ≤ k ∧ k ≤ b ∧ (a ∈ s ∨ a = 0) ∧ (b ∈ s ∨ b = m) ∧
    ∀ e ∈ s, e ≤ a ∨ b ≤ e := by
  classical
  have ex : ∃ b, k ≤ b ∧ (b ∈ s ∨ b = m) := ⟨m, hk, .inr rfl⟩
  refine ⟨Nat.findGreatest (· ∈ s) k, Nat.find ex, Nat.findGreatest_le k, (Nat.find_spec ex).1, ?_, (Nat.find_spec ex).2,
    fun e he => ?_⟩
  · by_cases h : Nat.findGreatest (· ∈ s) k = 0
    · exact .inr h
    · exact .inl (Nat.findGreatest_of_ne_zero rfl h)
  · rcases le_total e k with h | h
    · exact .inl (Nat.le_findGreatest h he)
    · exact .inr (Nat.find_min' ex ⟨h, .inl he⟩)

theorem isMap_refl (Z : Mdl Y i₀) : IsMap Z Z (𝟙 _) := by
  refine ⟨MapComp.corr_refl Z, fun k _ w hw => ?_⟩
  obtain ⟨mu, hmu, ht⟩ := exists_isTrans_id (Y := Y) Z.i
  obtain ⟨a, φ, e⟩ := Z.exists_chart w hw
  have h : Z.FlagAt w ((Z.fr a).bc φ) := (atlasOf Z).flagAt_fr (a := a) e
  refine ⟨𝟙 _, mu, _, ht, by simp, h, ?_⟩
  simpa only [hmu, Category.comp_id] using h

open Classical in

theorem exists_step (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (t : Step Y i₀) (ht : ∃ g, IsMap Z t.B g) :
    ∃ Z' : Mdl Y i₀, Z'.i = Z.i ∧ Z'.ty = Function.update Z.ty t.σ (insert t.k (Z.ty t.σ)) ∧ (∃ f, IsMap Z' Z f) ∧
      t.Holds Z' ∧ ∀ Z'' : Mdl Y i₀, (∃ g, IsMap Z'' Z g) → t.Holds Z'' → ∃ h, IsMap Z'' Z' h := by
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  have : CharZero Z.i.c.F := RingHom.charZero Z.i.c.F.val.toRingHom
  obtain ⟨g, hg⟩ := ht
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_lattice_coordinates_step E H Dw Xo p W Y i₀ hp hW t Z g hg
  obtain ⟨A, hA, α, hα⟩ := GlobalTheory.DRFlag.Atlas.exists_refine E H Dw _ _ _ _ _ _ _ _ (atlasOf Z) D.C
  obtain ⟨cv, Dv, hc, hl, hgl⟩ := GlobalTheory.T.atlas_lattice_coordinates E H Dw _ _ _ _ _ _ _ _ A D t.σ α hα
  obtain ⟨a, b, ha, hb, ha', hb', gap⟩ := exists_gap (Z.ty t.σ) t.le
  have geo := geoOf Z
  obtain ⟨X', f, q, κ, cl⟩ := GlobalTheory.T.cells_of_charts_polynomial _ Z.X (Z.π ≫ (Y Z.i).s) geo.proj geo.normal geo.flat A.ch
    (fun j => (A.alg j).comp (Z.i.c.V W).subtype) (GVar (Dw.mult t.σ) a t.k b) (GPm (Dw.mult t.σ) a b) _
    (fun j => gxi a b t.le (cv j)) (fun j => gell a b t.le (Dv j)) A.alg_s
    (fun j => ⟨fun w => (GlobalTheory.T.cell_coordinate_polynomials_surjective _ _ a _ b _ t.le _ _ w ha hb (hl j)).1,
      fun w => (GlobalTheory.T.cell_coordinate_polynomials_surjective _ _ a _ b _ t.le _ _ w ha hb (hl j)).2,
      fun K _ w w' ψ' h => (GlobalTheory.T.cell_coordinates_base_change K _ _ _ a _ b _ t.le _ _ _ _ (ψ'.comp MvPolynomial.C) ψ' w' ha hb (hl j) (hl j)
        fun _ _ => rfl).2 w h,
      GlobalTheory.T.cell_coordinate_linear_relation _ _ a _ b _ t.le _ _ ha hb (hl j)⟩)
    (fun K _ j j' φ w' ψ' e => by
      obtain ⟨⟨w, hw⟩, h⟩ := GlobalTheory.T.cell_coordinates_base_change K _ _ _ a _ b _ t.le _ _ _ _ φ ψ' w' ha hb (hl j) (hl j') fun r hr =>
        hgl K j j' φ _ e r (by rcases hr with rfl | rfl <;> tauto)
      exact ⟨w, h w hw⟩)
  let ty' := Function.update Z.ty t.σ (insert t.k (Z.ty t.σ))
  have t₁ : ty' t.σ = insert t.k (Z.ty t.σ) := Function.update_self _ _ _
  have t₂ : ∀ σ', σ' ≠ t.σ → ty' σ' = Z.ty σ' := fun σ' h => Function.update_of_ne h _ _
  obtain ⟨A', rel⟩ := GlobalTheory.T.cell_atlas_from_lattice E H Dw _ _ _ _ _ _ _ _ A D t.σ α cv Dv a t.k b t.le X' f q κ ty' ha hb ha' hb' gap hα hc hl
    cl t₁ t₂
  have hcar : A'.ch.carrier = f ⁻¹' A.ch.carrier := by
    rw [A'.cover, A.cover, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  have geo' : Geo (Y Z.i) (f ≫ Z.π) :=
    ⟨by rw [Category.assoc]; exact cl.proj, cl.normal, by rw [Category.assoc]; exact cl.flat,
      A'.cover ▸ hcar ▸ cl.dense⟩
  have up' : ∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw (Y Z.i).t K), A'.FlagAt w u →
      ∃ U : TVecs Dw (Y Z.i).t ((w ≫ f) ≫ Z.π), up U = u := fun K _ w u hu => by
    obtain ⟨a, φ, -, hfr, -⟩ := hu
    rw [← Category.assoc] at hfr
    exact exists_up fun σ i => (hfr.1 σ i).1
  have down : ∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw (Y Z.i).t K), A'.FlagAt w u →
      (atlasOf Z).FlagAt (w ≫ f) u := fun K _ w u hu => by
    obtain ⟨U, rfl⟩ := up' K w u hu
    exact (hA K _ _).1 ((rel K w U).1 hu).1
  have red : IsReduced X' := by
    have := fun x => (cl.normal x).1
    exact isReduced_of_isReduced_stalk _
  have pl : Planar D.Em f q := GlobalTheory.T.planar_of_dense_carriers _ _ _ _ _ _ D.Em f q A'.ch.carrier red (hcar ▸ cl.dense) fun K _ w hw β h => by
    obtain ⟨j, φ, e⟩ := A'.ch.exists_fac w (hw ⟨_, rfl⟩)
    have hu := A'.flagAt_fr e
    obtain ⟨U, hU⟩ := up' K w _ hu
    exact ⟨_, ((rel K w U).1 (hU ▸ hu)).2 β h⟩
  obtain ⟨Z', e, hi, hty, m₁, m₂, -⟩ := GlobalTheory.T.exists_model_of_atlas E H Dw Xo p W Y i₀ Z.i X' _ ty' A' Z.dvd Z.le geo'
  have sub : ∀ σ, Z.ty σ ⊆ ty' σ := fun σ => by
    by_cases h : σ = t.σ
    · rw [h, t₁]; exact Finset.subset_insert _ _
    · rw [t₂ σ h]
  have hf : IsMap Z' Z (e.hom ≫ f) :=
    ⟨⟨hi ▸ ⟨dvd_rfl, le_rfl, dvd_rfl⟩, hi ▸ le_rfl, hty ▸ sub⟩, m₂ _ _ _ (atlasOf Z) f rfl down⟩
  have he : MapsTo Z' A' e.hom := by
    simpa only [Category.comp_id] using m₂ _ _ _ A' (𝟙 _) (Category.id_comp _) fun K _ w u h => by
      simpa only [Category.comp_id] using h
  refine ⟨Z', hi, hty, ⟨_, hf⟩, GlobalTheory.T.lattice_step_atlas_pullback E H Dw Xo p W Y i₀ hp hW t Z g D hg hD A X' f q ty' A' hA rel pl Z' _ he hf
    (by rw [hty, t₁]; exact Finset.mem_insert_self _ _), fun Z'' ⟨g₀, hg₀⟩ hH => ?_⟩
  have sub' : ∀ σ, ty' σ ⊆ Z''.ty σ := fun σ => by
    by_cases h : σ = t.σ
    · rw [h, t₁]; exact Finset.insert_subset hH.1 (hg₀.1.2.2 _)
    · rw [t₂ σ h]; exact hg₀.1.2.2 _
  obtain ⟨h, hh⟩ := GlobalTheory.T.atlas_model_comparison E H Dw Xo p W Y i₀ Z.i _ _ ty' A' Z'' hp hW geo' hg₀.1.2.1 sub'
    (GlobalTheory.T.lattice_step_atlas_refinement E H Dw Xo p W Y i₀ hp hW t Z g D hg hD A X' f q ty' A' hA rel cl.ovr cl.lift Z'' g₀ hg₀ hH)
  exact ⟨h ≫ e.inv, ⟨hi ▸ hg₀.1.1, hi ▸ hg₀.1.2.1, hty ▸ sub'⟩, m₁ Z'' h hh⟩

theorem exists_isFlagCl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀) (s : Finset (Step Y i₀)), (∀ t ∈ s, ∃ f, IsMap Z t.B f) → ∃ Z', IsFlagCl Z s Z' := by
  classical
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨Z, isFlagCl_empty ⟨_, isMap_refl Z⟩⟩
  | insert t s _ ih =>
    intro h
    obtain ⟨Z₁, hi, hty, ⟨f, hf⟩, hs, mn⟩ := ih fun t' ht' => h t' (Finset.mem_insert_of_mem ht')
    obtain ⟨g, hg⟩ := h t (Finset.mem_insert_self _ _)
    obtain ⟨Z₂, hi', hty', ⟨f', hf'⟩, ht, mn'⟩ := exists_step hp hW Z₁ t ⟨_, MapComp.isMap_comp hf hg⟩
    refine ⟨Z₂, hi'.trans hi, fun σ => ?_, ⟨_, MapComp.isMap_comp hf' hf⟩, fun t' ht' => ?_, fun Z'' hg' hH => ?_⟩
    · rw [hty']
      ext r
      by_cases e : σ = t.σ
      · subst e
        simp only [Function.update_self, hty, Finset.mem_insert, Finset.mem_union, mem_stepTy, exists_eq_or_imp, true_and]
        tauto
      · simp only [Function.update_of_ne e, hty, Finset.mem_insert, Finset.mem_union, mem_stepTy, exists_eq_or_imp,
          Ne.symm e, false_and, false_or]
    · rcases Finset.mem_insert.1 ht' with rfl | ht'
      · exact ht
      · exact GlobalTheory.T.step_holds_of_map E H Dw Xo p W hp hW Y i₀ t' Z₁ Z₂ ⟨_, hf'⟩ (hs t' ht')
    · exact mn' Z'' (mn Z'' hg' fun t' ht' => hH t' (Finset.mem_insert_of_mem ht')) (hH t (Finset.mem_insert_self _ _))

end GlobalTheory.GrCl
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀) (s : Finset (Step Y i₀)), (∀ t ∈ s, ∃ f, IsMap Z t.B f) → ∃ Z', IsFlagCl Z s Z' := by
  atlas_forward_decl GlobalTheory.GrCl.exists_isFlagCl
end
