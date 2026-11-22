module

public import Mathlib
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

@[expose] public section

noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

@[reducible] def cplGSD {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (Y : Cpl S) : GSD K where
  G := S.G
  D := Y.Pts
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ
  Nab d := S.Nab d.1.1
  Del d := S.Del d.1.1

section Jet

open MvPolynomial Formalism.L2.Ker

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in
theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (c : K) :
    jetLin J (monomial μ c) = monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h : (monomial μ c : MvPolynomial _ K) = c • basisMonomials _ K μ := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

theorem jetMap_sum {α : Type} (s : Finset α) (r : α → K) (J : α → (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    jetMap (∑ x ∈ s, r x • J x) n = ∑ x ∈ s, r x • jetMap (J x) n := by
  have h : jetLin (∑ x ∈ s, r x • J x) = ∑ x ∈ s, r x • jetLin (J x) := by
    refine (basisMonomials _ K).ext fun μ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coe_basisMonomials, LinearMap.sum_apply, LinearMap.smul_apply, jetLin_monomial, one_mul, Finset.sum_apply, Pi.smul_apply,
      map_sum, smul_monomial]
  refine LinearMap.ext fun P => ?_
  simp only [jetMap, h, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]

omit [Fintype ι] in
theorem map_subD {L : Type} [Field L] (s : K →+* L) (P : Formalism.L2.DIV.Pol K ι a) :
    MvPolynomial.map s (subD K ι a b P) = subD L ι a b (MvPolynomial.map s P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [subD]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [subD, aeval_X]
    split_ifs <;> simp

theorem map_jetMap {L : Type} [Field L] (s : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → L) (r : L) (n : ι → ℕ)
    (P : Formalism.L2.DIV.Pol K ι a)
    (h : ∀ μ ∈ (subD K ι a b (P * ∏ τ, frDet K a τ ^ n τ)).support,
      s (J (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) = r * J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) :
    MvPolynomial.map s (jetMap J n P) = r • jetMap J' 0 (MvPolynomial.map s (P * ∏ τ, frDet K a τ ^ n τ)) := by
  have e0 : ∀ Q : Formalism.L2.DIV.Pol L ι a, jetMap J' 0 Q = jetLin J' (subD L ι a b Q) := fun Q => by simp [jetMap]
  have e1 : jetMap J n P = jetLin J (subD K ι a b (P * ∏ τ, frDet K a τ ^ n τ)) := rfl
  rw [e0, e1, ← map_subD]
  generalize subD K ι a b (P * ∏ τ, frDet K a τ ^ n τ) = Q at h
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [jetLin_monomial, map_monomial, map_monomial, jetLin_monomial, smul_monomial, map_mul, h μ hμ, smul_eq_mul, mul_left_comm]

end Jet

namespace ChSrc

variable {X : Fields} {R : Ranks} (A : ChSrc X R) (σ : X.K →+* ℂ)

abbrev Fr (X : Fields) (σ : X.K →+* ℂ) (n : ℕ) : Type := Frames (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt σ X.emb))

theorem half (R : Ranks) (j : ℕ) : ∃ z : ℤ, (z : ℚ) = (R.N j : ℚ) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  refine ⟨(a : ℤ) + j * (b + 1), ?_⟩
  simp only [Ranks.N, ha, hb]
  push_cast
  ring

def zOf (x : ℚ) : ℤ := ⌊x⌋

theorem zOf_spec (R : Ranks) (e : ℚ) (he : ∃ z : ℤ, e = z) (j : ℕ) : ((zOf (e - (R.N j : ℚ) / 2) : ℤ) : ℚ) = e - (R.N j : ℚ) / 2 := by
  obtain ⟨z, rfl⟩ := he
  obtain ⟨y, hy⟩ := half R j
  rw [← hy, ← Int.cast_sub, zOf, Int.floor_intCast]

def sS (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : ℤ :=
  if h : i < R.m then zOf (sExp' R ((hc τ).e ⟨i, h⟩) (i + 1)) else 0

def sD (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : ℤ :=
  if h : i < R.m then zOf (sExp R ((hc τ).e ⟨i, h⟩) (i + 1)) else 0

def trueWt (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : DomWeight (R.N i) :=
  shiftW (Examples₂.lamOf (hc τ) i) (-((i : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ)))

theorem trueWt_eq {Word : Type} (W : Wts X Word R) (u : Word) (i : ℕ) : trueWt (W.hc u) i = W.lamTrue u i := rfl

theorem trueWt_old (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) (a : Fin (R.N (i + 1))) (h : a.1 < R.N i) :
    (trueWt hc (i + 1) τ).w a = (trueWt hc i τ).w ⟨a.1, h⟩ + sS hc i τ - sD hc i τ := by
  have h0 := Wts.lamTrue_old (⟨fun τ => RowPar.of (hc τ), fun _ => hc, ∅⟩ : Wts X Unit R) () hi τ a h
  have h1 : ((sS hc i τ : ℤ) : ℚ) = sExp' R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
    rw [sS, dif_pos hi]; exact zOf_spec R _ ((hc τ).e_int _) _
  have h2 : ((sD hc i τ : ℤ) : ℚ) = sExp R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
    rw [sD, dif_pos hi]; exact zOf_spec R _ ((hc τ).e_int _) _
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [h1, h2]
  exact h0

theorem trueWt_new (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) (a : Fin (R.N (i + 1))) (h : ¬ a.1 < R.N i) :
    (trueWt hc (i + 1) τ).w a = -sD hc i τ := by
  have h0 := Wts.lamTrue_new (⟨fun τ => RowPar.of (hc τ), fun _ => hc, ∅⟩ : Wts X Unit R) () hi τ a h
  have h2 : ((sD hc i τ : ℤ) : ℚ) = sExp R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
    rw [sD, dif_pos hi]; exact zOf_spec R _ ((hc τ).e_int _) _
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [h2]
  exact h0

theorem trueWt_add_sS_nonneg (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) (a : Fin (R.N i)) :
    0 ≤ (trueWt hc i τ).w a + sS hc i τ := by
  have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
  have h1 := trueWt_old hc hi τ ⟨a.1, a.2.trans hN⟩ a.2
  have h2 := trueWt_new hc hi τ ⟨R.N i, hN⟩ (lt_irrefl _)
  have h3 := (trueWt hc (i + 1) τ).anti (show (⟨a.1, a.2.trans hN⟩ : Fin (R.N (i + 1))) ≤ ⟨R.N i, hN⟩ from a.2.le)
  rw [h1, h2] at h3
  simp only [Fin.eta] at h3
  omega

@[reducible] def exampleGSD (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) : GSD X.K where
  G := ℤˣ
  D := Unit
  V := VV X.K lam
  ιV := VVIdx lam
  decιV := Classical.decEq _
  bV := bVV X.K lam
  pair := pairVr X.emb lam 1
  ρ := 1
  Nab _ := nabAtr X.emb lam (stdLat X.E n)
  Del _ := delAtr X.emb lam (stdLat X.E n)

def polFn (X : Fields) (σ : X.K →+* ℂ) (n : ℕ) : Formalism.L2.DIV.Pol ℂ X.Tau n →ₗ[ℂ] (Fr X σ n → ℂ) := fnOf _ 0 1

theorem polFn_apply {n : ℕ} (Q : Formalism.L2.DIV.Pol ℂ X.Tau n) (y : Fr X σ n) :
    polFn X σ n Q y = MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) Q := by
  simp [polFn, fnOf]

def fnPol (X : Fields) (σ : X.K →+* ℂ) (n : ℕ) : (Fr X σ n → ℂ) →ₗ[ℂ] Formalism.L2.DIV.Pol ℂ X.Tau n := polOf _ 0 (stdFrC _)

theorem fnPol_polFn {n : ℕ} (Q : Formalism.L2.DIV.Pol ℂ X.Tau n) : fnPol X σ n (polFn X σ n Q) = Q := by
  have h := polOf_fnOf (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt σ X.emb)) 0 (stdFrC _) Q
  have e : (fun τ => ((stdFrC (n := n) (embAt σ X.emb)).1 τ)⁻¹) = 1 := funext fun τ => by simp [stdFrC]
  rw [e] at h
  exact h

def nuEnd (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : ℕ := ((trueWt hc i τ).detShift + sS hc i τ).toNat

theorem nuEnd_cast (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    (nuEnd hc i τ : ℤ) = (trueWt hc i τ).detShift + sS hc i τ := by
  have := trueWt_add_sS_nonneg hc hi τ ⟨R.N i - 1, by have := R.N_pos i; omega⟩
  rw [nuEnd, Int.toNat_of_nonneg]
  rwa [DomWeight.detShift, dif_pos (R.N_pos i)]

theorem nuEnd_eq {Pr : Primes X} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) :
    nuEnd (W.hc u) i = Formalism.L2.Ker.nuLast W u i := by
  funext τ
  have h1 : ((sS (W.hc u) i τ : ℤ) : ℚ) = sExp' R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := (by
    rw [sS, dif_pos hi]; exact zOf_spec R _ ((W.hc u τ).e_int _) _)
  have h0 := W.nuW_eq_true u hi τ ⟨R.N i - 1, by have := R.N_pos i; omega⟩
  rw [← h1] at h0
  have h2 : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w ⟨R.N i - 1, Nat.sub_lt (R.N_pos i) one_pos⟩ := dif_pos (R.N_pos i)
  rw [nuEnd, Formalism.L2.Ker.nuLast, h2, DomWeight.detShift, dif_pos (R.N_pos i), trueWt_eq]
  congr 1
  exact_mod_cast h0.symm

theorem trueWt_detShift_succ (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    (trueWt hc (i + 1) τ).detShift = -sD hc i τ := by
  have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
  rw [DomWeight.detShift, dif_pos (R.N_pos _)]
  exact trueWt_new hc hi τ _ (by simp only; omega)

section Laws

variable {A} {hc : X.Tau → HCParam R} (h : A.Tied hc) {cD : X.Tau → ℂ} {Th : A.ThFam} (hJ : A.JetTie σ hc (A.jetTh cD Th))
include h hJ

end Laws

end ChSrc

end GlobalTheory.GO
