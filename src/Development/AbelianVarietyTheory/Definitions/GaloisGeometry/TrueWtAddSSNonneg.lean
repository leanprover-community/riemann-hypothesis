module

public import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

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

  simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [jetLin_monomial, map_monomial, map_monomial, jetLin_monomial, smul_monomial, map_mul, h μ hμ, smul_eq_mul, mul_left_comm]

def derPol (cD : ι → K) (Q : Formalism.L2.DIV.Pol K ι a) (y' : ι → Matrix (Fin b) (Fin b) K) : MvPolynomial (DVar ι a b) K :=
  aeval (fun k : ι × Fin a × Fin a => ∑ β : Fin b,
    C (cD k.1 * (if h : (k.2.2 : ℕ) < b then y' k.1 β ⟨k.2.2, h⟩ else 0)) * X ((k.1, β, k.2.1) : DVar ι a b)) Q

end Jet

structure ChSrc (X : Fields) (R : Ranks) where

  F : ℕ → GFam X.K

  ok : ∀ i, (F i).Ok

  lam : ∀ i, X.Tau → DomWeight (R.N i)

  eV : ∀ i, (F i).V ≃ₗ[X.K] Formalism.L2.DIV.VV X.K (lam i)

  kk : KerFam F

  rho : ∀ i, (F i).Cl → ℂ

  rho' : ∀ i, (F (i + 1)).Cl → ℂ
  rho_norm : ∀ i, i < R.m → ∀ c, ‖rho i c‖ = 1
  rho'_norm : ∀ i, i < R.m → ∀ c, ‖rho' i c‖ = 1

  DG : ℕ
  DG_pos : 0 < DG
  dvd : ∀ i, i ≤ R.m → ∀ c : (F i).Cl,
    Nat.card (MulAction.stabilizer ((F i).G c.1) (((F i).mem c.1).outSec.rep c.2)) ∣ DG

namespace ChSrc

variable {X : Fields} {R : Ranks} (A : ChSrc X R) (σ : X.K →+* ℂ)

abbrev Fr (X : Fields) (σ : X.K →+* ℂ) (n : ℕ) : Type := Frames (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt σ X.emb))

def ev (i : ℕ) (x : (A.F i).V) : Fr X σ (R.N i) → ℂ := evV X.emb 1 (A.lam i) σ (A.eV i x)

def ker (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) : (A.F i).V →ₗ[X.K] (A.F (i + 1)).V :=
  GFam.Mat.atReps (A.kk i) (fun b => ((A.F i).mem b).outSec) (fun b => ((A.F (i + 1)).mem b).outSec) c c'

def kerC (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) : (Fr X σ (R.N i) → ℂ) →ₗ[ℂ] (Fr X σ (R.N (i + 1)) → ℂ) :=
  Classical.epsilon fun U : (Fr X σ (R.N i) → ℂ) →ₗ[ℂ] (Fr X σ (R.N (i + 1)) → ℂ) =>
    ∀ x, U (A.ev σ i x) = A.ev σ (i + 1) (A.ker i c c' x)

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

def chain (hc : X.Tau → HCParam R) : ColumnChain R X.Tau hc where
  cls i := (A.F i).Cl
  clsFin i := (A.ok i).fintypeCl
  stab i c := MulAction.stabilizer ((A.F i).G c.1) (((A.F i).mem c.1).outSec.rep c.2)
  stabGrp _ _ := inferInstance
  stabFin i c := (A.ok i c.1).fin_stab _
  DGam := A.DG
  DGam_pos := A.DG_pos
  dvd_DGam := A.dvd
  Y i := Fr X σ (R.N i)
  de _ y τ := deFr y τ
  de_ne _ y τ := (isUnit_det_fr y τ).ne_zero
  rhoDet := A.rho
  rhoDet' := A.rho'
  rho_norm := A.rho_norm
  rho'_norm := A.rho'_norm
  unf i c c' := (A.rho i c * A.rho' i c')⁻¹ •
    ((mulFun fun y => ∏ τ, deFr y τ ^ sD hc i τ).comp ((A.kerC σ i c c').comp (mulFun fun y => (∏ τ, deFr y τ ^ sS hc i τ)⁻¹)))
  sSharp := sS hc
  sSharp_eq i h τ := by
    rw [sS, dite_eq_left h]; exact zOf_spec R _ ((hc τ).e_int _) _
  sDiv := sD hc
  sDiv_eq i h τ := by
    rw [sD, dite_eq_left h]; exact zOf_spec R _ ((hc τ).e_int _) _

def emb (i : ℕ) (φ : (A.F i).Forms) : (A.F i).Cl → Fr X σ (R.N i) → ℂ :=
  fun c => A.ev σ i ((φ c.1).1 (((A.F i).mem c.1).outSec.rep c.2))

def evS (i : ℕ) : (A.F i).V →ₛₗ[σ] (Fr X σ (R.N i) → ℂ) :=
  (evV X.emb 1 (A.lam i) σ).comp (A.eV i).toLinearMap

def trueWt (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : DomWeight (R.N i) :=
  shiftW (Examples₂.lamOf (hc τ) i) (-((i : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ)))

theorem trueWt_eq {Word : Type} (W : Wts X Word R) (u : Word) (i : ℕ) : trueWt (W.hc u) i = W.lamTrue u i := rfl

theorem trueWt_old (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) (a : Fin (R.N (i + 1))) (h : a.1 < R.N i) :
    (trueWt hc (i + 1) τ).w a = (trueWt hc i τ).w ⟨a.1, h⟩ + sS hc i τ - sD hc i τ := by
  have h0 := Wts.lamTrue_old (⟨fun τ => RowPar.of (hc τ), fun _ => hc, ∅⟩ : Wts X Unit R) () hi τ a h
  have h1 : ((sS hc i τ : ℤ) : ℚ) = sExp' R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
    rw [sS, dite_eq_left hi]; exact zOf_spec R _ ((hc τ).e_int _) _
  have h2 : ((sD hc i τ : ℤ) : ℚ) = sExp R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
    rw [sD, dite_eq_left hi]; exact zOf_spec R _ ((hc τ).e_int _) _
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [h1, h2]
  exact h0

theorem trueWt_new (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) (a : Fin (R.N (i + 1))) (h : ¬ a.1 < R.N i) :
    (trueWt hc (i + 1) τ).w a = -sD hc i τ := by
  have h0 := Wts.lamTrue_new (⟨fun τ => RowPar.of (hc τ), fun _ => hc, ∅⟩ : Wts X Unit R) () hi τ a h
  have h2 : ((sD hc i τ : ℤ) : ℚ) = sExp R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
    rw [sD, dite_eq_left hi]; exact zOf_spec R _ ((hc τ).e_int _) _
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

structure Tied (hc : X.Tau → HCParam R) : Prop where

  lam_eq : ∀ i, i ≤ R.m → A.lam i = trueWt hc i

  act : ∀ i, i ≤ R.m → ∀ b : (A.F i).β, ∃ (u : (A.F i).G b →* UF X.E (R.N i)) (χ : (A.F i).G b →* X.Kˣ), ∀ g x,
    A.eV i ((A.F i).ρ b g x) = ((χ g : X.Kˣ) : X.K) • rhoVr X.emb (A.lam i) (ufGL X.E (R.N i) (u g)) (A.eV i x)

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

theorem exampleDatum_isAdmissible (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) : (exampleGSD X lam).Ok := by
  exact {
    fin_orb := Quotient.finite _
    fin_stab := fun _ => inferInstance
    nab_smul := fun _ _ => (Submodule.map_id _).symm
    del_smul := fun _ _ => (Submodule.map_id _).symm
    inv := fun _ _ _ => rfl }

theorem card_stabilizer_units_int (d : Unit) : Nat.card (MulAction.stabilizer ℤˣ d) = 2 := by
  have : MulAction.stabilizer ℤˣ d = ⊤ := by
    ext g; simp only [Subgroup.mem_top, iff_true]; rfl
  rw [this, Subgroup.card_top, Nat.card_eq_fintype_card]
  simp

theorem exists_linearForm_apply_eq_one (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) : ∃ f : VV X.K lam →ₗ[X.K] X.K, f (extV X.K lam) = 1 := by
  obtain ⟨f, hf⟩ := not_forall.mp (mt (Module.forall_dual_apply_eq_zero_iff X.K (extV X.K lam)).mp (extV_ne_zero lam))
  exact ⟨(f (extV X.K lam))⁻¹ • f, by simp [inv_mul_cancel₀ hf]⟩

def toyExample (hc : X.Tau → HCParam R) : ChSrc X R where
  F i := (exampleGSD X (trueWt hc i)).toFam
  ok i _ := exampleDatum_isAdmissible X (trueWt hc i)
  lam := trueWt hc
  eV _ := LinearEquiv.refl _ _
  kk i _ _ :=
    { k := fun _ _ => (exists_linearForm_apply_eq_one X (trueWt hc i)).choose.smulRight (extV X.K (trueWt hc (i + 1)))
      equiv := fun _ _ _ _ => rfl }
  rho _ _ := Complex.I
  rho' _ _ := -1
  rho_norm _ _ _ := by simp
  rho'_norm _ _ _ := by simp
  DG := 2
  DG_pos := two_pos
  dvd _ _ _ := (card_stabilizer_units_int _).dvd

def exampleExt (hc : X.Tau → HCParam R) (i : ℕ) : ((toyExample hc).F i).Forms := fun _ => ⟨fun _ => extV X.K (trueWt hc i), fun _ _ => rfl⟩

abbrev UnfFam : Type :=
  ∀ i, (A.F i).Cl → (A.F (i + 1)).Cl → ((Fr X σ (R.N i) → ℂ) →ₗ[ℂ] (Fr X σ (R.N (i + 1)) → ℂ))

def chainWith (hc : X.Tau → HCParam R) (U : A.UnfFam σ) : ColumnChain R X.Tau hc := { A.chain σ hc with unf := U }

def Unfolds (hc : X.Tau → HCParam R) (U : A.UnfFam σ) : Prop :=
  ∀ i, i < R.m → ∀ c c' x (y : Fr X σ (R.N (i + 1))), U i c c' ((A.chain σ hc).sharp i (A.ev σ i x)) y =
    (A.rho i c * A.rho' i c')⁻¹ * ((∏ τ, deFr y τ ^ sD hc i τ) * A.ev σ (i + 1) (A.ker i c c' x) y)

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

abbrev JetFam : Type :=
  ∀ i, (A.F i).Cl → (A.F (i + 1)).Cl → (Formalism.L2.DIV.Pol ℂ X.Tau (R.N i) →ₗ[ℂ] Formalism.L2.DIV.Pol ℂ X.Tau (R.N (i + 1)))

def unfJet (J : A.JetFam) : A.UnfFam σ := fun i c c' => polFn X σ (R.N (i + 1)) ∘ₗ J i c c' ∘ₗ fnPol X σ (R.N i)

def chainJet (hc : X.Tau → HCParam R) (J : A.JetFam) : ColumnChain R X.Tau hc := A.chainWith σ hc (A.unfJet σ J)

def nuEnd (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : ℕ := ((trueWt hc i τ).detShift + sS hc i τ).toNat

theorem nuEnd_cast (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    (nuEnd hc i τ : ℤ) = (trueWt hc i τ).detShift + sS hc i τ := by
  have := trueWt_add_sS_nonneg hc hi τ ⟨R.N i - 1, by have := R.N_pos i; omega⟩
  rw [nuEnd, Int.toNat_of_nonneg]
  rwa [DomWeight.detShift, dite_eq_left (R.N_pos i)]

theorem nuEnd_eq {Pr : Primes X} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) :
    nuEnd (W.hc u) i = Formalism.L2.Ker.nuLast W u i := by
  funext τ
  have h1 : ((sS (W.hc u) i τ : ℤ) : ℚ) = sExp' R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := (by
    rw [sS, dite_eq_left hi]; exact zOf_spec R _ ((W.hc u τ).e_int _) _)
  have h0 := W.nuW_eq_true u hi τ ⟨R.N i - 1, by have := R.N_pos i; omega⟩
  rw [← h1] at h0
  have h2 : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w ⟨R.N i - 1, Nat.sub_lt (R.N_pos i) one_pos⟩ := dite_eq_left (R.N_pos i)
  rw [nuEnd, Formalism.L2.Ker.nuLast, h2, DomWeight.detShift, dite_eq_left (R.N_pos i), trueWt_eq]
  congr 1
  exact_mod_cast h0.symm

theorem trueWt_detShift_succ (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    (trueWt hc (i + 1) τ).detShift = -sD hc i τ := by
  have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
  rw [DomWeight.detShift, dite_eq_left (R.N_pos _)]
  exact trueWt_new hc hi τ _ (by simp only; omega)

def sharpPol (hc : X.Tau → HCParam R) (i : ℕ) (x : (A.F i).V) : Formalism.L2.DIV.Pol ℂ X.Tau (R.N i) :=
  MvPolynomial.map σ ((A.eV i x).1 * ∏ τ, Formalism.L2.Ker.frDet X.K (R.N i) τ ^ nuEnd hc i τ)

def JetTie (hc : X.Tau → HCParam R) (J : A.JetFam) : Prop :=
  ∀ i, i < R.m → ∀ c c' x, MvPolynomial.map σ (A.eV (i + 1) (A.ker i c c' x)).1 =
    (A.rho i c * A.rho' i c') • J i c c' (A.sharpPol σ hc i x)

abbrev ThFam : Type := ∀ i, (A.F i).Cl → (A.F (i + 1)).Cl → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ

def jetTh (cD : X.Tau → ℂ) (Th : A.ThFam) : A.JetFam := fun i c c' => Formalism.L2.Ker.jetMap (Formalism.L2.Ker.jetC cD (Th i c c')) 0

def chainTh (hc : X.Tau → HCParam R) (cD : X.Tau → ℂ) (Th : A.ThFam) : ColumnChain R X.Tau hc := A.chainJet σ hc (A.jetTh cD Th)

end ChSrc

end GlobalTheory.GO
