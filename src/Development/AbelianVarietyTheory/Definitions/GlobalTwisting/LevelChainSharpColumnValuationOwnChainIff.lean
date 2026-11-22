module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.LocalRingCardinality.DataKerP
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

structure Ch (D : D7) (u : D.what₂.Word) where
  C : ColumnChain D.R D.what₂.Tau (D.hcW u)
  A : ColumnsAtT D.R C
  P : PeriodMap D.R C
  fm : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P

abbrev own (D : D7) (u : D.what₂.Word) : Ch D u := ⟨(D.mem u).C, (D.mem u).A, (D.mem u).P, D.fm u⟩

abbrev tw {D : D7} (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Ch D u :=
  ⟨D.chTw u μ, Tw.A u μ, D.PTw u μ, Tw.fm u μ⟩

variable {D : D7} {u : D.what₂.Word} (X : Ch D u)

def TauWeight (τ : D.what₂.Tau) : ℕ :=
  (Finset.range (D.R.m + 1)).sup fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs

abbrev Fn (i : ℕ) : Type := X.C.cls i → X.C.Y i → ℂ

abbrev Vl (i : ℕ) : Type := (X.fm.lat i).V

instance lvModFin (i : ℕ) (v : X.A.vT) (c : X.C.cls i) :
    Module.Finite (X.A.Fv v) (X.fm.lv i v c) :=
  Module.finite_of_finrank_pos (by rw [X.fm.lv_rank]; exact D.R.N_pos i)

instance lvFintype (i : ℕ) (v : X.A.vT) (c : X.C.cls i) : Fintype (X.fm.lv i v c) :=
  haveI : Finite (X.fm.lv i v c) := Module.finite_of_finite (X.A.Fv v)
  Fintype.ofFinite _

def Uop (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => ∑ x ∈ Finset.univ.filter (fun x : X.fm.lv i v c => X.fm.fv i v c x = 1),
    (X.fm.upT i v c x).toLinearMap ∘ₗ LinearMap.proj (X.fm.up i v c x)

def VVT (w : D.what₂.places.Pl) : Finset X.A.vT :=
  if X.fm.seenP w then Finset.univ.filter (fun v => X.fm.tauOf w v ∈ topsOf D.host D.eTau) else ∅

def Uprod (i : ℕ) (w : D.what₂.places.Pl) : Fn X i →ₗ[ℂ] Fn X i :=
  (VVT X w).toList.foldr (fun v g => (Uop X i v).comp g) LinearMap.id

def imgL {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn X i →ₗ[ℂ] Fn X j)
    (A : Submodule (Ow D w) (Vl X i)) : Submodule (Ow D w) (Vl X j) where
  carrier := {y | ∃ x ∈ A, X.fm.emb j y = f (X.fm.emb i x)}
  add_mem' := by
    rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
    exact ⟨x + y, A.add_mem hx hy, by rw [map_add (f := _), map_add (f := _), map_add (f := _), h1, h2]⟩
  zero_mem' := ⟨0, A.zero_mem, by simp⟩
  smul_mem' := by
    rintro r a ⟨x, hx, h1⟩
    refine ⟨r • x, A.smul_mem r hx, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1,
      LinearMap.map_smul]

def Sram (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl X 0) :=
  X.fm.S 0 w ⊓ X.fm.ramSub.restrictScalars (Ow D w)

def expT (w : D.what₂.places.Pl) : ℤ :=
  (D.R.m : ℤ) * ∑ v ∈ VVT X w, X.fm.bTop (X.fm.tauOf w v)

def Nlam (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl X 0) :=
  imgL X w (((X.A.T : ℂ) ^ expT X w) • (Uprod X 0 w) ^ D.R.m) (Sram X w)

def OverT (w : D.what₂.places.Pl) : Prop := D.what₂.places.resChar w = X.A.T

def tpow (n : ℕ) : ℂ := (X.A.T : ℂ) ^ n

instance lkModFin (i : ℕ) (v : X.A.vT) (c : X.C.cls i) : Module.Finite (X.A.Fv v) (X.fm.lk i v c) :=
  Module.finite_of_finrank_pos (by rw [X.fm.lk_rank]; exact D.R.N_pos i)

instance lkDualFintype (i : ℕ) (v : X.A.vT) (c : X.C.cls i) :
    Fintype (Module.Dual (X.A.Fv v) (X.fm.lk i v c)) :=
  haveI : Finite (Module.Dual (X.A.Fv v) (X.fm.lk i v c)) := Module.finite_of_finite (X.A.Fv v)
  Fintype.ofFinite _

def dia (i : ℕ) (v : X.A.vT) (a : (X.A.Fv v)ˣ) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => (X.fm.dilT i v a c).toLinearMap ∘ₗ LinearMap.proj (X.fm.dil i v a c)

def Nm (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i := ∑ a : (X.A.Fv v)ˣ, dia X i v a

theorem dia_zero (v : X.A.vT) (a : (X.A.Fv v)ˣ) : dia X 0 v a = X.A.rhoT v a := by
  apply LinearMap.ext; intro φ; funext c
  rw [X.fm.rhoT_dil v a φ c]; rfl

theorem Nm_zero (v : X.A.vT) : Nm X 0 v = X.A.Nm v := by
  unfold Nm ColumnsAtT.Nm; exact Finset.sum_congr rfl (fun a _ => dia_zero X v a)

def MramI (i : ℕ) : Submodule ℂ (Fn X i) := X.fm.Fi i ⊓ ⨅ v, LinearMap.ker (Nm X i v)

theorem MramI_zero : MramI X 0 = X.A.Mram := by
  unfold MramI ColumnsAtT.Mram; rw [X.fm.Fi_zero]; simp only [Nm_zero]

def KT (i : ℕ) : Fn X i →ₗ[ℂ] Fn X (i + 1) := X.C.Klin i

def colT : Fn X 0 → Fn X D.R.m := X.C.col

abbrev Wt (τ : D.what₂.Tau) : ℕ := TauWeight X τ

def Into {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn X i → Fn X j)
    (A : Submodule (Ow D w) (Vl X i)) (B : Submodule (Ow D w) (Vl X j)) : Prop :=
  ∀ x ∈ A, ∃ y ∈ B, X.fm.emb j y = f (X.fm.emb i x)

def LevelChainUOperatorCommutation : Prop :=
  ∀ i, i < D.R.m → ∀ v : X.A.vT, ∀ φ ∈ X.fm.Fi i,
    Uop X (i + 1) v (KT X i φ) =
      ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) • KT X i (Uop X i v φ)

def ETpi : ℝ :=
  2 * ∑ τ, (Wt X τ : ℝ) + (D.R.f : ℝ) * D.R.N D.R.m +
    ((tops D).card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4

def ET (w : D.what₂.places.Pl) : ℝ := if X.fm.seenP w then ETpi X else 0

def Conclusion5Sharp : Prop :=
  ∀ w, OverT X w → ∀ (c : D.what₂.LL) (n : ℤ), D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) →
    (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * ET X w) ≤ (n : ℝ) →
    Into X w (fun φ => D.what₂.embLL c • colT X φ) (Nlam X w) (X.fm.S D.R.m w)

def TupleChainSharpColumnValuation (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ w, Formalism.MainNotions.product_first_zeroth_parts.OverT D u w → ∀ (c : D.what₂.LL) (n : ℤ), D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) →
    (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * EatT D u w) ≤ (n : ℝ) →
    ∀ x ∈ LT.Nlam D u w, ∃ y ∈ (Tw.fm u μ).S D.R.m w,
      (Tw.fm u μ).emb D.R.m y = D.what₂.embLL c • (D.chTw u μ).col (D.e0Tw u μ ((D.fm u).emb 0 x))

section Indep

variable (Y : Ch D u)

end Indep

theorem emb_mem_Fi (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

def Ulist (l : List X.A.vT) : Fn X 0 →ₗ[ℂ] Fn X 0 := l.foldr (fun v g => (Uop X 0 v).comp g) LinearMap.id

variable {X}

namespace SharedBy

variable {Y : Ch D u} {e : Fn X 0 ≃ₗ[ℂ] Fn Y 0} {eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0}
  {ev : X.A.vT ≃ Y.A.vT} {eF : ∀ v, X.A.Fv v ≃+* Y.A.Fv (ev v)} (h : SharedBy X Y e eL ev eF)
include h

end SharedBy

section Reformulated

variable (D u)

theorem levelChainSharpColumnValuation_ownChain_iff : Conclusion5Sharp (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u := Iff.rfl

end Reformulated

end GlobalTheory.LvT
