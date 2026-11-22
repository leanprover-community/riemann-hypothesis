module

public import Mathlib
public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Formalism.LocalToGlobal.LatticeGeometry.ArVolEqOfNef
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Geo

section Weights

variable {D : D7} {j : ℕ}

def wtOfN (N : ℕ) (w : WeightFamilies.Wt D j) (τ : D.what₂.Tau) (i : Fin N) : ℤ :=
  if h : i.1 < (D.R.sigW j).1 then (w.aP τ ⟨i.1, h⟩ : ℤ) + ((w.n / 2 : ℕ) : ℤ)
  else if h' : i.1 - (D.R.sigW j).1 < (D.R.sigW j).2 then
    -(w.aM τ (Fin.rev ⟨i.1 - (D.R.sigW j).1, h'⟩) : ℤ) - ((w.n / 2 : ℕ) : ℤ)
  else 0

instance instAddCommSemigroupWt : AddCommSemigroup (WeightFamilies.Wt D j) where
  add := WeightAlgebra.wadd
  add_assoc _ _ _ := wt_ext (funext fun _ => funext fun _ => Nat.add_assoc _ _ _)
    (funext fun _ => funext fun _ => Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _)
  add_comm _ _ := wt_ext (funext fun _ => funext fun _ => Nat.add_comm _ _)
    (funext fun _ => funext fun _ => Nat.add_comm _ _) (Nat.add_comm _ _)

end Weights

section Val

variable {K : Type} [Field K] [NumberField K]

def vEK (la : HeightOneSpectrum (𝓞 K)) (a : K) : EReal :=
  open Classical in if a = 0 then ⊤ else (((vAdd la a : ℤ) : ℝ) : EReal)

theorem fv_vAdd_mul (la : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vAdd la (a * b) = vAdd la a + vAdd la b := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
  ring

theorem vEK_zero (la : HeightOneSpectrum (𝓞 K)) : vEK la (0 : K) = ⊤ := by simp [vEK]

theorem vEK_ne_bot (la : HeightOneSpectrum (𝓞 K)) (a : K) : vEK la a ≠ ⊥ := by
  unfold vEK; split_ifs <;> simp

theorem vEK_of_ne (la : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    vEK la a = (((vAdd la a : ℤ) : ℝ) : EReal) := by simp [vEK, ha]

theorem vEK_mul (la : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) (b : K) :
    vEK la (a * b) = (((vAdd la a : ℤ) : ℝ) : EReal) + vEK la b := by
  by_cases hb : b = 0
  · simp [vEK, hb]
  · rw [vEK_of_ne la (mul_ne_zero ha hb), vEK_of_ne la hb, fv_vAdd_mul la ha hb]
    push_cast; rfl

theorem vEK_add (la : HeightOneSpectrum (𝓞 K)) (a b : K) :
    min (vEK la a) (vEK la b) ≤ vEK la (a + b) := by
  by_cases hab : a + b = 0
  · simp [vEK, hab]
  by_cases ha : a = 0
  · subst ha; simp
  by_cases hb : b = 0
  · subst hb; simp
  rw [vEK_of_ne la hab, vEK_of_ne la ha, vEK_of_ne la hb]
  have hn := fun (x : K) (hx : x ≠ 0) => (Valuation.ne_zero_iff (la.valuation K)).mpr hx
  rcases le_max_iff.mp (Valuation.map_add (la.valuation K) a b) with h | h
  · have := (WithZero.log_le_log (hn _ hab) (hn _ ha)).mpr h
    have h' : vAdd la a ≤ vAdd la (a + b) := by unfold vAdd; omega
    exact min_le_of_left_le (by exact_mod_cast h')
  · have := (WithZero.log_le_log (hn _ hab) (hn _ hb)).mpr h
    have h' : vAdd la b ≤ vAdd la (a + b) := by unfold vAdd; omega
    exact min_le_of_right_le (by exact_mod_cast h')

end Val

structure FormsPkg (D : D7) (G : DV.Geo D.what₂.LL) (NW : ℕ → ℕ) (CompW : ℕ → Type)
    [∀ j, Fintype (CompW j)] (algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j))
    (PtY : ℕ → ℕ → Type) : Type 1 where

  KO : Type
  [fKO : Field KO]
  [nfKO : NumberField KO]

  eO : 𝓞 KO ≃+* D.what₂.O

  kL : KO →+* D.what₂.LL

  kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)

  Cusp : (j : ℕ) → WeightFamilies.Wt D j → Type
  [acgC : ∀ j w, AddCommGroup (Cusp j w)]
  [modC : ∀ j w, Module KO (Cusp j w)]
  [fdC : ∀ j w, FiniteDimensional KO (Cusp j w)]
  [modOC : ∀ j w, Module (𝓞 KO) (Cusp j w)]
  [towC : ∀ j w, IsScalarTower (𝓞 KO) KO (Cusp j w)]

  cmp : ∀ j w (c : CompW j), Cusp j w →ₛₗ[kL] G.Fn ((algW j).Yv c)

  cmp_mem : ∀ j w c (F : Cusp j w),
    cmp j w c F ∈ G.H0 ((algW j).Yv c) ((algW j).Lw c (wtOfN (NW j) w))

  cmp_cusp : ∀ j w c (F : Cusp j w),
    G.vanishOn ((algW j).Yv c) ((algW j).Lw c (wtOfN (NW j) w)) (cmp j w c F) ((algW j).Ybd c)

  cmp_span : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ w (s : ∀ c : CompW j, G.Fn ((algW j).Yv c)),
    (∀ c, s c ∈ G.H0 ((algW j).Yv c) ((algW j).Lw c (wtOfN (NW j) w)) ∧
      G.vanishOn ((algW j).Yv c) ((algW j).Lw c (wtOfN (NW j) w)) (s c) ((algW j).Ybd c)) →
    s ∈ Submodule.span D.what₂.LL (Set.range fun (F : Cusp j w) (c : CompW j) => cmp j w c F)

  cmp_indep : ∀ j w {n : ℕ} (v : Fin n → Cusp j w), LinearIndependent KO v →
    LinearIndependent D.what₂.LL (fun i (c : CompW j) => cmp j w c (v i))

  mulC : ∀ j (w w' : WeightFamilies.Wt D j), Cusp j w → Cusp j w' → Cusp j (WeightAlgebra.wadd w w')

  cmp_mul : ∀ j w w' c (F : Cusp j w) (F' : Cusp j w'),
    cmp j (WeightAlgebra.wadd w w') c (mulC j w w' F F') = cmp j w c F * cmp j w' c F'

  supN : ∀ j w, (KO →+* ℂ) → Cusp j w → ℝ
  supN_nonneg : ∀ j w σ F, 0 ≤ supN j w σ F
  supN_eq_zero : ∀ j w σ F, supN j w σ F = 0 ↔ F = 0
  supN_smul : ∀ j w σ (a : KO) F, supN j w σ (a • F) = ‖σ a‖ * supN j w σ F
  supN_add : ∀ j w σ F G, supN j w σ (F + G) ≤ supN j w σ F + supN j w σ G

  l2NormAlt : ∀ j w, (KO →+* ℂ) → Cusp j w → ℝ
  l2Norm_nonneg_bis : ∀ j w σ F, 0 ≤ l2NormAlt j w σ F
  l2Norm_eq_zero_iff : ∀ j w σ F, l2NormAlt j w σ F = 0 ↔ F = 0
  l2Norm_smul_alt : ∀ j w σ (a : KO) F, l2NormAlt j w σ (a • F) = ‖σ a‖ * l2NormAlt j w σ F
  l2Norm_add_le' : ∀ j w σ F G, l2NormAlt j w σ (F + G) ≤ l2NormAlt j w σ F + l2NormAlt j w σ G
  l2Norm_le_supNorm_alt : ∀ j w σ F, l2NormAlt j w σ F ≤ supN j w σ F

  Cu : ℕ → Type

  Xc : ∀ j, Cu j → Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E)
  Xc_lat : ∀ j c, Submodule.IsLattice D.host.E (Xc j c)

  FJt : ∀ j (c : Cu j), WeightFamilies.ExpoSet D (Xc j c) → WeightFamilies.Wt D j → Type
  [acgF : ∀ j c χ w, AddCommGroup (FJt j c χ w)]
  [modF : ∀ j c χ w, Module KO (FJt j c χ w)]

  sg : ∀ j (c : Cu j) (χ : WeightFamilies.ExpoSet D (Xc j c)) (w : WeightFamilies.Wt D j), Cusp j w →ₗ[KO] FJt j c χ w

  Pt : ℕ → HeightOneSpectrum (𝓞 KO) → Type

  pt66 : ∀ j la, Pt j la → PtY j (WeightAlgebra.resCh la)

  vAtC : ∀ j la, Pt j la → ∀ w, Cusp j w → EReal
  vAtC_zero : ∀ j la y w, vAtC j la y w 0 = ⊤
  vAtC_ne_bot : ∀ j la y w F, vAtC j la y w F ≠ ⊥
  vAtC_add : ∀ j la y w F G, min (vAtC j la y w F) (vAtC j la y w G) ≤ vAtC j la y w (F + G)
  vAtC_smul : ∀ j la y w (a : KO) F, a ≠ 0 →
    vAtC j la y w (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + vAtC j la y w F

  vAtC_mul : ∀ j la y w w' (F : Cusp j w) (F' : Cusp j w'),
    vAtC j la y (WeightAlgebra.wadd w w') (mulC j w w' F F') = vAtC j la y w F + vAtC j la y w' F'

  thAll : ∀ j (w : WeightFamilies.Wt D j), Submodule (𝓞 KO) (Cusp j w)

  shortTh : ∀ j (w : WeightFamilies.Wt D j), Submodule (𝓞 KO) (Cusp j w)

attribute [instance] FormsPkg.fKO FormsPkg.nfKO FormsPkg.acgC FormsPkg.modC FormsPkg.fdC
  FormsPkg.modOC FormsPkg.towC FormsPkg.acgF FormsPkg.modF

namespace FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
  {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
  (P : FormsPkg D G NW CompW algW PtY)

instance (j : ℕ) : Algebra P.KO (P.FnT j) :=
  RingHom.toAlgebra ((algebraMap D.what₂.LL (∀ c : CompW j, G.Fn ((algW j).Yv c))).comp P.kL)

variable {j : ℕ}

variable (la : HeightOneSpectrum (𝓞 P.KO)) (y : P.Pt j la)

instance instCommRingForms (j : ℕ) : CommRing (P.Forms j) := (P.FormsS j).toCommRing

instance instAlgForms (j : ℕ) : Algebra P.KO (P.Forms j) := (P.FormsS j).algebra

end FormsPkg

end Formalism.L2.Geo
