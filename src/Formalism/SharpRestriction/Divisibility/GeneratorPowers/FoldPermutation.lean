import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PartialDerivativeExponent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace FormalGroupOnCopies

def OnCopies {k : Type} [CommRing k] {n d : ℕ} (S : Finset (Fin n)) (f : PS k n d) : Prop :=
  ∀ mm : Fin n × Fin d →₀ ℕ, coeff mm f ≠ 0 → ∀ i ∈ mm.support, i.1 ∈ S

end FormalGroupOnCopies

open FormalGroupOnCopies

def ColumnsStatement : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O),
    constantCoeff (B.hL k h w0) = 0 →
    ∀ (m n : ℕ) (S : Finset (Fin n)) (f₁ f₂ : PS k n d) (ι : Type) [Fintype ι]
      (cp : ι → Fin n) (u : ι → Fin d → k) (P₁ P₂ : MvPolynomial ι k),
      OnCopies S f₁ → OnCopies Sᶜ f₂ → (∀ l ∈ P₁.vars, cp l ∈ S) → (∀ l ∈ P₂.vars, cp l ∉ S) →
      nabValN B k h w0 m (f₁ * f₂) cp u (P₁ * P₂) =
        nabValN B k h w0 m f₁ cp u P₁ * nabValN B k h w0 m f₂ cp u P₂

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

variable {R : Type} [CommRing R] {d n : ℕ}

def Vc (d : ℕ) (T : Finset (Fin n)) : Set (Fin n × Fin d) := {p | p.1 ∈ T}


theorem ev_mem {m : ℕ} (V : Set (Fin n × Fin d)) (a : Fin m → Pt R n d)
    (h0 : ∀ q i, constantCoeff (a q i) = 0) (hV : ∀ q i, a q i ∈ subV R V) (g : PS R m d) :
    ev a g ∈ subV R V := by
  have hs : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => h0 p.1 p.2
  exact subst_mem (fun p : Fin m × Fin d => a p.1 p.2) hs (fun p => hV p.1 p.2) g

theorem ev_cc {m : ℕ} (a : Fin m → Pt R n d) (h0 : ∀ q i, constantCoeff (a q i) = 0)
    (g : PS R m d) (hg : constantCoeff g = 0) : constantCoeff (ev a g) = 0 := by
  unfold ev
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  all_goals first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => h0 p.1 p.2)
    | exact fun p => h0 p.1 p.2
    | exact hg

theorem ptz_cc (b : Fin n) :
    ∀ (q : Fin 2) (i : Fin d), constantCoeff ((![pt R d b, 0] : Fin 2 → Pt R n d) q i) = 0 := by
  intro q i
  fin_cases q <;> simp [pt]

theorem ptz_mem (T : Finset (Fin n)) (b : Fin n) (hb : b ∈ T) :
    ∀ (q : Fin 2) (i : Fin d), (![pt R d b, 0] : Fin 2 → Pt R n d) q i ∈ subV R (Vc d T) := by
  intro q i
  fin_cases q
  · show OnV (Vc d T) (pt R d b i)
    unfold OnV pt
    intro e he p hp
    rw [MvPowerSeries.coeff_X] at he
    split_ifs at he with h
    · subst h
      have hp' := Finsupp.support_single_subset hp
      rw [Finset.mem_singleton] at hp'
      subst hp'
      exact hb
    · exact absurd rfl he
  · exact (subV R (Vc d T)).zero_mem



theorem dofN_mem (F : Fin d → PS R 2 d) (T : Finset (Fin n)) {b : Fin n} (hb : b ∈ T)
    (u : Fin d → R) (g : PS R n d) (hg : g ∈ subV R (Vc d T)) :
    DofN F b u g ∈ subV R (Vc d T) := by
  unfold DofN
  exact sum_mem fun j _ => mul_mem (sum_mem fun i _ =>
    mul_mem (C_mem _ _) (ev_mem _ _ (ptz_cc b) (ptz_mem T b hb) _)) (pderiv_mem _ hg)

theorem dofN_mul_right (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (A B : PS R n d)
    (hB : ∀ j, pderiv R (b, j) B = 0) : DofN F b u (A * B) = DofN F b u A * B := by
  unfold DofN
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Derivation.leibniz, hB j, smul_zero, zero_add, smul_eq_mul]
  ring

theorem dofN_mul_left (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (A B : PS R n d)
    (hA : ∀ j, pderiv R (b, j) A = 0) : DofN F b u (A * B) = A * DofN F b u B := by
  unfold DofN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Derivation.leibniz, hA j, smul_zero, add_zero, smul_eq_mul]
  ring

theorem it_right (D : PS R n d → PS R n d) (B : PS R n d) (hD : ∀ A, D (A * B) = D A * B) :
    ∀ (N : ℕ) (A : PS R n d), D^[N] (A * B) = D^[N] A * B
  | 0, _ => rfl
  | N + 1, A => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hD, it_right D B hD N]

theorem it_left (D : PS R n d → PS R n d) (A : PS R n d) (hD : ∀ B, D (A * B) = A * D B) :
    ∀ (N : ℕ) (B : PS R n d), D^[N] (A * B) = A * D^[N] B
  | 0, _ => rfl
  | N + 1, B => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hD, it_left D A hD N]

theorem it_mem (D : PS R n d → PS R n d) (Q : Subalgebra R (PS R n d)) (hD : ∀ g ∈ Q, D g ∈ Q) :
    ∀ (N : ℕ) (g : PS R n d), g ∈ Q → D^[N] g ∈ Q
  | 0, _, hg => hg
  | N + 1, g, hg => by
    rw [Function.iterate_succ_apply']
    exact hD _ (it_mem D Q hD N g hg)

section Fold

variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)

theorem fold_mem (T : Finset (Fin n)) (mm : ι →₀ ℕ) (hm : ∀ l, mm l ≠ 0 → cp l ∈ T) (L : List ι)
    (A : PS R n d) (hA : A ∈ subV R (Vc d T)) :
    L.foldr (fun l g => (DofN F (cp l) (u l))^[mm l] g) A ∈ subV R (Vc d T) := by
  induction L with
  | nil => exact hA
  | cons l L ih =>
    rw [List.foldr_cons]
    by_cases hl : mm l = 0
    · rw [hl, Function.iterate_zero_apply]
      exact ih
    · exact it_mem (DofN F (cp l) (u l)) (subV R (Vc d T))
        (fun g hg => dofN_mem F T (hm l hl) (u l) g hg) (mm l) _ ih

theorem fold_mul (S : Finset (Fin n)) (m₁ m₂ : ι →₀ ℕ) (hm1 : ∀ l, m₁ l ≠ 0 → cp l ∈ S)
    (hm2 : ∀ l, m₂ l ≠ 0 → cp l ∈ Sᶜ) (L : List ι) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    L.foldr (fun l g => (DofN F (cp l) (u l))^[(m₁ + m₂) l] g) (A * B) =
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m₁ l] g) A *
        L.foldr (fun l g => (DofN F (cp l) (u l))^[m₂ l] g) B := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons]
    rw [ih, Finsupp.add_apply]
    have hA' := fold_mem F cp u S m₁ hm1 L A hA
    have hB' := fold_mem F cp u Sᶜ m₂ hm2 L B hB
    by_cases hl : cp l ∈ S
    · have h2 : m₂ l = 0 := by
        by_contra h
        exact (Finset.mem_compl.1 (hm2 l h)) hl
      rw [h2, add_zero, it_right _ _ (fun X => dofN_mul_right F _ _ X _ (fun j =>
        pderiv_kill (i := (cp l, j)) (V := Vc d Sᶜ)
          (fun hc => (Finset.mem_compl.1 (show cp l ∈ Sᶜ from hc)) hl) hB'))]
      rfl
    · have h1 : m₁ l = 0 := by
        by_contra h
        exact hl (hm1 l h)
      rw [h1, zero_add, it_left _ _ (fun X => dofN_mul_left F _ _ _ X (fun j =>
        pderiv_kill (i := (cp l, j)) (V := Vc d S) (fun hc => hl (show cp l ∈ S from hc)) hA'))]
      rfl

theorem dmon_mul (S : Finset (Fin n)) (m₁ m₂ : ι →₀ ℕ) (hm1 : ∀ l, m₁ l ≠ 0 → cp l ∈ S)
    (hm2 : ∀ l, m₂ l ≠ 0 → cp l ∈ Sᶜ) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DmonN F cp u (m₁ + m₂) (A * B) = DmonN F cp u m₁ A * DmonN F cp u m₂ B := by
  unfold DmonN
  exact fold_mul F cp u S m₁ m₂ hm1 hm2 _ A B hA hB

theorem dmon_zero (g : PS R n d) : DmonN F cp u 0 g = g := by
  simp [DmonN]

theorem dpoly_sup (P : MvPolynomial ι R) (T : Finset (ι →₀ ℕ)) (hT : P.support ⊆ T)
    (g : PS R n d) : DpolyN F cp u P g = ∑ mm ∈ T, C (P.coeff mm) * DmonN F cp u mm g := by
  unfold DpolyN
  apply Finset.sum_subset hT
  intro mm _ hmm
  have h0 : P.coeff mm = 0 := by simpa [MvPolynomial.mem_support_iff] using hmm
  rw [h0, map_zero, zero_mul]

theorem dpoly_add (P Q : MvPolynomial ι R) (g : PS R n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [dpoly_sup F cp u (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    dpoly_sup F cp u P (P.support ∪ Q.support) Finset.subset_union_left,
    dpoly_sup F cp u Q (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mm _ => ?_)
  rw [MvPolynomial.coeff_add, map_add, add_mul]

theorem dpoly_monomial (mm : ι →₀ ℕ) (a : R) (g : PS R n d) :
    DpolyN F cp u (MvPolynomial.monomial mm a) g = C a * DmonN F cp u mm g := by
  classical
  rw [dpoly_sup F cp u _ {mm} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

theorem dpoly_one (g : PS R n d) : DpolyN F cp u 1 g = g := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, dpoly_monomial, map_one, one_mul, dmon_zero]

def dpolyHom (g : PS R n d) : MvPolynomial ι R →+ PS R n d where
  toFun P := DpolyN F cp u P g
  map_zero' := by simp [DpolyN]
  map_add' P Q := dpoly_add F cp u P Q g

theorem dpoly_mul (S : Finset (Fin n)) (P₁ P₂ : MvPolynomial ι R) (h1 : ∀ l ∈ P₁.vars, cp l ∈ S)
    (h2 : ∀ l ∈ P₂.vars, cp l ∉ S) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DpolyN F cp u (P₁ * P₂) (A * B) = DpolyN F cp u P₁ A * DpolyN F cp u P₂ B := by
  have e : P₁ * P₂ = ∑ m1 ∈ P₁.support, ∑ m2 ∈ P₂.support,
      MvPolynomial.monomial (m1 + m2) (P₁.coeff m1 * P₂.coeff m2) := by
    conv_lhs => rw [P₁.as_sum, P₂.as_sum]
    rw [Finset.sum_mul_sum]
    simp_rw [MvPolynomial.monomial_mul]
  calc DpolyN F cp u (P₁ * P₂) (A * B) = dpolyHom F cp u (A * B) (P₁ * P₂) := rfl
    _ = ∑ m1 ∈ P₁.support, ∑ m2 ∈ P₂.support,
          C (P₁.coeff m1) * DmonN F cp u m1 A * (C (P₂.coeff m2) * DmonN F cp u m2 B) := by
      rw [e, map_sum]
      refine Finset.sum_congr rfl fun m1 hm1 => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun m2 hm2 => ?_
      have hq1 : ∀ l, m1 l ≠ 0 → cp l ∈ S := fun l hl =>
        h1 l ((MvPolynomial.mem_vars_iff_mem_support l).2 ⟨m1, hm1, Finsupp.mem_support_iff.2 hl⟩)
      have hq2 : ∀ l, m2 l ≠ 0 → cp l ∈ Sᶜ := fun l hl =>
        Finset.mem_compl.2 (h2 l ((MvPolynomial.mem_vars_iff_mem_support l).2 ⟨m2, hm2, Finsupp.mem_support_iff.2 hl⟩))
      show DpolyN F cp u _ (A * B) = _
      rw [dpoly_monomial, dmon_mul F cp u S m1 m2 hq1 hq2 A B hA hB, map_mul]
      ring
    _ = DpolyN F cp u P₁ A * DpolyN F cp u P₂ B := by
      unfold DpolyN
      rw [Finset.sum_mul_sum]

theorem key_left (S : Finset (Fin n)) (P₁ : MvPolynomial ι R) (h1 : ∀ l ∈ P₁.vars, cp l ∈ S)
    (A B : PS R n d) (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DpolyN F cp u P₁ (A * B) = DpolyN F cp u P₁ A * B := by
  have h := dpoly_mul F cp u S P₁ 1 h1 (by intro l hl; simp [MvPolynomial.vars_one] at hl) A B hA hB
  rwa [mul_one, dpoly_one] at h

theorem key_right (S : Finset (Fin n)) (P₂ : MvPolynomial ι R) (h2 : ∀ l ∈ P₂.vars, cp l ∉ S)
    (A B : PS R n d) (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DpolyN F cp u P₂ (A * B) = A * DpolyN F cp u P₂ B := by
  have h := dpoly_mul F cp u S 1 P₂ (by intro l hl; simp [MvPolynomial.vars_one] at hl) h2 A B hA hB
  rwa [one_mul, dpoly_one] at h

theorem value_split (S : Finset (Fin n)) (P₁ P₂ : MvPolynomial ι R) (h1 : ∀ l ∈ P₁.vars, cp l ∈ S)
    (h2 : ∀ l ∈ P₂.vars, cp l ∉ S) (f₁ f₂ ES ET : PS R n d) (hf1 : f₁ ∈ subV R (Vc d S))
    (hf2 : f₂ ∈ subV R (Vc d Sᶜ)) (hES : ES ∈ subV R (Vc d S)) (hET : ET ∈ subV R (Vc d Sᶜ))
    (c1 : constantCoeff ES = 1) (c2 : constantCoeff ET = 1) :
    constantCoeff (DpolyN F cp u (P₁ * P₂) (f₁ * f₂ * (ES * ET))) =
      constantCoeff (DpolyN F cp u P₁ (f₁ * (ES * ET))) *
        constantCoeff (DpolyN F cp u P₂ (f₂ * (ES * ET))) := by
  have hA : f₁ * ES ∈ subV R (Vc d S) := Subalgebra.mul_mem _ hf1 hES
  have hB : f₂ * ET ∈ subV R (Vc d Sᶜ) := Subalgebra.mul_mem _ hf2 hET
  have e1 : f₁ * f₂ * (ES * ET) = (f₁ * ES) * (f₂ * ET) := by ring
  have e2 : f₁ * (ES * ET) = (f₁ * ES) * ET := by ring
  have e3 : f₂ * (ES * ET) = ES * (f₂ * ET) := by ring
  rw [e1, e2, e3, dpoly_mul F cp u S P₁ P₂ h1 h2 _ _ hA hB, key_left F cp u S P₁ h1 _ _ hA hET,
    key_right F cp u S P₂ h2 _ _ hES hB, map_mul, map_mul, map_mul, c1, c2, mul_one, one_mul]

end Fold

end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies


end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

variable {k : Type} [CommRing k] {d : ℕ}

def embP {n' n : ℕ} (e : Fin n' → Fin n) : Fin n' → Pt k n d := fun b => pt k d (e b)

theorem cz_embP {n' n : ℕ} (e : Fin n' → Fin n) : LogPf.CZ (embP (k := k) (d := d) e) := by
  intro j i
  simp [embP, pt]

theorem cz_ptz {n : ℕ} (b : Fin n) : LogPf.CZ (![pt k d b, 0] : Fin 2 → Pt k n d) := by
  intro j i
  fin_cases j <;> simp [pt]

theorem cc_ev {m n : ℕ} {a : Fin m → Pt k n d} (ha : LogPf.CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have e1 : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  conv_lhs => rw [e1]
  rw [LogPf.ev_add ha, LogPf.ev_C ha, map_add, LogPf.constantCoeff_ev ha h0, add_zero, constantCoeff_C]

theorem pderiv_embP {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (g : PS k n' d) (b : Fin n')
    (j : Fin d) : pderiv k (e b, j) (ev (embP e) g) = ev (embP e) (pderiv k (b, j) g) := by
  classical
  rw [LogPf.pderiv_ev (cz_embP e), Finset.sum_eq_single (b, j)]
  · simp [embP, LogPf.pderiv_pt]
  · intro p _ hp
    rw [show embP (k := k) (d := d) e p.1 p.2 = pt k d (e p.1) p.2 from rfl, LogPf.pderiv_pt, if_neg, mul_zero]
    intro hc
    apply hp
    have h1 : e p.1 = e b := congrArg Prod.fst hc
    have h2 : p.2 = j := congrArg Prod.snd hc
    exact Prod.ext (he h1) h2
  · simp

theorem pderiv_ev_embP_of_notMem_range {n' n : ℕ} (e : Fin n' → Fin n) (g : PS k n' d) (c : Fin n) (hc : ∀ b, e b ≠ c)
    (j : Fin d) : pderiv k (c, j) (ev (embP e) g) = 0 := by
  classical
  refine LogPf.pderiv_ev_zero (cz_embP e) g (c, j) fun b i => ?_
  rw [show embP (k := k) (d := d) e b i = pt k d (e b) i from rfl, LogPf.pderiv_pt, if_neg]
  intro h
  exact hc b (congrArg Prod.fst h)

theorem ev_ptz {n' n : ℕ} (e : Fin n' → Fin n) (b : Fin n') (X : PS k 2 d) :
    ev ![pt k d (e b), 0] X = ev (embP e) (ev ![pt k d b, 0] X) := by
  rw [LogPf.ev_ev (cz_embP e) (cz_ptz b)]
  congr 1
  funext q i
  fin_cases q
  · simp [LogPf.ev_X (cz_embP e), embP, pt]
  · simp [LogPf.ev_zero' (cz_embP e)]

theorem dofN_embP (F : Fin d → PS k 2 d) {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (b : Fin n')
    (u : Fin d → k) (g : PS k n' d) : DofN F (e b) u (ev (embP e) g) = ev (embP e) (DofN F b u g) := by
  unfold DofN
  rw [LogPf.ev_sum (cz_embP e)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_sum (cz_embP e), pderiv_embP e he]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_C (cz_embP e), ev_ptz]

section Comm

def cB (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) : Fin n × Fin d → PS k n d := fun t =>
  if t.1 = b then ev (embP (fun _ : Fin 1 => b)) (WickVanishing.Nab.co G u ((0 : Fin 1), t.2)) else 0

theorem inj1 {n : ℕ} (b : Fin n) : Function.Injective (fun _ : Fin 1 => b) := by
  intro x y _
  exact Subsingleton.elim x y

theorem dofN_vf (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN G.F b u g = WickVanishing.Nab.vf (cB G b u) g := by
  classical
  unfold DofN WickVanishing.Nab.vf cB
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos rfl]
    congr 1
    unfold WickVanishing.Nab.co
    rw [LogPf.ev_sum (cz_embP _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LogPf.ev_mul (cz_embP _), LogPf.ev_C (cz_embP _)]
    congr 1
    exact ev_ptz (fun _ : Fin 1 => b) 0 _
  · intro c _ hc
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg hc, zero_mul]
  · simp

theorem cB_one (G : FGLaw k d) (u : Fin d → k) : cB G (0 : Fin 1) u = WickVanishing.Nab.co G u := by
  funext t
  have h1 : t.1 = 0 := Subsingleton.elim _ _
  have hp : (embP (k := k) (d := d) (fun _ : Fin 1 => (0 : Fin 1))) = fun j => pt k (n := 1) d j := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  simp only [cB, if_pos h1, hp, LogPf.ev_pt]
  rw [show t = ((0 : Fin 1), t.2) from Prod.ext h1 rfl]

theorem dofN_cB_ne (G : FGLaw k d) {n : ℕ} (b c : Fin n) (hbc : b ≠ c) (u v : Fin d → k) (t : Fin n × Fin d) :
    DofN G.F b u (cB G c v t) = 0 := by
  unfold cB
  split_ifs
  · unfold DofN
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_ev_embP_of_notMem_range _ _ b (fun _ => Ne.symm hbc) j, mul_zero]
  · unfold DofN
    simp

theorem dofN_comm (G : FGLaw k d) {n : ℕ} (b b' : Fin n) (u v : Fin d → k) (g : PS k n d) :
    DofN G.F b u (DofN G.F b' v g) = DofN G.F b' v (DofN G.F b u g) := by
  classical
  rw [dofN_vf G b, dofN_vf G b', dofN_vf G b', dofN_vf G b, ← sub_eq_zero, WickVanishing.Nab.vf_comm]
  have hz : (fun t => WickVanishing.Nab.vf (cB G b u) (cB G b' v t) - WickVanishing.Nab.vf (cB G b' v) (cB G b u t)) =
      fun _ => (0 : PS k n d) := by
    funext t
    rw [← dofN_vf G b, ← dofN_vf G b']
    by_cases hb : b = b'
    · rw [← hb]
      have hE : ∀ (w : Fin d → k) (X : PS k 1 d),
          DofN G.F b w (ev (embP (fun _ : Fin 1 => b)) X) = ev (embP (fun _ : Fin 1 => b)) (DofN G.F 0 w X) :=
        fun w X => dofN_embP G.F (fun _ : Fin 1 => b) (inj1 b) 0 w X
      unfold cB
      by_cases ht : t.1 = b
      · rw [if_pos ht, if_pos ht, hE, hE, ← LogPf.ev_sub (cz_embP _), dofN_vf G (0 : Fin 1),
          dofN_vf G (0 : Fin 1), cB_one, cB_one, WickVanishing.Nab.co_bracket G u v, LogPf.ev_zero' (cz_embP _)]
      · rw [if_neg ht, if_neg ht]
        unfold DofN
        simp
    · rw [dofN_cB_ne G b b' hb, dofN_cB_ne G b' b (Ne.symm hb), sub_zero]
  rw [hz, WickVanishing.Nab.vf_zeroc]

end Comm

section Fold

variable {n' n : ℕ} (F : Fin d → PS k 2 d)
  (hF : ∀ (b b' : Fin n) (v v' : Fin d → k) (G : PS k n d), DofN F b v (DofN F b' v' G) = DofN F b' v' (DofN F b v G))
  (e : Fin n' → Fin n) (he : Function.Injective e) {ι ι' : Type} [Fintype ι] [Fintype ι']
  (cp : ι → Fin n) (u : ι → Fin d → k) (cp' : ι' → Fin n') (u' : ι' → Fin d → k) (φ : ι' → ι)
  (hφ : Function.Injective φ) (hcp : ∀ l, cp (φ l) = e (cp' l)) (hu : ∀ l, u (φ l) = u' l)
include hF he hφ hcp hu

end Fold

section Val

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (K : Type) [CommRing K]
  [Algebra ℚ K] [Algebra R K]

end Val

end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
end
end
