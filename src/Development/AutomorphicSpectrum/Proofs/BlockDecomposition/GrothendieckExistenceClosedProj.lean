import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
import BuildAid.ForwardExisting
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveCharts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Saturation
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionPullbackKernelSup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSup

section
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.Tower

variable {R : Type} [CommRing R] {N : ℕ}

theorem sub_tail_mem (I : Ideal R) (e : ℕ) (G : ℕ → MvPolynomial (Fin (N + 1)) R)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) (m k : ℕ) :
    G m - G (m + k) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : G (m + k) - G (m + k + 1) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
      Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hd (m + k))
    have h3 : G m - G (m + (k + 1)) = (G m - G (m + k)) + (G (m + k) - G (m + k + 1)) := by
      rw [show m + (k + 1) = m + k + 1 from rfl]
      ring
    rw [h3]
    exact add_mem ih h2

theorem exists_limit_form (I : Ideal R) [IsPrecomplete I R] (n e : ℕ)
    (G : ℕ → MvPolynomial (Fin (N + 1)) R) (hom : ∀ i, (G i).IsHomogeneous n)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    ∃ g : MvPolynomial (Fin (N + 1)) R, g.IsHomogeneous n ∧
      ∀ i, G i - g ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have htop : ∀ k, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcoef : ∀ d i k, coeff d (G i) - coeff d (G (i + k)) ∈ I ^ (e + i + 1) := by
    intro d i k
    have h := (mem_map_C_iff.1 (sub_tail_mem I e G hd i k)) d
    rwa [coeff_sub] at h
  have hL : ∀ d, ∃ Ld : R, ∀ i, coeff d (G i) - Ld ∈ I ^ (e + i + 1) := by
    intro d
    obtain ⟨Ld, hLd⟩ := IsPrecomplete.prec' (I := I) (fun i => coeff d (G i)) (by
      intro m n hmn
      rw [SModEq.sub_mem, htop]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact Ideal.pow_le_pow_right (by omega) (hcoef d m k))
    refine ⟨Ld, fun i => ?_⟩
    have h1 := hcoef d i (e + 1)
    have h2 := hLd (i + (e + 1))
    rw [SModEq.sub_mem, htop] at h2
    have h3 : coeff d (G i) - Ld =
        (coeff d (G i) - coeff d (G (i + (e + 1)))) + (coeff d (G (i + (e + 1))) - Ld) := by ring
    rw [h3]
    exact add_mem h1 (Ideal.pow_le_pow_right (by omega) h2)
  choose Lf hLf using hL
  refine ⟨∑ d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n, monomial d (Lf d), ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ (fun d hd => isHomogeneous_monomial _ ?_)
    rw [Finset.mem_finsuppAntidiag] at hd
    rw [Finsupp.degree_eq_sum]
    exact hd.1
  · intro i
    rw [mem_map_C_iff]
    intro d
    rw [coeff_sub, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases hdS : d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n
    · rw [if_pos hdS]
      exact hLf d i
    · rw [if_neg hdS, sub_zero]
      have h0 : coeff d (G i) = 0 := by
        by_contra hne
        apply hdS
        have hw := hom i hne
        rw [Finset.mem_finsuppAntidiag]
        refine ⟨?_, Finset.subset_univ _⟩
        rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
        exact hw
      rw [h0]
      exact zero_mem _

theorem exists_form_in_all (I : Ideal R) [IsPrecomplete I R]
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R))
    (hbase : ∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e)
    (hanti : ∀ e, L (e + 1) ≤ L e) (n₀ : ℕ)
    (hlift : ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (e n : ℕ) (hn : n₀ ≤ n) (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ L e)
    (hgn : g.IsHomogeneous n) :
    ∃ g' : MvPolynomial (Fin (N + 1)) R, g'.IsHomogeneous n ∧ (∀ j, g' ∈ L j) ∧
      g - g' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have hL : Antitone L := antitone_nat_of_succ_le hanti
  let lift' : ℕ → MvPolynomial (Fin (N + 1)) R → MvPolynomial (Fin (N + 1)) R := fun j f =>
    if h : ∃ f' ∈ L (j + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (j + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) then h.choose else f
  let s : ℕ → MvPolynomial (Fin (N + 1)) R := fun i =>
    Nat.rec (motive := fun _ => MvPolynomial (Fin (N + 1)) R) g (fun k f => lift' (e + k) f) i
  have hsS : ∀ i, s (i + 1) = lift' (e + i) (s i) := fun i => rfl
  have hstep : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n →
      s (i + 1) ∈ L (e + i + 1) ∧ (s (i + 1)).IsHomogeneous n ∧
        s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
    rintro i ⟨h1, h2⟩
    have hex := hlift (e + i) n hn (s i) h1 h2
    rw [hsS]
    simp only [lift']
    rw [dif_pos hex]
    exact hex.choose_spec
  have hinv : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n := by
    intro i
    induction i with
    | zero => exact ⟨hg, hgn⟩
    | succ i ih => exact ⟨(hstep i ih).1, (hstep i ih).2.1⟩
  have hd : ∀ i, s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
    fun i => (hstep i (hinv i)).2.2
  obtain ⟨g', hg'n, hg'⟩ := exists_limit_form I n e s (fun i => (hinv i).2) hd
  refine ⟨g', hg'n, fun j => ?_, hg' 0⟩
  have h1 : s j ∈ L j := hL (by omega : j ≤ e + j) (hinv j).1
  have h2 : s j - g' ∈ L j := hL (by omega : j ≤ e + j) (hbase (e + j) (hg' j))
  have h3 : g' = s j - (s j - g') := by ring
  rw [h3]
  exact sub_mem h1 h2

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem exists_limit_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e, L (e + 1) ≤ L e) →
    ∀ (n₀ : ℕ), (∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ J : Ideal (MvPolynomial (Fin (N + 1)) R), HomogIdeal J ∧ ∀ e, J ≤ L e ∧
        ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
          J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  intro R _ I hI N L hhom hbase hanti n₀ hlift
  have : IsPrecomplete I R := hI.toIsPrecomplete
  classical
  let S : Set (MvPolynomial (Fin (N + 1)) R) := {g | ∃ n, n₀ ≤ n ∧ g.IsHomogeneous n ∧ ∀ j, g ∈ L j}
  refine ⟨Ideal.span S, ?_, fun e => ⟨?_, ?_⟩⟩
  · intro d f hf
    have hH : (Ideal.span S).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) R) :=
      Ideal.homogeneous_span _ _ (fun x hx => by
        obtain ⟨n, _, hn, _⟩ := hx
        exact ⟨n, (mem_homogeneousSubmodule n x).2 hn⟩)
    have h := (Ideal.IsHomogeneous.mem_iff _ hH).1 hf d
    have e1 : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) f d :
        MvPolynomial (Fin (N + 1)) R) = homogeneousComponent d f := decomposition.decompose'_apply f d
    rwa [e1] at h
  · rw [Ideal.span_le]
    rintro g ⟨n, _, _, hall⟩
    exact hall e
  · intro f hf k
    refine ⟨n₀, ?_⟩
    rw [← sum_homogeneousComponent f, Finset.mul_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have hmem : X k ^ n₀ * homogeneousComponent d f ∈ L e := Ideal.mul_mem_left _ _ (hhom e d f hf)
    have hh : (X k ^ n₀ * homogeneousComponent d f).IsHomogeneous (n₀ + d) :=
      (isHomogeneous_X_pow k n₀).mul (homogeneousComponent_isHomogeneous d f)
    obtain ⟨g', hg'n, hall, hdiff⟩ :=
      exists_form_in_all I L hbase hanti n₀ hlift e (n₀ + d) (Nat.le_add_right _ _) _ hmem hh
    have h3 : X k ^ n₀ * homogeneousComponent d f = g' + (X k ^ n₀ * homogeneousComponent d f - g') := by
      ring
    rw [h3]
    exact add_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨n₀ + d, Nat.le_add_right _ _, hg'n, hall⟩))
      (Ideal.mem_sup_right hdiff)

end GlobalTheory.CompanionTheory.GE.Tower
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_lift_adic_filtration : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e, L (e + 1) ≤ L e) →
    ∀ (n₀ : ℕ), (∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ J : Ideal (MvPolynomial (Fin (N + 1)) R), HomogIdeal J ∧ ∀ e, J ≤ L e ∧
        ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
          J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.Tower.exists_limit_ideal
end

section
section
noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.SerreVan

variable {B : Type} [CommRing B] {M : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem comp_mul {a : MvPolynomial (Fin M) B} {e : ℕ} (ha : a.IsHomogeneous e) (d : ℕ)
    (f : MvPolynomial (Fin M) B) :
    homogeneousComponent (e + d) (a * f) = a * homogeneousComponent d f := by
  have h := DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (Fin M) B)
    (i := e) (j := d) (a := a) (b := f) ha
  rw [← decomposition.decompose'_apply, ← decomposition.decompose'_apply]
  exact h

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem comp_zero_X_mul (i : Fin M) (f : MvPolynomial (Fin M) B) :
    homogeneousComponent 0 (X i * f) = 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem_of_not_le (homogeneousSubmodule (Fin M) B)
    (i := 1) (n := 0) (a := X i) (b := f) (isHomogeneous_X B i) (by norm_num)
  rw [← decomposition.decompose'_apply]
  exact h

noncomputable def sat {R : Type} [CommRing R] (Q : Ideal R) (x : R) : Ideal R :=
  _root_.UpperTheory.Reformulated.B.IdealSaturationByElement.sat Q x

def V0 (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ f ∈ P, f.IsHomogeneous n → (∀ i ∈ W, ∃ m : ℕ, X i ^ m * f ∈ Q) → f ∈ Q

def V1 (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin M → MvPolynomial (Fin M) B),
    (∀ i ∈ W, f i ∈ P ∧ (f i).IsHomogeneous (n + k)) →
    (∀ i ∈ W, ∀ j ∈ W, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ Q) →
    ∃ g ∈ P, g.IsHomogeneous n ∧ ∀ i ∈ W, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ Q

section Extension

variable {W : Finset (Fin M)} {P P' Q : Ideal (MvPolynomial (Fin M) B)} {n₀ : ℕ}

end Extension

section Steps

variable {W : Finset (Fin M)} {P P' Q : Ideal (MvPolynomial (Fin M) B)} {n₀ : ℕ}

end Steps

section Base

variable {P Q : Ideal (MvPolynomial (Fin M) B)}

end Base

section Main

variable {P Q : Ideal (MvPolynomial (Fin M) B)}

theorem charts [IsNoetherianRing B] (W : Finset (Fin M)) :
    ∀ P Q : Ideal (MvPolynomial (Fin M) B), HomogIdeal P → HomogIdeal Q → Q ≤ P →
      (∀ j, j ∉ W → ∃ k : ℕ, ∀ f ∈ P, X j ^ k * f ∈ Q) →
      ∃ n₀, V0 W P Q n₀ ∧ V1 W P Q n₀ :=
  _root_.UpperTheory.Reformulated.B.ProjectiveCharts.charts W

theorem serre_vanishing : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (N : ℕ)
    (P : Ideal (MvPolynomial (Fin (N + 1)) B)), HomogIdeal P →
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin (N + 1) → MvPolynomial (Fin (N + 1)) B),
      (∀ i, (f i).IsHomogeneous (n + k)) →
      (∀ i j, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ P) →
      ∃ g : MvPolynomial (Fin (N + 1)) B, g.IsHomogeneous n ∧
        ∀ i, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ P := by
  intro B _ _ N P hP
  obtain ⟨n₀, -, h⟩ := charts (B := B) (M := N + 1) Finset.univ ⊤ P (fun _ _ _ => trivial) hP
    le_top (fun j hj => absurd (Finset.mem_univ j) hj)
  refine ⟨n₀, fun n hn k f hf hc => ?_⟩
  obtain ⟨g, -, hgh, hg⟩ := h n hn k f (fun i _ => ⟨trivial, hf i⟩)
    (fun i _ j _ => hc i j)
  exact ⟨g, hgh, fun i => hg i (Finset.mem_univ i)⟩

end Main

end GlobalTheory.CompanionTheory.GE.SerreVan
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_sections_glue_homogeneous : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (N : ℕ) (P : Ideal (MvPolynomial (Fin (N + 1)) B)), HomogIdeal P →
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin (N + 1) → MvPolynomial (Fin (N + 1)) B),
      (∀ i, (f i).IsHomogeneous (n + k)) →
      (∀ i j, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ P) →
      ∃ g : MvPolynomial (Fin (N + 1)) B, g.IsHomogeneous n ∧
        ∀ i, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ P := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.SerreVan.serre_vanishing
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.Lift

variable {R : Type} [CommRing R] (I : Ideal R) (N : ℕ)

def iota : reesAlgebra I →+* Polynomial (MvPolynomial (Fin (N + 1)) R) :=
  (Polynomial.mapRingHom (C : R →+* MvPolynomial (Fin (N + 1)) R)).comp
    (reesAlgebra I).val.toRingHom

def Psi : MvPolynomial (Fin (N + 1)) (reesAlgebra I) →+*
    Polynomial (MvPolynomial (Fin (N + 1)) R) :=
  eval₂Hom (iota I N) (fun i => Polynomial.C (X i))

def phi (d : ℕ) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    MvPolynomial (Fin (N + 1)) R :=
  (Psi I N p).coeff d

variable {I N}

theorem phi_add (d : ℕ) (p q : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (p + q) = phi I N d p + phi I N d q := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_add, Polynomial.coeff_add]

theorem phi_sub (d : ℕ) (p q : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (p - q) = phi I N d p - phi I N d q := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_sub, Polynomial.coeff_sub]

theorem phi_zero (d : ℕ) : phi I N d 0 = 0 := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_zero, Polynomial.coeff_zero]

theorem phi_X_mul (d : ℕ) (i : Fin (N + 1)) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (X i * p) = X i * phi I N d p := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_mul, GlobalTheory.CompanionTheory.GE.Lift.Psi, MvPolynomial.eval₂Hom_X', Polynomial.coeff_C_mul]

theorem phi_X_pow_mul (d : ℕ) (i : Fin (N + 1)) (m : ℕ)
    (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (X i ^ m * p) = X i ^ m * phi I N d p := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', mul_assoc, GlobalTheory.CompanionTheory.GE.Lift.phi_X_mul, ih, ← mul_assoc, ← pow_succ']

theorem phi_C_mul (d : ℕ) (b : reesAlgebra I) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (C b * p) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal d,
      C ((b : Polynomial R).coeff x.1) * phi I N x.2 p := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_mul, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.CompanionTheory.GE.Lift.Psi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
    GlobalTheory.CompanionTheory.GE.Lift.iota, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rfl

theorem phi_monomial (d : ℕ) (s : Fin (N + 1) →₀ ℕ) (b : reesAlgebra I) :
    phi I N d (monomial s b) = monomial s ((b : Polynomial R).coeff d) := by
  have hprod : (s.prod fun i k => (Polynomial.C (X i) : Polynomial (MvPolynomial (Fin (N + 1)) R)) ^ k) =
      Polynomial.C (s.prod fun i k => X i ^ k) := by
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [GlobalTheory.CompanionTheory.GE.Lift.phi, GlobalTheory.CompanionTheory.GE.Lift.Psi, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_monomial, hprod, Polynomial.coeff_mul_C, GlobalTheory.CompanionTheory.GE.Lift.iota,
    RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map, MvPolynomial.monomial_eq]
  rfl

theorem coeff_phi (d : ℕ) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I))
    (s : Fin (N + 1) →₀ ℕ) :
    coeff s (phi I N d p) = ((coeff s p : reesAlgebra I) : Polynomial R).coeff d := by
  induction p using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [GlobalTheory.CompanionTheory.GE.Lift.phi_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq =>
    rw [GlobalTheory.CompanionTheory.GE.Lift.phi_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
    simp

theorem phi_mem_map (d : ℕ) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d p ∈ (I ^ d).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  rw [mem_map_C_iff]
  intro s
  rw [coeff_phi]
  exact (mem_reesAlgebra_iff I _).1 (coeff s p).2 d

theorem phi_isHomogeneous (d n : ℕ) {p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)}
    (hp : p.IsHomogeneous n) : (phi I N d p).IsHomogeneous n := by
  intro s hs
  apply hp
  intro h0
  apply hs
  rw [coeff_phi, h0]
  simp

theorem phi_homogeneousComponent (d e : ℕ) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (homogeneousComponent e p) = homogeneousComponent e (phi I N d p) := by
  ext s
  simp only [GlobalTheory.CompanionTheory.GE.Lift.coeff_phi, MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp

theorem exists_lift (d : ℕ) (t : MvPolynomial (Fin (N + 1)) R)
    (ht : t ∈ (I ^ d).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    ∃ τ : MvPolynomial (Fin (N + 1)) (reesAlgebra I),
      ∀ s, ((coeff s τ : reesAlgebra I) : Polynomial R) = Polynomial.monomial d (coeff s t) := by
  have hmem : ∀ s, Polynomial.monomial d (coeff s t) ∈ reesAlgebra I := by
    intro s
    rw [mem_reesAlgebra_iff]
    intro i
    rw [Polynomial.coeff_monomial]
    split_ifs with h
    · subst h
      exact MvPolynomial.mem_map_C_iff.1 ht s
    · exact zero_mem _
  refine ⟨∑ s ∈ t.support, monomial s (⟨Polynomial.monomial d (coeff s t), hmem s⟩ : reesAlgebra I),
    fun s => ?_⟩
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h]
    simp

theorem phi_lift {d : ℕ} {t : MvPolynomial (Fin (N + 1)) R}
    {τ : MvPolynomial (Fin (N + 1)) (reesAlgebra I)}
    (h : ∀ s, ((coeff s τ : reesAlgebra I) : Polynomial R) = Polynomial.monomial d (coeff s t))
    (d' : ℕ) : phi I N d' τ = if d' = d then t else 0 := by
  ext s
  rw [GlobalTheory.CompanionTheory.GE.Lift.coeff_phi, h, Polynomial.coeff_monomial]
  by_cases hd : d' = d
  · subst hd
    simp
  · rw [if_neg (Ne.symm hd), if_neg hd, MvPolynomial.coeff_zero]

theorem lift_isHomogeneous {d n : ℕ} {t : MvPolynomial (Fin (N + 1)) R}
    {τ : MvPolynomial (Fin (N + 1)) (reesAlgebra I)}
    (h : ∀ s, ((coeff s τ : reesAlgebra I) : Polynomial R) = Polynomial.monomial d (coeff s t))
    (ht : t.IsHomogeneous n) : τ.IsHomogeneous n := by
  intro s hs
  apply ht
  intro h0
  apply hs
  apply Subtype.ext
  rw [h, h0]
  simp

theorem pow_mul_le (I : Ideal R) (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R))
    (hbase : ∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e)
    (hsat : ∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ L e) → f ∈ L e)
    (hcompat : ∀ e, ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (k e : ℕ) :
    (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k) := by
  have hstep : ∀ e, I.map (C : R →+* MvPolynomial (Fin (N + 1)) R) * L e ≤ L (e + 1) := by
    intro e
    rw [Ideal.mul_le]
    intro a ha f hf
    apply hsat (e + 1)
    intro j
    obtain ⟨m, hm⟩ := hcompat e f hf j
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hm
    refine ⟨m, ?_⟩
    have hav : a * v ∈ L (e + 1) := by
      refine hbase (e + 1) ?_
      rw [pow_succ', Ideal.map_mul]
      exact Ideal.mul_mem_mul ha hv
    have hsplit : X j ^ m * (a * f) = a * u + a * v := by
      rw [← mul_add, huv]
      ring
    rw [hsplit]
    exact add_mem (Ideal.mul_mem_left _ _ hu) hav
  induction k generalizing e with
  | zero => simp
  | succ k ih =>
    calc (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ (k + 1) * L e
        = (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k *
            ((I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) * L e) := by
          rw [pow_succ, mul_assoc]
      _ ≤ (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L (e + 1) :=
          Ideal.mul_mono_right (hstep e)
      _ ≤ L (e + 1 + k) := ih (e + 1)
      _ = L (e + (k + 1)) := by rw [add_assoc, add_comm 1 k]

def reesIdeal (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R))
    (hL : ∀ k e, (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k)) :
    Ideal (MvPolynomial (Fin (N + 1)) (reesAlgebra I)) where
  carrier := {p | ∀ d, phi I N d p ∈ L d}
  add_mem' := fun hp hq d => by
    rw [phi_add]
    exact add_mem (hp d) (hq d)
  zero_mem' := fun d => by
    rw [phi_zero]
    exact zero_mem _
  smul_mem' := fun c p hp => by
    show ∀ d, phi I N d (c * p) ∈ L d
    induction c using MvPolynomial.induction_on with
    | C b =>
      intro d
      rw [phi_C_mul]
      refine sum_mem fun x hx => ?_
      have hx' : x.2 + x.1 = d := by
        rw [add_comm]
        exact Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [← hx']
      refine hL x.1 x.2 ?_
      refine Ideal.mul_mem_mul ?_ (hp x.2)
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).1 b.2 x.1)
    | add a b ha hb =>
      intro d
      rw [add_mul, phi_add]
      exact add_mem (ha d) (hb d)
    | mul_X a i ha =>
      intro d
      rw [mul_comm a, mul_assoc, phi_X_mul]
      exact Ideal.mul_mem_left _ _ (ha d)

theorem mem_reesIdeal {L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)}
    {hL : ∀ k e, (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k)}
    {p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)} :
    p ∈ reesIdeal L hL ↔ ∀ d, phi I N d p ∈ L d :=
  Iff.rfl

theorem reesIdeal_homog {L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)}
    (hhom : ∀ e, HomogIdeal (L e))
    (hL : ∀ k e, (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k)) :
    HomogIdeal (reesIdeal L hL) := by
  unfold GlobalTheory.CompanionTheory.GE.HomogIdeal at hhom ⊢
  intro e p hp
  rw [GlobalTheory.CompanionTheory.GE.Lift.mem_reesIdeal] at hp ⊢
  intro d
  rw [GlobalTheory.CompanionTheory.GE.Lift.phi_homogeneousComponent]
  exact hhom d e _ (hp d)

theorem homogIdeal_map (J : Ideal R) :
    HomogIdeal (J.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) := by
  unfold GlobalTheory.CompanionTheory.GE.HomogIdeal
  intro d f hf
  rw [MvPolynomial.mem_map_C_iff] at hf ⊢
  intro m
  rw [MvPolynomial.coeff_homogeneousComponent]
  split_ifs
  · exact hf m
  · exact zero_mem _

theorem uniform_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ L e) → f ∈ L e) →
    (∀ e, ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ n₀ : ℕ, ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  intro R _ _ I N L hhom hbase hsat hcompat
  have hL : ∀ k e, (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k) :=
    GlobalTheory.CompanionTheory.GE.Lift.pow_mul_le I L hbase hsat hcompat
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.compatible_sections_glue_homogeneous (reesAlgebra I) N
    (GlobalTheory.CompanionTheory.GE.Lift.reesIdeal L hL) (GlobalTheory.CompanionTheory.GE.Lift.reesIdeal_homog hhom hL)
  refine ⟨n₀, fun e n hn f hf hfh => ?_⟩
  choose m hm using hcompat e f hf
  set k := Finset.univ.sup m with hk
  have hv : ∀ i, ∃ v ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R),
      v.IsHomogeneous (n + k) ∧ X i ^ k * f - v ∈ L (e + 1) := by
    intro i
    obtain ⟨c, hc⟩ : ∃ c, k = m i + c :=
      Nat.exists_eq_add_of_le (Finset.le_sup (f := m) (Finset.mem_univ i))
    have hmem : X i ^ k * f ∈
        L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
      have h := Ideal.mul_mem_left _ (X i ^ c) (hm i)
      convert h using 1
      rw [hc, pow_add]
      ring
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hmem
    have hXf : (X i ^ k * f).IsHomogeneous (n + k) := by
      rw [add_comm n k]
      exact (MvPolynomial.isHomogeneous_X_pow i k).mul hfh
    refine ⟨homogeneousComponent (n + k) w,
      GlobalTheory.CompanionTheory.GE.Lift.homogIdeal_map (I ^ (e + 1)) (n + k) w hw,
      MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩
    have hfix : homogeneousComponent (n + k) (X i ^ k * f) = X i ^ k * f := by
      rw [MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.mem_homogeneousSubmodule _ _).2 hXf), if_pos rfl]
    rw [← hfix, ← map_sub, ← huw, add_sub_cancel_right]
    exact hhom (e + 1) (n + k) u hu
  choose v hvI hvh hvL using hv
  choose τ hτ using fun i => GlobalTheory.CompanionTheory.GE.Lift.exists_lift (e + 1) (v i) (hvI i)
  obtain ⟨g, hg, hgm⟩ := hn₀ n hn k τ
    (fun i => GlobalTheory.CompanionTheory.GE.Lift.lift_isHomogeneous (hτ i) (hvh i)) (by
      intro i j
      refine ⟨0, ?_⟩
      rw [pow_zero, one_mul, GlobalTheory.CompanionTheory.GE.Lift.mem_reesIdeal]
      intro d
      rw [GlobalTheory.CompanionTheory.GE.Lift.phi_sub, GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul, GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul,
        GlobalTheory.CompanionTheory.GE.Lift.phi_lift (hτ i), GlobalTheory.CompanionTheory.GE.Lift.phi_lift (hτ j)]
      split_ifs with hd
      · subst hd
        have h := sub_mem (Ideal.mul_mem_left _ (X i ^ k) (hvL j))
          (Ideal.mul_mem_left _ (X j ^ k) (hvL i))
        convert h using 1
        ring
      · simp)
  refine ⟨f - GlobalTheory.CompanionTheory.GE.Lift.phi I N (e + 1) g, ?_,
    hfh.sub (GlobalTheory.CompanionTheory.GE.Lift.phi_isHomogeneous (e + 1) n hg), ?_⟩
  · apply hsat (e + 1)
    intro i
    obtain ⟨p, hp⟩ := hgm i
    refine ⟨p + k, ?_⟩
    have h1 := GlobalTheory.CompanionTheory.GE.Lift.mem_reesIdeal.1 hp (e + 1)
    rw [GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul, GlobalTheory.CompanionTheory.GE.Lift.phi_sub, GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul,
      GlobalTheory.CompanionTheory.GE.Lift.phi_lift (hτ i), if_pos rfl] at h1
    have h := sub_mem (Ideal.mul_mem_left _ (X i ^ p) (hvL i)) h1
    convert h using 1
    ring
  · rw [sub_sub_cancel]
    exact GlobalTheory.CompanionTheory.GE.Lift.phi_mem_map (e + 1) g

end GlobalTheory.CompanionTheory.GE.Lift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_filtration_saturated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ L e) → f ∈ L e) →
    (∀ e, ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ n₀ : ℕ, ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.Lift.uniform_lift
end

section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
open GlobalTheory.ProjSpace

namespace GlobalTheory.CompanionTheory.GE.Family

variable {R : Type} [CommRing R] {N : ℕ}

instance isClosedImmersion_thickι (I : Ideal R) (e : ℕ) : IsClosedImmersion (thickι R I N e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold thickι
  infer_instance

theorem thickMap_comp_thickι (I : Ideal R) (e : ℕ) :
    thickMap R I e (PO R N) ≫ thickι R I N (e + 1) = thickι R I N e := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

instance isClosedImmersion_thickMap (I : Ideal R) (e : ℕ) :
    IsClosedImmersion (thickMap R I e (PO R N)) := by
  have : IsClosedImmersion (thickMap R I e (PO R N) ≫ thickι R I N (e + 1)) := by
    rw [thickMap_comp_thickι]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (thickι R I N (e + 1))

theorem formOn_X_pow_mul (k : Fin (N + 1)) {m n : ℕ} {f : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)) :
    formOn (chart R N k) k le_rfl (m + n) (X k ^ m * f) h = formOn (chart R N k) k le_rfl n f hf := by
  simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self, one_pow, one_mul]

theorem killsForm_of_X_pow_mul {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) {n : ℕ}
    {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n)
    (h : ∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal φ) : KillsForm φ n f hf := by
  intro k
  obtain ⟨m, hm⟩ := h k
  have hh : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n) :=
    (isHomogeneous_X_pow k m).mul hf
  have := (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ (m + n) _ hh).1 hm k
  rwa [formOn_X_pow_mul k hf hh] at this

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem homogeneousComponent_X_pow_mul (k : Fin (N + 1)) (m d : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) :
    homogeneousComponent (m + d) (X k ^ m * f) = X k ^ m * homogeneousComponent d f := by
  have := DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (Fin (N + 1)) R)
    (a := X k ^ m) (b := f) (i := m) (j := d) (isHomogeneous_X_pow k m)
  have h2 : ∀ (g : MvPolynomial (Fin (N + 1)) R) (d : ℕ),
      ((DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) g) d :
        MvPolynomial (Fin (N + 1)) R) = homogeneousComponent d g :=
    fun g d => decomposition.decompose'_apply g d
  rwa [h2, h2] at this

theorem mem_vanIdeal_of_X_pow_mul {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)
    (f : MvPolynomial (Fin (N + 1)) R) (h : ∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal φ) :
    f ∈ vanIdeal φ := by
  rw [← sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun d _ => ?_
  refine (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ d _ (homogeneousComponent_isHomogeneous d f)).2
    (killsForm_of_X_pow_mul φ _ fun k => ?_)
  obtain ⟨m, hm⟩ := h k
  exact ⟨m, homogeneousComponent_X_pow_mul k m d f ▸ vanIdeal_homog φ (m + d) _ hm⟩

theorem killsForm_comp {Y Z : Scheme.{0}} (g : Z ⟶ Y) (φ : Y ⟶ PSpace R N) {n : ℕ}
    {f : MvPolynomial (Fin (N + 1)) R} {hf : f.IsHomogeneous n} (h : KillsForm φ n f hf) :
    KillsForm (g ≫ φ) n f hf := by
  intro k
  have := h k
  rw [Scheme.Hom.comp_app]
  change (g.app _).hom ((φ.app _).hom _) = 0
  rw [this, map_zero]

theorem vanIdeal_le_comp {Y Z : Scheme.{0}} (g : Z ⟶ Y) (φ : Y ⟶ PSpace R N) :
    vanIdeal φ ≤ vanIdeal (g ≫ φ) :=
  Ideal.span_mono fun _ ⟨n, hf, h⟩ => ⟨n, hf, killsForm_comp g φ h⟩

theorem map_pow_le_vanIdeal {Y : Scheme.{0}} (I : Ideal R) (e : ℕ)
    (a : Y ⟶ (thickObj R I e (PO R N)).left) :
    (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ vanIdeal (a ≫ thickι R I N e) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  refine (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm _ 0 (C r) (isHomogeneous_C _ r)).2 (killsForm_comp a _ fun k => ?_)
  have h := (GlobalTheory.CompanionTheory.GE.ker_thickι_chart I N e k).2 0 (C r) (isHomogeneous_C _ r) (Ideal.mem_map_of_mem _ hr)
  rw [Scheme.Hom.ker_apply] at h
  exact h

theorem exists_X_pow_mul_mem {Y Z : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ]
    (ψ : Z ⟶ PSpace R N) [QuasiCompact ψ] (I : Ideal R) (e : ℕ)
    (hker : Scheme.Hom.ker ψ = Scheme.Hom.ker φ ⊔ Scheme.Hom.ker (thickι R I N e))
    {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R} {hf : f.IsHomogeneous n}
    (hK : KillsForm ψ n f hf) (k : Fin (N + 1)) :
    ∃ m : ℕ, X k ^ m * f ∈ vanIdeal φ ⊔
      (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  have h1 : formOn (chart R N k) k le_rfl n f hf ∈
      (Scheme.Hom.ker ψ).ideal ⟨chart R N k, isAffineOpen_chart R N k⟩ := by
    rw [Scheme.Hom.ker_apply]
    exact hK k
  rw [hker, Scheme.IdealSheafData.ideal_sup] at h1
  obtain ⟨s, hs, s', hs', hss⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, t, ht, htm, rfl⟩ := (GlobalTheory.CompanionTheory.GE.ker_thickι_chart I N e k).1 s' hs'
  obtain ⟨a, b, hb, rfl⟩ := GlobalTheory.ProjSpace.Model.exists_formOn k s
  rw [Scheme.Hom.ker_apply] at hs
  obtain ⟨m, hm, hkill⟩ := GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul φ a b hb k hs
  have hmem : X k ^ m * b ∈ vanIdeal φ := (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ _ _ hm).2 hkill
  have key : X k ^ (a + c) * f = X k ^ (n + c) * b + X k ^ (n + a) * t := by
    have hL : (X k ^ (a + c) * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (a + c + n) :=
      (isHomogeneous_X_pow k _).mul hf
    have hR : (X k ^ (n + c) * b + X k ^ (n + a) * t :
        MvPolynomial (Fin (N + 1)) R).IsHomogeneous (a + c + n) := by
      refine IsHomogeneous.add ?_ ?_
      · have := (isHomogeneous_X_pow (R := R) k (n + c)).mul hb
        rwa [show n + c + a = a + c + n by ring] at this
      · have := (isHomogeneous_X_pow (R := R) k (n + a)).mul ht
        rwa [show n + a + c = a + c + n by ring] at this
    refine (formOn_chart_inj R N k hL hR).1 ?_
    simp only [formOn_eq_aeval, map_add, map_mul, map_pow, aeval_X, ratioOn_self, one_pow,
      one_mul] at hss ⊢
    exact hss.symm
  refine ⟨m + a + c, ?_⟩
  have e1 : X k ^ (m + a + c) * f =
      X k ^ (n + c) * (X k ^ m * b) + X k ^ (m + n + a) * t := by
    have : X k ^ (m + a + c) * f = X k ^ m * (X k ^ (a + c) * f) := by ring
    rw [this, key]; ring
  rw [e1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hmem))
    (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right htm))

theorem vanIdeal_family : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤
        vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal (i e ≫ thickι R I N e)) →
        f ∈ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ≤ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
        vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔
          (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) := by
  intro R _ _ I N Cs i β hi hβ
  have hcomp : ∀ e, i e ≫ thickι R I N e =
      β e ≫ i (e + 1) ≫ thickι R I N (e + 1) := fun e => by
    rw [← thickMap_comp_thickι I e, ← Category.assoc, ← Category.assoc, (hβ e).w]
  refine ⟨fun e => map_pow_le_vanIdeal I e (i e), fun e f h => mem_vanIdeal_of_X_pow_mul _ f h,
    fun e => ?_, fun e f hf k => ?_⟩
  · rw [hcomp e]
    exact vanIdeal_le_comp _ _
  · have hker : Scheme.Hom.ker (i e ≫ thickι R I N e) =
        Scheme.Hom.ker (i (e + 1) ≫ thickι R I N (e + 1)) ⊔ Scheme.Hom.ker (thickι R I N e) := by
      have := GlobalTheory.CompanionTheory.GE.ker_inter_eq_sup (thickι R I N (e + 1)) (i (e + 1)) (thickMap R I e (PO R N))
        (β e) (i e) (hβ e)
      rwa [thickMap_comp_thickι, Category.assoc, ← hcomp e] at this
    refine Submodule.span_induction (p := fun f _ => ∃ m : ℕ, X k ^ m * f ∈
        vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔
          (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ?_ ?_ ?_ ?_ hf
    · rintro x ⟨n, hx, hK⟩
      exact exists_X_pow_mul_mem _ _ I e hker hK k
    · exact ⟨0, by simp⟩
    · rintro x y _ _ ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      have e1 : X k ^ (a + b) * (x + y) = X k ^ b * (X k ^ a * x) + X k ^ a * (X k ^ b * y) := by
        ring
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
    · rintro a x _ ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hm

end GlobalTheory.CompanionTheory.GE.Family
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_vanishing_ideal_system : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤
        vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal (i e ≫ thickι R I N e)) →
        f ∈ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ≤ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
        vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔
          (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_pullback_of_kernel_sup : ∀ {X A B Z : Scheme.{0}} (a : A ⟶ X) (b : B ⟶ X) (f : Z ⟶ A) (g : Z ⟶ B)
    [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion (f ≫ a)], f ≫ a = g ≫ b →
    Scheme.Hom.ker (f ≫ a) = Scheme.Hom.ker a ⊔ Scheme.Hom.ker b → IsPullback f g a b := by
  first | exact @GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | exact GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | (intros; apply GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup <;> assumption)
end

section
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GE

variable {R : Type} [CommRing R] {N : ℕ}

theorem exists_eq_formOn (k : Fin (N + 1)) (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    ∃ (n : ℕ) (a : MvPolynomial (Fin (N + 1)) R) (ha : a.IsHomogeneous n),
      s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n a ha := by
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway (GlobalTheory.ProjSpace.grading R N) (X k) (GlobalTheory.ProjSpace.X_mem R N k) one_pos).hom).2 s
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (GlobalTheory.ProjSpace.X_mem R N k) x
  have hf' : f.IsHomogeneous n := by simpa using hf
  refine ⟨n, f, hf', ?_⟩
  exact (GlobalTheory.ProjFrac.awayToSection_mk _ _ _).trans (GlobalTheory.ProjFrac.frac_eq rfl)

theorem homogeneousComponent_mem_map_C {K : Ideal R} {d : ℕ} {v : MvPolynomial (Fin (N + 1)) R}
    (hv : v ∈ K.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    homogeneousComponent d v ∈ K.map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  rw [mem_map_C_iff] at hv ⊢
  intro m
  rw [coeff_homogeneousComponent]
  split_ifs
  · exact hv m
  · exact zero_mem _

def homogOf (J : Ideal (MvPolynomial (Fin (N + 1)) R)) (hJ : HomogIdeal J) :
    HomogeneousIdeal (GlobalTheory.ProjSpace.grading R N) :=
  ⟨J, fun d f hf => by
    have := hJ d f hf
    rwa [← decomposition.decompose'_apply f d] at this⟩

theorem ker_le_sup_chart {Y : Scheme.{0}} (I : Ideal R) (e : ℕ)
    (J : Ideal (MvPolynomial (Fin (N + 1)) R)) (hJ : HomogIdeal J)
    (φ : Y ⟶ PSpace R N) [QuasiCompact φ]
    (hge : ∀ f ∈ vanIdeal φ, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (k : Fin (N + 1)) :
    (Scheme.Hom.ker φ).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ≤
      (Scheme.Hom.ker (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ))).ideal
          ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ⊔
        (Scheme.Hom.ker (thickι R I N e)).ideal
          ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ := by
  intro s hs
  obtain ⟨n, a, ha, rfl⟩ := exists_eq_formOn k s
  rw [Scheme.Hom.ker_apply] at hs
  obtain ⟨m, h, hK⟩ := GlobalTheory.T.chart_vanishing_kills_form_mul_pow φ n a ha k hs
  obtain ⟨m', hm'⟩ := hge _ ((GlobalTheory.T.mem_vanishing_ideal_iff_kills_form φ _ _ h).2 hK) k
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hm'
  have hb : (X k ^ m' * (X k ^ m * a) : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m' + (m + n)) :=
    (isHomogeneous_X_pow k m').mul h
  have hcu := homogeneousComponent_isHomogeneous (m' + (m + n)) u
  have hcv := homogeneousComponent_isHomogeneous (m' + (m + n)) v
  have hsum : homogeneousComponent (m' + (m + n)) u + homogeneousComponent (m' + (m + n)) v =
      X k ^ m' * (X k ^ m * a) := by
    rw [← map_add, huv, homogeneousComponent_of_mem hb, if_pos rfl]
  have e1 : GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n a ha =
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl (m' + (m + n)) _ (hcu.add hcv) :=
    GlobalTheory.ProjFrac.frac_eq (by rw [hsum]; ring)
  rw [e1, GlobalTheory.ProjSpace.formOn_add hcu hcv]
  refine Submodule.add_mem_sup ?_ ?_
  · rw [Scheme.Hom.ker_apply]
    exact (GlobalTheory.ProjSpace.vPlusι_app_formOn_eq_zero_iff (homogOf J hJ) k hcu).2
      ⟨0, by rw [pow_zero, one_mul]; exact hJ _ _ hu⟩
  · exact (GlobalTheory.T.thickening_section_homogeneous_form I N e k).2 _ _ hcv (homogeneousComponent_mem_map_C hv)

instance isClosedImmersion_thickι (I : Ideal R) (e : ℕ) : IsClosedImmersion (thickι R I N e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem thickMap_thickι (I : Ideal R) (e : ℕ) :
    thickMap R I e (PO R N) ≫ thickι R I N (e + 1) = thickι R I N e :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem exists_closed_of_homogIdeal : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    ∀ (J : Ideal (MvPolynomial (Fin (N + 1)) R)), HomogIdeal J →
    (∀ e, J ≤ vanIdeal (i e ≫ thickι R I N e)) →
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ (PO R N).left) (b : ∀ e, Cs e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst (PO R N).hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e := by
  intro R _ _ I N Cs i β hi hsq J hJ hle hge
  have hcl : ∀ e, IsClosedImmersion (i e ≫ thickι R I N e) := fun e => by
    have := hi e
    infer_instance
  have hfac : ∀ e, ∃ ψ : Cs e ⟶ GlobalTheory.ProjSpace.VPlus (homogOf J hJ),
      ψ ≫ GlobalTheory.ProjSpace.vPlusι (homogOf J hJ) = i e ≫ thickι R I N e := fun e =>
    (GlobalTheory.ProjSpace.exists_comp_vPlusι_iff (homogOf J hJ) _).2 fun k n f hf hfJ =>
      (GlobalTheory.T.mem_vanishing_ideal_iff_kills_form _ n f hf).1 (hle e hfJ) k
  choose b hb using hfac
  refine ⟨GlobalTheory.ProjSpace.VPlus (homogOf J hJ), GlobalTheory.ProjSpace.vPlusι (homogOf J hJ), b, inferInstance,
    fun e => ?_, fun e => ?_⟩
  · have hc : IsClosedImmersion (b e ≫ GlobalTheory.ProjSpace.vPlusι (homogOf J hJ)) := by
      rw [hb]
      exact hcl e
    refine GlobalTheory.T.is_pullback_of_kernel_sup _ _ _ _ (hb e) ?_
    rw [hb]
    have := hcl e
    have h1 : Scheme.Hom.ker (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ)) ≤
        Scheme.Hom.ker (i e ≫ thickι R I N e) := by
      rw [← hb e]
      exact Scheme.Hom.le_ker_comp _ _
    have h2 : Scheme.Hom.ker (thickι R I N e) ≤ Scheme.Hom.ker (i e ≫ thickι R I N e) :=
      Scheme.Hom.le_ker_comp _ _
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun k => ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩)
      (GlobalTheory.ProjSpace.iSup_chart R N) fun k => le_antisymm ?_ ?_
    · exact ker_le_sup_chart I e J hJ _ (hge e) k
    · exact (Scheme.IdealSheafData.le_def.1 (sup_le h1 h2)) _
  · refine (cancel_mono (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ))).1 ?_
    rw [Category.assoc, hb, hb, ← Category.assoc, (hsq e).w, Category.assoc, thickMap_thickι]

end GlobalTheory.CompanionTheory.GE
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_le_thickening : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    ∀ (J : Ideal (MvPolynomial (Fin (N + 1)) R)), HomogIdeal J →
    (∀ e, J ≤ vanIdeal (i e ≫ thickι R I N e)) →
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ (PO R N).left) (b : ∀ e, Cs e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst (PO R N).hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.GE

theorem geClosedProj : GEClosedProj := by
  intro R _ _ I hI N P Cs i β hi hβ
  obtain ⟨hbase, hsat, hanti, hcompat⟩ := GlobalTheory.T.thickening_vanishing_ideal_system R I N Cs i β hi hβ
  obtain ⟨n₀, hlift⟩ := GlobalTheory.T.homogeneous_ideal_filtration_saturated R I N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hsat hcompat
  obtain ⟨J, hJ, h⟩ := GlobalTheory.T.homogeneous_lift_adic_filtration R I hI N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hanti n₀ hlift
  exact GlobalTheory.T.homogeneous_ideal_le_thickening R I N Cs i β hi hβ J hJ (fun e => (h e).1) (fun e => (h e).2)

end GlobalTheory.CompanionTheory.GE
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieck_existence_closed_proj : GEClosedProj := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.geClosedProj
end
