import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostGaloisCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRoots
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivativeCyclotomicMul

section
section
noncomputable section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.TraceTower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem eq_on_fix {T : Tower p Ω} {r : Ω} {h h' : Gal p Ω} (hh : h ∈ Hinf T) (hh' : h' ∈ Hinf T)
    (e : h r = h' r) {x : Ω} (hx : x ∈ FixI (Hfix T r)) : h x = h' x := by
  have hm : h'⁻¹ * h ∈ Hfix T r := by
    refine ⟨(Hinf T).mul_mem ((Hinf T).inv_mem hh') hh, ?_⟩
    refine MulAction.mem_stabilizer_iff.2 ?_
    rw [AlgEquiv.smul_def, AlgEquiv.mul_apply, e]
    exact h'.symm_apply_apply r
  have h1 : h'.symm (h x) = x := hx.2 _ hm
  exact h'.symm_apply_eq.1 h1

end GlobalTheory.TraceTower

open GlobalTheory.TraceTower in
theorem GlobalTheory.traceTower_dualData : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt p r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ (ι : Type) [Fintype ι] (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) → (∀ k, v k ∈ FixI (Hfix T r)) →
  ∑ k, u k * v k = (p : Ω) → (∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0) →
  ∃ tr : Ω → Ω, DualData (FixI (Hinf T)) (FixI (Hfix T r)) u v tr := by
  intro p _ Ω _ _ T n r _ hor ι _ u v hu hv huv hz
  classical
  have hfin : {ρ : Ω | ∃ h ∈ Hinf T, h r = ρ}.Finite := by
    refine ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).finite_toSet.subset ?_
    rintro ρ ⟨h, hh, rfl⟩
    obtain ⟨i, hi⟩ := hor h hh
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨i % p ^ n, Nat.mod_lt _ (ppow_pos n), ?_⟩
    rw [hi]
    congr 1
    conv_rhs => rw [← Nat.div_add_mod i (p ^ n)]
    rw [pow_add, pow_mul, (T.prim n).pow_eq_one, one_pow, one_mul]
  set O := hfin.toFinset with hOdef
  have hO : ∀ ρ, ρ ∈ O ↔ ∃ h ∈ Hinf T, h r = ρ := fun ρ => hfin.mem_toFinset
  have hg0 : ∀ ρ, ∃ f : Gal p Ω, ρ ∈ O → f ∈ Hinf T ∧ f r = ρ := by
    intro ρ
    by_cases hρ : ρ ∈ O
    · obtain ⟨h, hh, e⟩ := (hO ρ).1 hρ
      exact ⟨h, fun _ => ⟨hh, e⟩⟩
    · exact ⟨1, fun h => absurd h hρ⟩
  choose g hg using hg0
  have hrO : r ∈ O := (hO r).2 ⟨1, (Hinf T).one_mem, rfl⟩
  have fixr : ∀ x ∈ FixI (Hfix T r), g r x = x := fun x hx =>
    hx.2 _ ⟨(hg r hrO).1, MulAction.mem_stabilizer_iff.2 (by rw [AlgEquiv.smul_def]; exact (hg r hrO).2)⟩
  have kk : ∀ f ∈ Hinf T, ∀ ρ ∈ O, ∀ x ∈ FixI (Hfix T r), f (g ρ x) = g (f ρ) x ∧ f ρ ∈ O := by
    intro f hf ρ hρ x hx
    have hm : f * g ρ ∈ Hinf T := (Hinf T).mul_mem hf (hg ρ hρ).1
    have hr' : (f * g ρ) r = f ρ := by rw [AlgEquiv.mul_apply, (hg ρ hρ).2]
    have hfO : f ρ ∈ O := (hO _).2 ⟨_, hm, hr'⟩
    refine ⟨?_, hfO⟩
    have := eq_on_fix hm (hg _ hfO).1 (by rw [hr', (hg _ hfO).2]) hx
    rwa [AlgEquiv.mul_apply] at this
  have zero_inv : ∀ ρ ∈ O, ρ ≠ r → ∑ k, v k * g ρ (u k) = 0 := by
    intro ρ hρ hne
    set f := g ρ
    have hf : f ∈ Hinf T := (hg ρ hρ).1
    have hne' : f⁻¹ r ≠ r := by
      intro e
      apply hne
      rw [← (hg ρ hρ).2]
      have e' : f.symm r = r := e
      conv_lhs => rw [← e']
      exact f.apply_symm_apply r
    have h0 := hz _ ((Hinf T).inv_mem hf) hne'
    calc ∑ k, v k * f (u k) = f (∑ k, u k * f⁻¹ (v k)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
          have : f (f⁻¹ (v k)) = v k := f.apply_symm_apply (v k)
          rw [this, mul_comm]
      _ = 0 := by rw [h0, map_zero]
  refine ⟨fun x => ∑ ρ ∈ O, g ρ x, fun x hx => ⟨hx.1, fun f hf => hx.2 f hf.1⟩, fun x hx => hx.1,
    hu, hv, ?_, ?_, ?_, ?_, ?_, huv⟩
  · intro x hx
    refine ⟨int_sum _ _ fun ρ _ => int_gal _ hx.1, fun f hf => ?_⟩
    show f (∑ ρ ∈ O, g ρ x) = ∑ ρ ∈ O, g ρ x
    rw [map_sum]
    calc ∑ ρ ∈ O, f (g ρ x) = ∑ ρ ∈ O, g (f ρ) x :=
          Finset.sum_congr rfl fun ρ hρ => (kk f hf ρ hρ x hx).1
      _ = ∑ ρ ∈ O, g ρ x := by
        refine Finset.sum_nbij' (fun ρ => f ρ) (fun ρ => f.symm ρ) (fun ρ hρ => (kk f hf ρ hρ x hx).2)
          (fun ρ hρ => (kk f⁻¹ ((Hinf T).inv_mem hf) ρ hρ x hx).2) (fun ρ _ => f.symm_apply_apply ρ)
          (fun ρ _ => f.apply_symm_apply ρ) (fun ρ _ => rfl)
  · intro x _ y _
    simp only [map_add, Finset.sum_add_distrib]
  · intro b hb x _
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [map_mul, hb.2 _ (hg ρ hρ).1]
  · intro y hy
    calc ∑ k, u k * ∑ ρ ∈ O, g ρ (v k * y) = ∑ ρ ∈ O, g ρ y * ∑ k, u k * g ρ (v k) := by
          simp only [map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
      _ = g r y * ∑ k, u k * g r (v k) := by
          refine Finset.sum_eq_single r (fun ρ hρ hne => ?_) (fun h => absurd hrO h)
          rw [hz _ (hg ρ hρ).1 (by rw [(hg ρ hρ).2]; exact hne), mul_zero]
      _ = p * y := by
          rw [fixr y hy, Finset.sum_congr rfl fun k _ => by rw [fixr (v k) (hv k)], huv, mul_comm]
  · intro y hy
    calc ∑ k, v k * ∑ ρ ∈ O, g ρ (u k * y) = ∑ ρ ∈ O, g ρ y * ∑ k, v k * g ρ (u k) := by
          simp only [map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
      _ = g r y * ∑ k, v k * g r (u k) := by
          refine Finset.sum_eq_single r (fun ρ hρ hne => ?_) (fun h => absurd hrO h)
          rw [zero_inv ρ hρ hne, mul_zero]
      _ = p * y := by
          rw [fixr y hy, Finset.sum_congr rfl fun k _ => by rw [fixr (u k) (hu k)], ← huv,
            mul_comm]
          congr 1
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
end
end

open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceTower_almostDualBases_adjoin_kummer_root : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt p r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ (ι : Type) [Fintype ι] (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) → (∀ k, v k ∈ FixI (Hfix T r)) →
  ∑ k, u k * v k = (p : Ω) → (∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0) →
  ∃ tr : Ω → Ω, DualData (FixI (Hinf T)) (FixI (Hfix T r)) u v tr := by
  atlas_forward_decl GlobalTheory.traceTower_dualData
end

section
section
noncomputable section

namespace GlobalTheory.DerExt

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
variable {ι : Type} [Fintype ι]

def D0 (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * d (tr (v k * x))

def phi (D : Ω → Ω) (x y : Ω) : Ω := D (x * y) - x * D y - y * D x

def psi (u v : ι → Ω) (D : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * phi D (v k) x

theorem phi_comm (D : Ω → Ω) (x y : Ω) : phi D x y = phi D y x := by
  unfold phi; rw [mul_comm x y]; ring

theorem phi_one (D : Ω → Ω) (y : Ω) : phi D 1 y = -(y * D 1) := by
  unfold phi; simp

theorem phi_ident (D : Ω → Ω) (w x y : Ω) :
    w * phi D x y - phi D (w * x) y + phi D w (x * y) - y * phi D w x = 0 := by
  unfold phi; rw [show w * x * y = w * (x * y) by ring]; ring

variable {B C : Subalgebra (O0 p) Ω} {u v : ι → Ω} {tr : Ω → Ω} {d : Ω → Ω}

theorem traceDerivationFirstApprox_add_isInt (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt p (D0 u v tr d (x + y) - D0 u v tr d x - D0 u v tr d y) := by
  obtain ⟨_, hCi, hu, hv, htr, hadd, -⟩ := h
  refine int_congr (int_sum Finset.univ _ fun k _ => int_mul (hCi _ (hu k))
    (hd.1 _ (htr _ (C.mul_mem (hv k) hx)) _ (htr _ (C.mul_mem (hv k) hy)))) ?_
  simp only [D0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, hadd _ (C.mul_mem (hv k) hx) _ (C.mul_mem (hv k) hy)]; ring

theorem traceDerivationFirstApprox_mul_left_isInt (h : DualData B C u v tr) (hd : IsDer B d) {b x : Ω} (hb : b ∈ B) (hx : x ∈ C) :
    IsInt p (D0 u v tr d (b * x) - b * D0 u v tr d x - p * x * d b) := by
  obtain ⟨_, hCi, hu, hv, htr, -, hlin, hdual, -⟩ := h
  refine int_congr (int_sum Finset.univ _ fun k _ => int_mul (hCi _ (hu k))
    (hd.2.1 b hb _ (htr _ (C.mul_mem (hv k) hx)))) ?_
  rw [← hdual x hx]
  simp only [D0, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show v k * (b * x) = b * (v k * x) by ring, hlin b hb _ (C.mul_mem (hv k) hx)]; ring

theorem phi_add (h : DualData B C u v tr) (hd : IsDer B d) {x x' y : Ω} (hx : x ∈ C) (hx' : x' ∈ C)
    (hy : y ∈ C) :
    IsInt p (phi (D0 u v tr d) (x + x') y - phi (D0 u v tr d) x y - phi (D0 u v tr d) x' y) := by
  refine int_congr (int_sub (traceDerivationFirstApprox_add_isInt h hd (C.mul_mem hx hy) (C.mul_mem hx' hy))
    (int_mul (h.2.1 y hy) (traceDerivationFirstApprox_add_isInt h hd hx hx'))) ?_
  simp only [phi, add_mul]; ring

theorem phi_bmul (h : DualData B C u v tr) (hd : IsDer B d) {b x y : Ω} (hb : b ∈ B) (hx : x ∈ C)
    (hy : y ∈ C) :
    IsInt p (phi (D0 u v tr d) (b * x) y - b * phi (D0 u v tr d) x y) := by
  refine int_congr (int_sub (traceDerivationFirstApprox_mul_left_isInt h hd hb (C.mul_mem hx hy))
    (int_mul (h.2.1 y hy) (traceDerivationFirstApprox_mul_left_isInt h hd hb hx))) ?_
  simp only [phi]; rw [show b * x * y = b * (x * y) by ring]; ring

theorem lin_sum (h : DualData B C u v tr) (f : Ω → Ω)
    (hadd : ∀ x ∈ C, ∀ y ∈ C, IsInt p (f (x + y) - f x - f y))
    (hlin : ∀ b ∈ B, ∀ x ∈ C, IsInt p (f (b * x) - b * f x))
    {κ : Type} (s : Finset κ) (w b : κ → Ω) (hw : ∀ i, w i ∈ C) (hb : ∀ i, b i ∈ B) :
    IsInt p (f (∑ i ∈ s, w i * b i) - ∑ i ∈ s, b i * f (w i)) := by
  classical
  have hBC := h.1
  induction s using Finset.induction_on with
  | empty =>
    simpa using hlin 0 B.zero_mem 0 C.zero_mem
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS : ∑ i ∈ s, w i * b i ∈ C := C.sum_mem fun i _ => C.mul_mem (hw i) (hBC (hb i))
    have h1 := hadd _ (C.mul_mem (hw a) (hBC (hb a))) _ hS
    have h2 := hlin (b a) (hb a) (w a) (hw a)
    rw [mul_comm (b a) (w a)] at h2
    exact int_congr (int_add h1 (int_add h2 ih)) (by ring)

theorem sum_swap_eq (h : DualData B C u v tr) (D : Ω → Ω) {x : Ω} (hx : x ∈ C) (y : Ω) :
    ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y = p * x * psi u v D y := by
  obtain ⟨_, -, hu, -, -, -, -, hdual, -⟩ := h
  calc ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y
      = ∑ k, ∑ l, u k * tr (v k * (x * u l)) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show u l * (v k * x) = v k * (x * u l) by ring]; ring
    _ = ∑ l, ∑ k, u k * tr (v k * (x * u l)) * phi D (v l) y := Finset.sum_comm
    _ = ∑ l, (∑ k, u k * tr (v k * (x * u l))) * phi D (v l) y := by
        simp only [Finset.sum_mul]
    _ = ∑ l, p * (x * u l) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hdual _ (C.mul_mem hx (hu l))]
    _ = p * x * psi u v D y := by
        simp only [psi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem S_congr (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt p (p * ∑ k, u k * phi (D0 u v tr d) (v k * x) y - p * x * psi u v (D0 u v tr d) y) := by
  have hBC := h.1
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have htr := h.2.2.2.2.1
  have hdual2 := h.2.2.2.2.2.2.2.2.1
  have hpB : (p : Ω) ∈ B := natCast_mem B p
  have key : ∀ k, IsInt p (u k * (p * phi (D0 u v tr d) (v k * x) y -
      ∑ l, tr (u l * (v k * x)) * phi (D0 u v tr d) (v l) y)) := by
    intro k
    have hz : v k * x ∈ C := C.mul_mem (hv k) hx
    have ha := phi_bmul h hd hpB hz hy
    have hb := lin_sum h (fun z => phi (D0 u v tr d) z y)
      (fun a ha b hb => phi_add h hd ha hb hy) (fun b hb a ha => phi_bmul h hd hb ha hy)
      Finset.univ v (fun l => tr (u l * (v k * x))) hv
      (fun l => htr _ (C.mul_mem (hu l) hz))
    rw [hdual2 _ hz] at hb
    exact int_mul (hCi _ (hu k)) (int_congr (int_sub hb ha) (by ring))
  refine int_congr (int_sum Finset.univ _ fun k _ => key k) ?_
  rw [← sum_swap_eq h (D0 u v tr d) hx y, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

def Dext (p : ℕ) (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω :=
  (p : Ω) ^ 2 * D0 u v tr d x + p * psi u v (D0 u v tr d) x

theorem Dext_mul (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt p (Dext p u v tr d (x * y) - x * Dext p u v tr d y - y * Dext p u v tr d x) := by
  have hsum := h.2.2.2.2.2.2.2.2.2
  have hid : (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
      psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x = 0 := by
    calc (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
          psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x
        = ∑ k, u k * (v k * phi (D0 u v tr d) x y - phi (D0 u v tr d) (v k * x) y +
            phi (D0 u v tr d) (v k) (x * y) - y * phi (D0 u v tr d) (v k) x) := by
          rw [← hsum]
          simp only [psi, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by simp [phi_ident]
  refine int_congr (S_congr h hd hx hy) ?_
  simp only [Dext, phi, psi] at hid ⊢
  linear_combination (p : Ω) * hid

theorem Dext_add (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt p (Dext p u v tr d (x + y) - Dext p u v tr d x - Dext p u v tr d y) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have h1 := traceDerivationFirstApprox_add_isInt h hd hx hy
  have h2 : IsInt p (∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
      phi (D0 u v tr d) y (v k))) :=
    int_sum Finset.univ _ fun k _ => int_mul (hCi _ (hu k)) (phi_add h hd hx hy (hv k))
  refine int_congr (int_add (int_mul (int_pow (int_nat p) 2) h1) (int_mul (int_nat p) h2)) ?_
  have e : psi u v (D0 u v tr d) (x + y) - psi u v (D0 u v tr d) x - psi u v (D0 u v tr d) y =
      ∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
        phi (D0 u v tr d) y (v k)) := by
    simp only [psi, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) (x + y), phi_comm _ (v k) x, phi_comm _ (v k) y]; ring
  simp only [Dext]
  linear_combination (p : Ω) * e

theorem Dext_B (h : DualData B C u v tr) (hd : IsDer B d) {b : Ω} (hb : b ∈ B) :
    IsInt p (Dext p u v tr d b - (p : Ω) ^ 3 * d b) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have hsum := h.2.2.2.2.2.2.2.2.2
  have h1 := traceDerivationFirstApprox_mul_left_isInt h hd hb C.one_mem
  rw [mul_one, mul_one] at h1
  have h2 : IsInt p (psi u v (D0 u v tr d) b + p * b * D0 u v tr d 1) := by
    refine int_congr (int_sum Finset.univ _ fun k _ => int_mul (hCi _ (hu k))
      (phi_bmul h hd hb C.one_mem (hv k))) ?_
    rw [← hsum]
    simp only [psi, phi_one, mul_one, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) b]; ring
  refine int_congr (int_add (int_mul (int_pow (int_nat p) 2) h1) (int_mul (int_nat p) h2)) ?_
  simp only [Dext]; ring

theorem Dext_isDer (h : DualData B C u v tr) (hd : IsDer B d) : IsDer C (Dext p u v tr d) :=
  ⟨fun x hx y hy => Dext_add h hd hx hy, fun x hx y hy => Dext_mul h hd hx hy,
   fun c => int_congr (int_add (Dext_B h hd (B.algebraMap_mem c))
     (int_mul (int_pow (int_nat p) 3) (hd.2.2 c))) (by ring)⟩

theorem exists_ext : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω),
    DualData B C u v tr →
    ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt p (D b - (p : Ω) ^ 3 * d b) := by
  intro p _ Ω _ _ B C ι _ u v tr h d hd
  exact ⟨Dext p u v tr d, Dext_isDer h hd, fun b hb => Dext_B h hd hb⟩

end GlobalTheory.DerExt
end
end

open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivationModIntegral_extension_p_cube : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt p (D b - (p : Ω) ^ 3 * d b) := by
  atlas_forward_decl GlobalTheory.DerExt.exists_ext
end

section
section
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumDlog

theorem der_dual_p_sq_int : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω),
    DualData B C u v tr →
  ∀ D : Ω → Ω, IsDer C D → ∀ x ∈ C, (∀ k l, IsInt p (D (tr (u l * (x * v k))))) →
    IsInt p ((p : Ω) ^ 2 * D x) := by
  intro p _ Ω _ _ B C ι _ u v tr hd D hD x hx hT
  obtain ⟨hBC, hCi, hu, hv, htr, -, -, hsu, hsv, huv⟩ := hd
  have s1 : ∀ k, IsInt p ((p : Ω) * D (x * v k) - ∑ l, tr (u l * (x * v k)) * D (v l)) := by
    intro k
    have hy : x * v k ∈ C := mul_mem hx (hv k)
    have a1 := hD.alg_mul hCi (p : O0 p) hy
    simp only [map_natCast] at a1
    rw [← hsv _ hy] at a1
    have a2 := hD.sum Finset.univ (fun l => v l * tr (u l * (x * v k)))
      (fun l _ => mul_mem (hv l) (hBC (htr _ (mul_mem (hu l) hy))))
    have a3 : IsInt p (∑ l, D (v l * tr (u l * (x * v k))) -
        ∑ l, tr (u l * (x * v k)) * D (v l)) := by
      rw [← Finset.sum_sub_distrib]
      refine int_sum _ _ fun l _ => ?_
      have ht : tr (u l * (x * v k)) ∈ C := hBC (htr _ (mul_mem (hu l) hy))
      exact int_congr (int_add (hD.2.1 _ (hv l) _ ht) (int_mul (hCi _ (hv l)) (hT k l))) (by ring)
    exact int_congr (int_add (int_add (int_neg a1) a2) a3) (by ring)
  have e2 : ∀ l, ∑ k, u k * (tr (u l * (x * v k)) * D (v l)) = (p : Ω) * (x * (u l * D (v l))) := by
    intro l
    have h := hsu (x * u l) (mul_mem hx (hu l))
    calc ∑ k, u k * (tr (u l * (x * v k)) * D (v l))
        = (∑ k, u k * tr (v k * (x * u l))) * D (v l) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show u l * (x * v k) = v k * (x * u l) by ring]; ring
      _ = _ := by rw [h]; ring
  have e : ∑ k, u k * ∑ l, tr (u l * (x * v k)) * D (v l) = (p : Ω) * (x * ∑ l, u l * D (v l)) := by
    calc _ = ∑ l, ∑ k, u k * (tr (u l * (x * v k)) * D (v l)) := by
            simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      _ = ∑ l, (p : Ω) * (x * (u l * D (v l))) := Finset.sum_congr rfl fun l _ => e2 l
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have s2 : IsInt p ((p : Ω) * ∑ k, u k * D (x * v k) - (p : Ω) * (x * ∑ l, u l * D (v l))) := by
    have a : IsInt p (∑ k, u k * ((p : Ω) * D (x * v k) - ∑ l, tr (u l * (x * v k)) * D (v l))) :=
      int_sum _ _ fun k _ => int_mul (hCi _ (hu k)) (s1 k)
    refine int_congr a ?_
    rw [← e, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have s3 : IsInt p (∑ k, u k * D (x * v k) - x * ∑ k, u k * D (v k) - (p : Ω) * D x) := by
    have a : IsInt p (∑ k, u k * (D (x * v k) - x * D (v k) - v k * D x)) :=
      int_sum _ _ fun k _ => int_mul (hCi _ (hu k)) (hD.2.1 x hx (v k) (hv k))
    refine int_congr a ?_
    rw [← huv, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact int_congr (int_sub s2 (int_mul (int_nat p) s3)) (by ring)

end GlobalTheory.KumDlog
end

open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationModIntegral_almostDual_p_sq_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ D : Ω → Ω, IsDer C D → ∀ x ∈ C, (∀ k l, IsInt p (D (tr (u l * (x * v k))))) → IsInt p ((p : Ω) ^ 2 * D x) := by
  atlas_forward_decl GlobalTheory.KumDlog.der_dual_p_sq_int
end

section
section
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.FixFrac

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def fracField (T : Tower p Ω) : Subfield Ω where
  carrier := {x | ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b}
  zero_mem' := ⟨0, 0, zero_mem _, 1, one_mem _, one_ne_zero, by simp⟩
  one_mem' := ⟨0, 1, one_mem _, 1, one_mem _, one_ne_zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, a, ha, b, hb, hb0, rfl⟩ ⟨m', c, hc, d, hd, hd0, rfl⟩
    have h1 := Lev_mono T (le_max_left m m')
    have h2 := Lev_mono T (le_max_right m m')
    refine ⟨max m m', a * d + b * c, add_mem (mul_mem (h1 ha) (h2 hd)) (mul_mem (h1 hb) (h2 hc)),
      b * d, mul_mem (h1 hb) (h2 hd), mul_ne_zero hb0 hd0, ?_⟩
    rw [div_add_div _ _ hb0 hd0]
  mul_mem' := by
    rintro _ _ ⟨m, a, ha, b, hb, hb0, rfl⟩ ⟨m', c, hc, d, hd, hd0, rfl⟩
    have h1 := Lev_mono T (le_max_left m m')
    have h2 := Lev_mono T (le_max_right m m')
    exact ⟨max m m', a * c, mul_mem (h1 ha) (h2 hc), b * d, mul_mem (h1 hb) (h2 hd),
      mul_ne_zero hb0 hd0, div_mul_div_comm a b c d⟩
  neg_mem' := by
    rintro _ ⟨m, a, ha, b, hb, hb0, rfl⟩
    exact ⟨m, -a, neg_mem ha, b, hb, hb0, (neg_div b a).symm⟩
  inv_mem' := by
    rintro _ ⟨m, a, ha, b, hb, hb0, rfl⟩
    by_cases ha0 : a = 0
    · exact ⟨0, 0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [ha0]⟩
    · exact ⟨m, b, hb, a, ha, ha0, inv_div a b⟩

theorem mem_fracField_of_mem (T : Tower p Ω) {m : ℕ} {a : Ω} (ha : a ∈ Lev T m) :
    a ∈ fracField T :=
  ⟨m, a, ha, 1, one_mem _, one_ne_zero, (div_one a).symm⟩

theorem fixed_eq_div : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (x : Ω), (∀ h ∈ Hinf T, h x = x) →
    ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b := by
  intro p _ Ω _ _ hC T x hx
  haveI : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hC.inj
  letI : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hC.alg
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  haveI : IsAlgClosed Ω := hC.clo
  haveI : IsAlgClosure (FractionRing (O0 p)) Ω := ⟨hC.clo, inferInstance⟩
  haveI : CharZero Ω := Basic.charZero_of_isClo hC
  haveI : CharZero (FractionRing (O0 p)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  haveI : IsGalois (FractionRing (O0 p)) Ω := IsAlgClosure.isGalois _ _
  let E := IntermediateField.adjoin (FractionRing (O0 p)) (Set.range T.ζ ∪ Set.range T.qq)
  have hxE : x ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hfix : ∀ y ∈ E, σ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ
    have hmem : σ.restrictScalars (O0 p) ∈ Hinf T := by
      rw [mem_Hinf]
      intro n
      exact ⟨hfix _ (IntermediateField.subset_adjoin _ _ (Or.inl ⟨n, rfl⟩)),
        hfix _ (IntermediateField.subset_adjoin _ _ (Or.inr ⟨n, rfl⟩))⟩
    exact hx _ hmem
  have halg : ∀ c : FractionRing (O0 p), algebraMap (FractionRing (O0 p)) Ω c ∈ fracField T := by
    intro c
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (O0 p)) c
    dsimp only
    rw [IsFractionRing.mk'_eq_div, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    exact ⟨0, _, Subalgebra.algebraMap_mem _ a, _, Subalgebra.algebraMap_mem _ (s : O0 p),
      (map_ne_zero_iff _ hC.inj).2 (nonZeroDivisors.ne_zero s.2), rfl⟩
  have hle : E ≤ (fracField T).toIntermediateField halg := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact mem_fracField_of_mem T (zeta_mem_Lev T n)
    · exact mem_fracField_of_mem T (qq_mem_Lev T n)
  exact hle hxE

end GlobalTheory.FixFrac
end
end

open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerGaloisFixed_eq_div_levelElements : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (x : Ω), (∀ h ∈ Hinf T, h x = x) →
  ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b := by
  atlas_forward_decl GlobalTheory.FixFrac.fixed_eq_div
end

section
section
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.K5.LevClosed

open Polynomial

theorem mem_adjoin_inv_of_isIntegral {R K : Type*} [CommRing R] [Field K] [Algebra R K] {z : K}
    (hz : z ≠ 0) (hi : IsIntegral R z) : z ∈ Algebra.adjoin R {z⁻¹} := by
  obtain ⟨f, hm, hf⟩ := hi
  letI : Invertible z := invertibleOfNonzero hz
  have h1 := eval₂_reverse_mul_pow (algebraMap R K) z f
  rw [hf, invOf_eq_inv] at h1
  have h2 : eval₂ (algebraMap R K) z⁻¹ f.reverse = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ hz)
  have h3 := divX_mul_X_add f.reverse
  rw [coeff_zero_reverse, hm.leadingCoeff] at h3
  have h4 := congrArg (eval₂ (algebraMap R K) z⁻¹) h3
  rw [h2, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, map_one] at h4
  have hzz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  have h5 : z = -(aeval z⁻¹ (divX f.reverse)) := by
    rw [aeval_def]
    linear_combination z * h4 - eval₂ (algebraMap R K) z⁻¹ (divX f.reverse) * hzz
  have hm' : -(aeval z⁻¹ (divX f.reverse)) ∈ Algebra.adjoin R {z⁻¹} :=
    neg_mem (aeval_mem_adjoin_singleton R _)
  rwa [← h5] at hm'

theorem lev_closed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
      IsInt p (a / b) → a / b ∈ Lev T m := by
  intro p _ Ω _ _ hΩ T m hm a ha b hb hb0 hint
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T m
  obtain ⟨-, hrange⟩ := GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hΩ T m hm ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
  rw [← hrange] at ha hb ⊢
  obtain ⟨a', rfl⟩ := (AlgHom.mem_range ι).1 ha
  obtain ⟨b', rfl⟩ := (AlgHom.mem_range ι).1 hb
  rcases ValuationRing.dvd_total b' a' with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine (AlgHom.mem_range ι).2 ⟨c, ?_⟩
    rw [hc, map_mul, mul_div_cancel_left₀ _ hb0]
  · have ha0 : ι a' ≠ 0 := by
      intro h; apply hb0; rw [hc, map_mul, h, zero_mul]
    have hz0 : ι a' / ι b' ≠ 0 := div_ne_zero ha0 hb0
    have hzi : (ι a' / ι b')⁻¹ = ι c := by
      rw [inv_div, hc, map_mul, mul_div_cancel_left₀ _ ha0]
    have hmem := mem_adjoin_inv_of_isIntegral hz0 hint
    rw [hzi] at hmem
    have hle : Algebra.adjoin (O0 p) {ι c} ≤ ι.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 ⟨c, rfl⟩)
    exact hle hmem

end GlobalTheory.K5.LevClosed
end
end

open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerLevelAdjoinRoots_integrallyClosed_quotient : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
  IsInt p (a / b) → a / b ∈ Lev T m := by
  atlas_forward_decl GlobalTheory.K5.LevClosed.lev_closed
end

section
section
open GlobalTheory.K5 GlobalTheory.KumDlog Polynomial

noncomputable section
namespace GlobalTheory.LevDer

theorem int_div_of_mk {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω] [CharZero Ω]
    (m : ℕ) (a : integralClosure (O0 p) Ω)
    (ha : Ideal.Quotient.mk (Ideal.span {((p : integralClosure (O0 p) Ω)) ^ m}) a = 0) :
    IsInt p ((a : Ω) / (p : Ω) ^ m) := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  have hp : (p : Ω) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine int_congr c.2 ?_
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
  field_simp

theorem natCast_eq_pow {Ω : Type} [Field Ω] (N p k : ℕ) (h : N = p ^ (k + 1)) :
    (N : Ω) = (p : Ω) ^ (k + 1) := by
  subst h; push_cast; rfl

set_option maxHeartbeats 2000000 in

theorem exists_levDer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m →
    ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq := by
  intro p _ Ω _ _ hC T m hm
  haveI : CharZero Ω := Basic.charZero_of_isClo hC
  obtain ⟨ι, hι⟩ := Basic.exists_isEmb T m
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hC T m hm ι hι
  have hιA : ∀ z, ι z ∈ integralClosure (O0 p) Ω := fun z =>
    Lev_int T m _ (hrange ▸ AlgHom.mem_range_self ι z)
  let ιA : On p m →ₐ[O0 p] integralClosure (O0 p) Ω := ι.codRestrict _ hιA
  have hιAv : ∀ z, ((ιA z : integralClosure (O0 p) Ω) : Ω) = ι z := fun z => rfl
  let I : Ideal (integralClosure (O0 p) Ω) := Ideal.span {((p : integralClosure (O0 p) Ω)) ^ m}
  letI : Algebra (On p m) (integralClosure (O0 p) Ω ⧸ I) :=
    ((Ideal.Quotient.mk I).comp ιA.toRingHom).toAlgebra
  have halg : ∀ z, algebraMap (On p m) (integralClosure (O0 p) Ω ⧸ I) z = Ideal.Quotient.mk I (ιA z) :=
    fun z => rfl
  haveI : IsScalarTower (O0 p) (On p m) (integralClosure (O0 p) Ω ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [halg, AlgHom.commutes, Ideal.Quotient.mk_algebraMap]

  let g : Ω → On p m := Function.invFun ι
  have hg : ∀ x ∈ Lev T m, ι (g x) = x := fun x hx =>
    Function.invFun_eq ((AlgHom.mem_range ι).1 (hrange.symm ▸ hx))
  have hgm : ∀ x ∈ Lev T m, ∀ z, ι z = x → g x = z := fun x hx z hz =>
    hinj ((hg x hx).trans hz.symm)
  let lift : (integralClosure (O0 p) Ω ⧸ I) → integralClosure (O0 p) Ω :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ s, Ideal.Quotient.mk I (lift s) = s := Function.surjInv_eq _
  have hdiv := fun a ha => GlobalTheory.LevDer.int_div_of_mk (p := p) (Ω := Ω) m a ha

  have hF : ∀ D : Derivation (O0 p) (On p m) (integralClosure (O0 p) Ω ⧸ I),
      IsDer (Lev T m) (fun x => ((lift (D (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ m) := by
    intro D
    refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
    · have e : g (x + y) = g x + g y :=
        hgm _ (add_mem hx hy) _ (by rw [map_add, hg x hx, hg y hy])
      refine int_congr (hdiv (lift (D (g (x + y))) - lift (D (g x)) - lift (D (g y))) ?_) ?_
      · rw [map_sub, map_sub, hlift, hlift, hlift, e, map_add]; ring
      · push_cast; ring
    · have e : g (x * y) = g x * g y :=
        hgm _ (mul_mem hx hy) _ (by rw [map_mul, hg x hx, hg y hy])
      refine int_congr (hdiv (lift (D (g (x * y))) - ιA (g x) * lift (D (g y))
        - ιA (g y) * lift (D (g x))) ?_) ?_
      · rw [map_sub, map_sub, map_mul, map_mul, hlift, hlift, hlift, e, Derivation.leibniz,
          Algebra.smul_def, Algebra.smul_def, halg, halg]; ring
      · push_cast; rw [hιAv, hιAv, hg x hx, hg y hy]; ring
    · have e : g (algebraMap (O0 p) Ω c) = algebraMap (O0 p) (On p m) c :=
        hgm _ (Subalgebra.algebraMap_mem _ c) _ (ι.commutes c)
      refine hdiv _ ?_
      rw [hlift, e, Derivation.map_algebraMap]

  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hpd := GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T 1 1 le_rfl (Nat.totient_pos.2 (ppow_pos (p := p) 1))
  let u : integralClosure (O0 p) Ω := ⟨(p : Ω) / (T.ζ 1 - 1) ^ 1, hpd⟩
  have hz1 : T.ζ 1 - 1 ≠ 0 :=
    sub_ne_zero.2 ((T.prim 1).ne_one (by simpa using (Fact.out : p.Prime).one_lt))
  have hpow : T.ζ (k + 1) ^ p ^ k = T.ζ 1 := by
    have := zeta_pow T 1 k; rwa [add_comm] at this
  have hxn : Ideal.Quotient.mk (towerIdeal p (k + 1)) (C X) = xn p (k + 1) := rfl
  have hyn : Ideal.Quotient.mk (towerIdeal p (k + 1)) X = yn p (k + 1) := rfl
  have hd := congrArg ι (DlogUniq.derivative_cyclotomic_mul p k)
  simp only [map_mul, map_sub, map_pow, map_natCast, map_one, hι.1, hpow] at hd
  have hxz : algebraMap (On p (k + 1)) (integralClosure (O0 p) Ω ⧸ I)
      (aeval (xn p (k + 1)) (derivative (cyclotomic (p ^ (k + 1)) (O0 p)))) *
      algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * xn p (k + 1)) = 0 := by
    rw [← map_mul, halg, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨ιA (xn p (k + 1)) ^ (p ^ (k + 1) - 1) * u * ιA (xn p (k + 1)), Subtype.ext ?_⟩
    have hp' : (p : Ω) = (T.ζ 1 - 1) * ((p : Ω) / (T.ζ 1 - 1) ^ 1) := by field_simp
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, hιAv,
      map_mul, map_natCast, hι.1, u]
    linear_combination (-((p : Ω) / (T.ζ 1 - 1) ^ 1 * T.ζ (k + 1))) * hd -
      (ι (aeval (xn p (k + 1)) (derivative (cyclotomic (p ^ (k + 1)) (O0 p)))) * T.ζ (k + 1)) * hp'
  obtain ⟨Dz, hzx, hzy⟩ := DlogUniq.exists_derivation (cyclotomic (p ^ (k + 1)) (O0 p)) (p ^ (k + 1))
    (qO p) (towerIdeal p (k + 1)) rfl (integralClosure (O0 p) Ω ⧸ I)
    (algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * xn p (k + 1))) 0 hxz (mul_zero _)
  have hyq : ∀ N : ℕ, N = p ^ (k + 1) → (N : integralClosure (O0 p) Ω ⧸ I) *
      algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * yn p (k + 1)) = 0 := by
    intro N hN
    rw [← map_natCast (algebraMap (On p (k + 1)) (integralClosure (O0 p) Ω ⧸ I)) N, ← map_mul, halg,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨ιA ((p : On p (k + 1)) * yn p (k + 1)), Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, hιAv,
      map_mul, map_natCast]
    rw [natCast_eq_pow (Ω := Ω) N p k hN]
    ring
  obtain ⟨N, hN⟩ : ∃ N, N = p ^ (k + 1) := ⟨_, rfl⟩
  obtain ⟨Dq, hqx, hqy⟩ := DlogUniq.exists_derivation (cyclotomic (p ^ (k + 1)) (O0 p)) N
    (qO p) (towerIdeal p (k + 1)) (by rw [hN]; rfl) (integralClosure (O0 p) Ω ⧸ I)
    0 (algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * yn p (k + 1))) (mul_zero _)
    (hyq N hN)
  rw [hxn] at hzx hqx
  rw [hyn] at hzy hqy
  have hgz : g (T.ζ (k + 1)) = xn p (k + 1) := hgm _ (zeta_mem_Lev T _) _ hι.1
  have hgq : g (T.qq (k + 1)) = yn p (k + 1) := hgm _ (qq_mem_Lev T _) _ hι.2
  refine ⟨fun x => ((lift (Dz (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ (k + 1),
    fun x => ((lift (Dq (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ (k + 1),
    hF Dz, hF Dq, ?_, ?_, ?_, ?_⟩
  · refine int_congr (hdiv (lift (Dz (xn p (k + 1))) - ιA ((p : On p (k + 1)) * xn p (k + 1))) ?_) ?_
    · rw [map_sub, hlift, hzx, halg, sub_self]
    · simp only [hgz, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast, hιAv, map_mul, map_natCast, hι.1]
      ring
  · exact int_congr (hdiv (lift (Dz (yn p (k + 1)))) (by rw [hlift, hzy])) (by simp only [hgq])
  · exact int_congr (hdiv (lift (Dq (xn p (k + 1)))) (by rw [hlift, hqx])) (by simp only [hgz])
  · refine int_congr (hdiv (lift (Dq (yn p (k + 1))) - ιA ((p : On p (k + 1)) * yn p (k + 1))) ?_) ?_
    · rw [map_sub, hlift, hqy, halg, sub_self]
    · simp only [hgq, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast, hιAv, map_mul, map_natCast, hι.2]
      ring

end GlobalTheory.LevDer
end
end

open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dlog_derivations_towerLevel_mod_integral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m →
  ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq := by
  atlas_forward_decl GlobalTheory.LevDer.exists_levDer
end

section
section
noncomputable section

namespace GlobalTheory.LevGlue

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem der_pow_val {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (hD : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) (hp : (p : Ω) ≠ 0) {x c : Ω} {m j : ℕ} (hx : x ∈ S)
    (h : IsInt p (D x - c * x / (p : Ω) ^ (m + j))) :
    IsInt p (D (x ^ (p ^ j)) - c * x ^ (p ^ j) / (p : Ω) ^ m) := by
  obtain ⟨k, hk⟩ : ∃ k, p ^ j = k + 1 := ⟨p ^ j - 1, (Nat.succ_pred_eq_of_pos (ppow_pos j)).symm⟩
  have h1 := hD.pow hS hx k
  rw [← hk] at h1
  have e : c * x ^ (p ^ j) / (p : Ω) ^ m =
      ((p ^ j : ℕ) : Ω) * x ^ k * (c * x / (p : Ω) ^ (m + j)) := by
    have e1 : x ^ (p ^ j) = x ^ k * x := by rw [hk, pow_succ]
    have e2 : ((p ^ j : ℕ) : Ω) = (p : Ω) ^ j := by push_cast; ring
    rw [e1, e2, pow_add]
    field_simp
  refine int_congr (int_add h1 (int_mul (int_mul (int_nat (p ^ j)) (int_pow (hS x hx) k)) h)) ?_
  linear_combination (-1 : Ω) * e

theorem compat_gen (T : Tower p Ω) {m n : ℕ} (hmn : m ≤ n) {D D' : Ω → Ω}
    (hD : IsDer (Lev T n) D) (hD' : IsDer (Lev T m) D')
    (hz : IsInt p (D (T.ζ m) - D' (T.ζ m))) (hq : IsInt p (D (T.qq m) - D' (T.qq m))) :
    ∀ x ∈ Lev T m, IsInt p (D x - D' x) :=
  IsDer.adjoin (t := {T.ζ m, T.qq m}) (IsDer.sub (hD.mono (Lev_mono T hmn)) hD') (Lev_int T m)
    (by rintro x (rfl | rfl); exacts [zeta_mem_Lev T m, qq_mem_Lev T m])
    (by rintro x (rfl | rfl); exacts [hz, hq])

theorem vals_down (T : Tower p Ω) (hp : (p : Ω) ≠ 0) {m n : ℕ} (hmn : m ≤ n) {dz dq : Ω → Ω}
    (hz : IsDer (Lev T n) dz) (hq : IsDer (Lev T n) dq) (hv : Vals T n dz dq) : Vals T m dz dq := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hS := Lev_int T (m + j)
  have zm := zeta_mem_Lev T (m + j)
  have qm := qq_mem_Lev T (m + j)
  have z0 : ∀ {D : Ω → Ω} {x : Ω}, IsInt p (D x) → IsInt p (D x - 0 * x / (p : Ω) ^ (m + j)) :=
    fun h => int_congr h (by ring)
  have z1 : ∀ {D : Ω → Ω} {y : Ω}, IsInt p (D y - 0 * y / (p : Ω) ^ m) → IsInt p (D y) :=
    fun h => int_congr h (by ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := der_pow_val hz hS hp zm hv.1
    rwa [zeta_pow] at this
  · have := z1 (der_pow_val hz hS hp qm (z0 hv.2.1))
    rwa [qq_pow] at this
  · have := z1 (der_pow_val hq hS hp zm (z0 hv.2.2.1))
    rwa [zeta_pow] at this
  · have := der_pow_val hq hS hp qm hv.2.2.2
    rwa [qq_pow] at this

theorem glue_fam (T : Tower p Ω) (F : ℕ → Ω → Ω) (hF : ∀ m, IsDer (Lev T (m + 1)) (F m))
    (hc : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (F n x - F m x)) :
    ∃ G : Ω → Ω, (∀ m, ∀ x ∈ Lev T (m + 1), IsInt p (G x - F m x)) ∧
      ∀ S : Subalgebra (O0 p) Ω, (∀ x ∈ S, ∃ m, x ∈ Lev T m) → IsDer S G := by
  classical
  let M : Ω → ℕ := fun x => if h : ∃ m, x ∈ Lev T (m + 1) then Classical.choose h else 0
  have hG : ∀ m, ∀ x ∈ Lev T (m + 1), IsInt p (F (M x) x - F m x) := by
    intro m x hx
    have h : ∃ m, x ∈ Lev T (m + 1) := ⟨m, hx⟩
    have hM : M x = Classical.choose h := dif_pos h
    have ha := Classical.choose_spec h
    rw [hM]
    have h1 := hc _ (max m (Classical.choose h)) (le_max_right _ _) x ha
    have h2 := hc _ (max m (Classical.choose h)) (le_max_left _ _) x hx
    exact int_congr (int_sub h2 h1) (by ring)
  refine ⟨fun x => F (M x) x, hG, fun S hS => ?_⟩
  have two : ∀ x ∈ S, ∀ y ∈ S, ∃ n, x ∈ Lev T (n + 1) ∧ y ∈ Lev T (n + 1) := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hS x hx
    obtain ⟨b, hb⟩ := hS y hy
    exact ⟨a + b, Lev_mono T (by omega) ha, Lev_mono T (by omega) hb⟩
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    refine int_congr (int_add (int_add (int_sub (int_sub ((hF n).1 x hxn y hyn)
      (hG n x hxn)) (hG n y hyn)) (hG n _ (add_mem hxn hyn))) int_zero) ?_
    ring
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    have ix := Lev_int T _ x hxn
    have iy := Lev_int T _ y hyn
    refine int_congr (int_sub (int_sub (int_add ((hF n).2.1 x hxn y hyn)
      (hG n _ (mul_mem hxn hyn))) (int_mul ix (hG n y hyn))) (int_mul iy (hG n x hxn))) ?_
    ring
  · have hm := (Lev T (0 + 1)).algebraMap_mem c
    exact int_congr (int_add (hG 0 _ hm) ((hF 0).2.2 c)) (by ring)

theorem glue : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
    (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq) →
    ∃ dz dq : Ω → Ω, IsDer B dz ∧ IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → Vals T m dz dq := by
  intro p _ Ω _ _ hclo T B hB hlev
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hclo
  have hp : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h' : ∀ m : ℕ, ∃ dz dq : Ω → Ω, IsDer (Lev T (m + 1)) dz ∧ IsDer (Lev T (m + 1)) dq ∧
      Vals T (m + 1) dz dq := fun m => hlev (m + 1) (by omega)
  choose Z Q hZ hQ hV using h'
  have cZ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (Z n x - Z m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hZ n) (hZ m)
      (int_congr (int_sub v.1 (hV m).1) (by ring)) (int_congr (int_sub v.2.1 (hV m).2.1) (by ring))
  have cQ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (Q n x - Q m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hQ n) (hQ m)
      (int_congr (int_sub v.2.2.1 (hV m).2.2.1) (by ring))
      (int_congr (int_sub v.2.2.2 (hV m).2.2.2) (by ring))
  obtain ⟨dz, hdz, hdzB⟩ := glue_fam T Z hZ cZ
  obtain ⟨dq, hdq, hdqB⟩ := glue_fam T Q hQ cQ
  refine ⟨dz, dq, hdzB B hB, hdqB B hB, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have v := hV k
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact int_congr (int_add (hdz k _ (zeta_mem_Lev T _)) v.1) (by ring)
  · exact int_congr (int_add (hdz k _ (qq_mem_Lev T _)) v.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (zeta_mem_Lev T _)) v.2.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (qq_mem_Lev T _)) v.2.2.2) (by ring)

end GlobalTheory.LevGlue
end
end

open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dlog_derivations_glued_tower_levels : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
  (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq) →
  ∃ dz dq : Ω → Ω, IsDer B dz ∧ IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → Vals T m dz dq := by
  atlas_forward_decl GlobalTheory.LevGlue.glue
end

section
section
noncomputable section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumDlog

theorem kaehler_rel_isInt (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω) (hS : ∀ x ∈ S, IsInt p x)
    (hι : ∀ x, ι x ∈ S) (D : Ω → Ω) (hD : IsDer S D) (a b c x y z : On p n)
    (hrel : a • KaehlerDifferential.D (O0 p) (On p n) x =
      b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z) :
    IsInt p (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  letI : Module (On p n) Ω := Module.compHom Ω ι.toRingHom
  have hsm : ∀ (r : On p n) (w : Ω), r • w = ι r * w := fun _ _ => rfl
  haveI : IsScalarTower (O0 p) (On p n) Ω := ⟨fun r s w => by
    rw [hsm, hsm, map_smul, smul_mul_assoc]⟩
  let N : Submodule (On p n) Ω :=
    { carrier := {w | IsInt p w}
      add_mem' := fun ha hb => int_add ha hb
      zero_mem' := int_zero
      smul_mem' := fun r w hw => by
        show IsInt p (r • w)
        rw [hsm]; exact int_mul (hS _ (hι r)) hw }
  have memN : ∀ w, w ∈ N ↔ IsInt p w := fun _ => Iff.rfl
  have key : ∀ w w' : Ω, IsInt p (w - w') → N.mkQ w = N.mkQ w' := fun w w' h =>
    (Submodule.Quotient.eq N).2 h
  let L : On p n →ₗ[O0 p] Ω ⧸ N :=
    { toFun := fun u => N.mkQ (D (ι u))
      map_add' := fun u v => by
        rw [← map_add]
        refine key _ _ ?_
        rw [map_add]
        exact int_congr (hD.1 _ (hι u) _ (hι v)) (by ring)
      map_smul' := fun r u => by
        simp only [RingHom.id_apply]
        rw [← LinearMap.map_smul_of_tower]
        refine key _ _ ?_
        rw [map_smul, Algebra.smul_def, Algebra.smul_def]
        exact hD.alg_mul hS r (hι u) }
  let d : Derivation (O0 p) (On p n) (Ω ⧸ N) := Derivation.mk' L (fun u v => by
    show N.mkQ (D (ι (u * v))) = u • N.mkQ (D (ι v)) + v • N.mkQ (D (ι u))
    rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add]
    refine key _ _ ?_
    rw [hsm, hsm, map_mul]
    exact int_congr (hD.2.1 _ (hι u) _ (hι v)) (by ring))
  have hd : ∀ u, d.liftKaehlerDifferential (KaehlerDifferential.D (O0 p) (On p n) u) =
      N.mkQ (D (ι u)) := fun u => by
    rw [Derivation.liftKaehlerDifferential_comp_D]; rfl
  have h2 := congrArg d.liftKaehlerDifferential hrel
  simp only [map_add, LinearMap.map_smul, hd] at h2
  rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add,
    ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, N.ker_mkQ, memN, hsm, hsm, hsm] at h2
  exact int_congr h2 (by ring)

end GlobalTheory.KumDlog
end
end

open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_relation_derivationModIntegral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω), (∀ x ∈ S, IsInt p x) → (∀ x, ι x ∈ S) →
  ∀ D : Ω → Ω, IsDer S D → ∀ a b c x y z : On p n,
  a • KaehlerDifferential.D (O0 p) (On p n) x = b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z →
  IsInt p (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  atlas_forward_decl GlobalTheory.KumDlog.kaehler_rel_isInt
end

section
section
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumExpo

theorem exponents : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n m : ℕ), 2 * n ≤ m → ∀ lz lq : Gal p Ω → ZMod (p ^ n),
  IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq → ∀ g ∈ Gn T n,
  ∃ (i j : ℕ) (s t : ℤ), g (T.ζ m) = T.ζ m ^ i ∧ g (T.qq m) = T.ζ m ^ j * T.qq m ∧
    (i : ℤ) = 1 + p ^ n * ((lz g).val : ℤ) + p ^ (2 * n) * s ∧ (j : ℤ) = p ^ n * ((lq g).val : ℤ) + p ^ (2 * n) * t := by
  intro p _ Ω _ _ T n m hm lz lq hz hq g hg
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm

  have h1 : (g (T.ζ (2 * n + k))) ^ (p ^ (2 * n + k)) = 1 := by
    rw [← map_pow, (T.prim _).pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := (T.prim _).eq_pow_of_pow_eq_one h1
  have hqne := qq_ne T (2 * n + k)
  have h2 : (g (T.qq (2 * n + k)) / T.qq (2 * n + k)) ^ (p ^ (2 * n + k)) = 1 := by
    rw [div_pow, ← map_pow, kummerTower_qq_pow_level_eq_q, AlgEquiv.commutes, ← kummerTower_qq_pow_level_eq_q T (2 * n + k),
      div_self (pow_ne_zero _ hqne)]
  obtain ⟨j, -, hj⟩ := (T.prim _).eq_pow_of_pow_eq_one h2
  have hj' : g (T.qq (2 * n + k)) = T.ζ (2 * n + k) ^ j * T.qq (2 * n + k) := by
    rw [hj, div_mul_cancel₀ _ hqne]

  have ez : T.ζ (2 * n + k) ^ (p ^ k) = T.ζ (2 * n) := zeta_pow T (2 * n) k
  have eq' : T.qq (2 * n + k) ^ (p ^ k) = T.qq (2 * n) := qq_pow T (2 * n) k
  have ezn : T.ζ (2 * n) ^ (p ^ n) = T.ζ n := by
    have := zeta_pow T n n
    rwa [← two_mul] at this
  have gz : g (T.ζ (2 * n)) = T.ζ (2 * n) ^ i := by
    rw [← ez, map_pow, ← hi, ← pow_mul, ← pow_mul, Nat.mul_comm i]
  have gq : g (T.qq (2 * n)) = T.ζ (2 * n) ^ j * T.qq (2 * n) := by
    rw [← eq', map_pow, hj', mul_pow, ← pow_mul, mul_comm j, pow_mul, ez]
  have kz := hz g hg
  have kq := hq g hg
  rw [gz, ← ezn, ← pow_mul, ← pow_succ] at kz
  rw [gq, ← ezn, ← pow_mul] at kq
  have kq' := mul_right_cancel₀ (qq_ne T (2 * n)) kq
  rw [GlobalTheory.K5.Basic.zeta_pow_eq_iff] at kz kq'
  rw [Nat.modEq_iff_dvd] at kz kq'
  obtain ⟨s, hs⟩ := kz
  obtain ⟨t, ht⟩ := kq'
  refine ⟨i, j, -s, -t, hi.symm, hj', ?_, ?_⟩
  · push_cast at hs ⊢
    linear_combination -hs
  · push_cast at ht ⊢
    linear_combination -ht

end GlobalTheory.KumExpo
end

open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerGn_exponents_kummer_cochains : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n m : ℕ), 2 * n ≤ m → ∀ lz lq : Gal p Ω → ZMod (p ^ n),
  IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq → ∀ g ∈ Gn T n,
  ∃ (i j : ℕ) (s t : ℤ), g (T.ζ m) = T.ζ m ^ i ∧ g (T.qq m) = T.ζ m ^ j * T.qq m ∧
    (i : ℤ) = 1 + p ^ n * ((lz g).val : ℤ) + p ^ (2 * n) * s ∧ (j : ℤ) = p ^ n * ((lq g).val : ℤ) + p ^ (2 * n) * t := by
  atlas_forward_decl GlobalTheory.KumExpo.exponents
end

section
section
open GlobalTheory.K5

noncomputable section
namespace GlobalTheory.KumDlog
variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem emb_mem_Lev {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hΩ : IsClo p Ω) (hn : 1 ≤ n)
    (hι : IsEmb T n ι) (x : On p n) : ι x ∈ Lev T n := by
  rw [← (GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hΩ T n hn ι hι).2]; exact ⟨x, rfl⟩

theorem p_ne (T : Tower p Ω) : (p : Ω) ≠ 0 := by
  have h := (T.prim 1).neZero'
  have := h.ne
  simpa using this

theorem conj_mem_Hinf {T : Tower p Ω} {n : ℕ} {lz lq : Gal p Ω → ZMod (p ^ n)}
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq)
    {g h : Gal p Ω} (hg : g ∈ Gn T n) (hh : h ∈ Hinf T) : g⁻¹ * h * g ∈ Hinf T := by
  rw [mem_Hinf] at hh ⊢
  intro m
  obtain ⟨i, j, -, -, e1, e2, -⟩ := GlobalTheory.T.towerGn_exponents_kummer_cochains p Ω T n (m + 2 * n) (by omega) lz lq hz hq g hg
  have k1 : (g⁻¹ * h * g) (T.ζ (m + 2 * n)) = T.ζ (m + 2 * n) := by
    show g.symm (h (g _)) = _
    rw [AlgEquiv.symm_apply_eq, e1, map_pow, (hh _).1]
  have k2 : (g⁻¹ * h * g) (T.qq (m + 2 * n)) = T.qq (m + 2 * n) := by
    show g.symm (h (g _)) = _
    rw [AlgEquiv.symm_apply_eq, e2, map_mul, map_pow, (hh _).1, (hh _).2]
  constructor
  · rw [← zeta_pow T m (2 * n), map_pow, k1]
  · rw [← qq_pow T m (2 * n), map_pow, k2]

theorem gal_mem_fix {T : Tower p Ω} {n : ℕ} {a lz lq : Gal p Ω → ZMod (p ^ n)} {r : Ω}
    (ha : IsKum T n (Gn T n) r a)
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq)
    {g : Gal p Ω} (hg : g ∈ Gn T n) : ∀ x ∈ FixI (Hfix T r), g x ∈ FixI (Hfix T r) := by
  intro x hx
  refine ⟨int_gal g hx.1, fun h hh => ?_⟩
  have h1 : g⁻¹ * h * g ∈ Hfix T r := by
    refine ⟨conj_mem_Hinf hz hq hg hh.1, ?_⟩
    show g.symm (h (g r)) = r
    have h2 : h r = r := hh.2
    rw [AlgEquiv.symm_apply_eq, ha g hg, map_mul, map_pow, h2, (mem_Hinf.1 hh.1 n).1]
  have h3 : g.symm (h (g x)) = x := hx.2 _ h1
  rwa [AlgEquiv.symm_apply_eq] at h3

theorem fix_mem_Lev (hΩ : IsClo p Ω) (T : Tower p Ω) :
    ∀ x ∈ FixI (Hinf T), ∃ m : ℕ, x ∈ Lev T m := by
  intro x hx
  obtain ⟨m, a, ha, b, hb, hb0, rfl⟩ := GlobalTheory.T.towerGaloisFixed_eq_div_levelElements p Ω hΩ T x hx.2
  exact ⟨m + 1, GlobalTheory.T.towerLevelAdjoinRoots_integrallyClosed_quotient p Ω hΩ T (m + 1) (by omega) a (Lev_mono T (by omega) ha) b
    (Lev_mono T (by omega) hb) hb0 hx.1⟩

theorem der_zeta_pow {T : Tower p Ω} {C : Subalgebra (O0 p) Ω} {D : Ω → Ω} (hD : IsDer C D)
    (hC : ∀ x ∈ C, IsInt p x) {m : ℕ} (hm : T.ζ m ∈ C) {e : Ω}
    (he : IsInt p (D (T.ζ m) - e * T.ζ m)) (i : ℕ) :
    IsInt p (D (T.ζ m ^ i) - i * e * T.ζ m ^ i) := by
  have h1 := int_mul (int_zeta_inv T m) (int_add (hD.pow' hC hm i)
    (int_mul (int_mul (int_nat i) (int_pow (int_zeta T m) i)) he))
  refine int_congr h1 ?_
  have := zeta_ne T m
  field_simp
  ring

theorem exists_ders (hp2 : p ≠ 2) (hΩ : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) {r : Ω}
    (hr : IsInt p r) {a lz lq : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n (Gn T n) r a)
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq) :
    ∃ Dz Dq : Ω → Ω, IsDer (FixI (Hfix T r)) Dz ∧ IsDer (FixI (Hfix T r)) Dq ∧
      IsInt p (Dz (T.ζ n) - (p : Ω) ^ 4 / p ^ n * T.ζ n) ∧ IsInt p (Dz (T.qq n)) ∧
      IsInt p (Dq (T.ζ n)) ∧ IsInt p (Dq (T.qq n) - (p : Ω) ^ 4 / p ^ n * T.qq n) ∧
      ∀ g ∈ Gn T n, ∃ s t : ℤ, IsInt p ((p : Ω) ^ 2 * (Dz (g r) -
        (1 + p ^ n * ((lz g).val : Ω) + p ^ (2 * n) * s) * g (Dz r) -
        (p ^ n * ((lq g).val : Ω) + p ^ (2 * n) * t) * g (Dq r))) := by
  have hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r := fun h hh => ⟨_, ha h (Hinf_le T n hh)⟩
  obtain ⟨ι, _, u, v, hu, hv, huv, h0⟩ := GlobalTheory.T.exists_almostGalois_coordinates p hp2 Ω hΩ T n r hr hH
  obtain ⟨tr, hd⟩ := GlobalTheory.T.traceTower_almostDualBases_adjoin_kummer_root p Ω T n r hr hH ι u v hu hv huv h0
  obtain ⟨dz, dq, hdz, hdq, hval⟩ := GlobalTheory.T.exists_dlog_derivations_glued_tower_levels p Ω hΩ T _ (fix_mem_Lev hΩ T)
    (fun m hm => GlobalTheory.T.exists_dlog_derivations_towerLevel_mod_integral p Ω hΩ T m hm)
  obtain ⟨Dz, hDz, ez⟩ := GlobalTheory.T.exists_derivationModIntegral_extension_p_cube p Ω _ _ ι u v tr hd dz hdz
  obtain ⟨Dq, hDq, eq⟩ := GlobalTheory.T.exists_derivationModIntegral_extension_p_cube p Ω _ _ ι u v tr hd dq hdq
  have hC := hd.2.1
  have hLB : ∀ m, Lev T m ≤ FixI (Hinf T) := fun m => Lev_le_FixI T m (Hinf_le T m)
  have p3 : IsInt p ((p : Ω) ^ 3) := int_pow (int_nat p) 3
  have V : ∀ m, 1 ≤ m → IsInt p (Dz (T.ζ m) - (p : Ω) ^ 4 / p ^ m * T.ζ m) ∧ IsInt p (Dz (T.qq m)) ∧
      IsInt p (Dq (T.ζ m)) ∧ IsInt p (Dq (T.qq m) - (p : Ω) ^ 4 / p ^ m * T.qq m) := by
    intro m hm
    obtain ⟨v1, v2, v3, v4⟩ := hval m hm
    have z := hLB m (zeta_mem_Lev T m)
    have q := hLB m (qq_mem_Lev T m)
    exact ⟨int_congr (int_add (ez _ z) (int_mul p3 v1)) (by ring),
      int_congr (int_add (ez _ q) (int_mul p3 v2)) (by ring),
      int_congr (int_add (eq _ z) (int_mul p3 v3)) (by ring),
      int_congr (int_add (eq _ q) (int_mul p3 v4)) (by ring)⟩
  obtain ⟨w1, w2, w3, w4⟩ := V n hn
  refine ⟨Dz, Dq, hDz, hDq, w1, w2, w3, w4, fun g hg => ?_⟩
  have hrC : r ∈ FixI (Hfix T r) := ⟨hr, fun h hh => hh.2⟩
  have hex : ∀ kl : ι × ι, ∃ m, tr (u kl.2 * (r * v kl.1)) ∈ Lev T m := fun kl =>
    fix_mem_Lev hΩ T _ (hd.2.2.2.2.1 _ (mul_mem (hu _) (mul_mem hrC (hv _))))
  choose M hM using hex
  obtain ⟨m, hm2, hmM⟩ : ∃ m, 2 * n ≤ m ∧ ∀ kl, M kl ≤ m :=
    ⟨max (2 * n) (Finset.univ.sup M), le_max_left _ _, fun kl =>
      le_trans (Finset.le_sup (f := M) (Finset.mem_univ kl)) (le_max_right _ _)⟩
  obtain ⟨i, j, s, t, e1, e2, hi, hj⟩ := GlobalTheory.T.towerGn_exponents_kummer_cochains p Ω T n m hm2 lz lq hz hq g hg
  obtain ⟨y1, y2, y3, y4⟩ := V m (by omega)
  have zC := hd.1 (hLB m (zeta_mem_Lev T m))
  have qC := hd.1 (hLB m (qq_mem_Lev T m))
  have hD' := ((hDz.conj g (gal_mem_fix ha hz hq hg)).sub (hDz.smul (int_nat i))).sub
    (hDq.smul (int_nat j))
  have hvan := hD'.adjoin hC (t := {T.ζ m, T.qq m}) (by rintro x (rfl | rfl); exacts [zC, qC]) (by
    rintro x (rfl | rfl)
    · have a1 := int_gal g.symm (der_zeta_pow hDz hC zC y1 i)
      rw [← e1] at a1
      refine int_congr (int_sub (int_sub a1 (int_mul (int_nat i) y1)) (int_mul (int_nat j) y3)) ?_
      simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, AlgEquiv.symm_apply_apply]
      ring
    · have a1 := int_add (int_add (hDz.2.1 _ (pow_mem zC j) _ qC)
        (int_mul (int_pow (int_zeta T m) j) y2)) (int_mul (int_qq T m) (der_zeta_pow hDz hC zC y1 j))
      have a2 : IsInt p (Dz (g (T.qq m)) - j * ((p : Ω) ^ 4 / p ^ m) * g (T.qq m)) := by
        rw [e2]; exact int_congr a1 (by ring)
      have a3 := int_gal g.symm a2
      refine int_congr (int_sub (int_sub a3 (int_mul (int_nat i) y2)) (int_mul (int_nat j) y4)) ?_
      simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, AlgEquiv.symm_apply_apply]
      ring)
  have hU := GlobalTheory.T.derivationModIntegral_almostDual_p_sq_isInt p Ω _ _ ι u v tr hd _ hD' r hrC
    (fun k l => hvan _ (Lev_mono T (hmM (k, l)) (hM (k, l))))
  refine ⟨s, t, int_congr (int_gal g hU) ?_⟩
  have hi' : (i : Ω) = 1 + p ^ n * ((lz g).val : Ω) + p ^ (2 * n) * s := by
    have := congrArg (Int.cast : ℤ → Ω) hi
    push_cast at this
    simpa using this
  have hj' : (j : Ω) = p ^ n * ((lq g).val : Ω) + p ^ (2 * n) * t := by
    have := congrArg (Int.cast : ℤ → Ω) hj
    push_cast at this
    simpa using this
  rw [← hi', ← hj']
  simp only [map_sub, map_mul, map_pow, map_natCast, AlgEquiv.apply_symm_apply]

theorem core (hp2 : p ≠ 2) (hΩ : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n)
    (ι : On p n →ₐ[O0 p] Ω) (hι : IsEmb T n ι) (u A B : On p n)
    (hrel : (xn p n * yn p n) • KaehlerDifferential.D (O0 p) (On p n) u =
      (xn p n * A) • KaehlerDifferential.D (O0 p) (On p n) (yn p n) +
      (yn p n * B) • KaehlerDifferential.D (O0 p) (On p n) (xn p n))
    {r : Ω} (hr : r ^ (p ^ n) = ι u) {a lz lq : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a)
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq) :
    Cob1 n (Gn T n) (fun g => (p : Ω) ^ 6 *
      (ι u * ((a g).val : Ω) - ι A * ((lq g).val : Ω) - ι B * ((lz g).val : Ω))) := by
  have hL := emb_mem_Lev hΩ hn hι
  have hI : ∀ x, IsInt p (ι x) := fun x => Lev_int T n _ (hL x)
  have hrI : IsInt p r := int_of_pow (ppow_pos n) (hr ▸ hI u)
  obtain ⟨Dz, Dq, hDz, hDq, w1, w2, w3, w4, hE⟩ := exists_ders hp2 hΩ T n hn hrI ha hz hq
  have hC : ∀ x ∈ FixI (Hfix T r), IsInt p x := fun x hx => hx.1
  have hLC : Lev T n ≤ FixI (Hfix T r) := Lev_le_FixI T n (le_trans inf_le_left (Hinf_le T n))
  have hrC : r ∈ FixI (Hfix T r) := ⟨hrI, fun h hh => hh.2⟩
  have kz := GlobalTheory.T.kaehler_relation_derivationModIntegral p Ω n ι _ hC (fun x => hLC (hL x)) Dz hDz _ _ _ _ _ _ hrel
  have kq := GlobalTheory.T.kaehler_relation_derivationModIntegral p Ω n ι _ hC (fun x => hLC (hL x)) Dq hDq _ _ _ _ _ _ hrel
  simp only [map_mul, hι.1, hι.2] at kz kq
  have z0 := zeta_ne T n
  have q0 := qq_ne T n
  have p0 := p_ne T
  have inv := int_mul (int_zeta_inv T n) (int_qq_inv T n)
  obtain ⟨N, hN⟩ : ∃ N, p ^ n = N + 1 := ⟨p ^ n - 1, by have := ppow_pos (p := p) n; omega⟩
  have hN' : ((N + 1 : ℕ) : Ω) = (p : Ω) ^ n := by rw [← hN]; push_cast; rfl
  have pz := hDz.pow hC hrC N
  have pq := hDq.pow hC hrC N
  rw [hN', ← hN, hr] at pz pq
  have Ez : IsInt p ((p : Ω) ^ n * (r ^ N * Dz r) - ι B * (p ^ 4 / p ^ n)) := by
    refine int_congr (int_sub (int_mul inv (int_add (int_add kz
      (int_mul (int_mul (int_zeta T n) (hI A)) w2)) (int_mul (int_mul (int_qq T n) (hI B)) w1))) pz) ?_
    field_simp
    ring
  have Eq : IsInt p ((p : Ω) ^ n * (r ^ N * Dq r) - ι A * (p ^ 4 / p ^ n)) := by
    refine int_congr (int_sub (int_mul inv (int_add (int_add kq
      (int_mul (int_mul (int_zeta T n) (hI A)) w4)) (int_mul (int_mul (int_qq T n) (hI B)) w3))) pq) ?_
    field_simp
    ring
  have p2 : IsInt p ((p : Ω) ^ 2) := int_pow (int_nat p) 2
  refine ⟨_, int_mul p2 Ez, fun g hg => ?_⟩
  obtain ⟨s, t, hst⟩ := hE g hg
  have hfix : ∀ x, g (ι x) = ι x := fun x => (Lev_le_FixI T n le_rfl (hL x)).2 g hg
  have zC := hLC (zeta_mem_Lev T n)
  have b1 := int_add (hDz.2.1 _ (pow_mem zC (a g).val) _ hrC)
    (int_mul hrI (der_zeta_pow hDz hC zC w1 (a g).val))
  rw [← ha g hg] at b1
  have b2 := int_mul (int_pow (int_gal g hrI) N) (int_sub hst (int_mul p2 b1))
  have gz := int_gal g Ez
  have gq := int_gal g Eq
  have pn : IsInt p ((p : Ω) ^ n) := int_pow (int_nat p) n
  have p6 : IsInt p ((p : Ω) ^ 6) := int_pow (int_nat p) 6
  refine ⟨_, int_add (int_add (int_add (int_add b2
    (int_mul (int_mul (int_add (int_nat (lz g).val) (int_mul pn (int_int s))) p2) gz))
    (int_mul (int_mul (int_add (int_nat (lq g).val) (int_mul pn (int_int t))) p2) gq))
    (int_mul (int_mul p6 (hI B)) (int_int s))) (int_mul (int_mul p6 (hI A)) (int_int t)), ?_⟩
  simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, hfix]
  have c1 : g r ^ N * T.ζ n ^ (a g).val = r ^ N := by
    rw [ha g hg, mul_pow, mul_right_comm, ← pow_succ, ← hN, ← pow_mul, mul_comm (a g).val, pow_mul,
      (T.prim n).pow_eq_one, one_pow, one_mul]
  have c2 : r ^ N * r = ι u := by rw [← pow_succ, ← hN, hr]
  rw [two_mul, pow_add]
  have hQ : (p : Ω) ^ n * ((p : Ω) ^ 4 / (p : Ω) ^ n) = (p : Ω) ^ 4 :=
    mul_div_cancel₀ _ (pow_ne_zero _ p0)
  generalize (p : Ω) ^ 4 / (p : Ω) ^ n = Q at *
  generalize (p : Ω) ^ n = P at *
  linear_combination (-(p : Ω) ^ 2 * P * Dz r - (p : Ω) ^ 6 * r * ((a g).val : Ω)) * c1 -
    (p : Ω) ^ 6 * ((a g).val : Ω) * c2 +
    (-(p : Ω) ^ 2 * r * ((a g).val : Ω) * (g r ^ N * T.ζ n ^ (a g).val) +
      (((lz g).val : Ω) + P * s) * (p : Ω) ^ 2 * ι B + (((lq g).val : Ω) + P * t) * (p : Ω) ^ 2 * ι A) * hQ

theorem exists_kum (T : Tower p Ω) (n : ℕ) {r : Ω} (hr : r ≠ 0)
    (h : ∀ g ∈ Gn T n, g (r ^ (p ^ n)) = r ^ (p ^ n)) : ∃ a, IsKum T n (Gn T n) r a := by
  haveI : NeZero (p ^ n) := ⟨(ppow_pos n).ne'⟩
  have : ∀ g : Gal p Ω, ∃ i : ZMod (p ^ n), g ∈ Gn T n → g r = T.ζ n ^ i.val * r := by
    intro g
    by_cases hg : g ∈ Gn T n
    · obtain ⟨i, hi, e⟩ := (T.prim n).eq_pow_of_pow_eq_one (ξ := g r / r) (by
        rw [div_pow, ← map_pow, h g hg, div_self (pow_ne_zero _ hr)])
      refine ⟨i, fun _ => ?_⟩
      rw [ZMod.val_cast_of_lt hi, e, div_mul_cancel₀ _ hr]
    · exact ⟨0, fun h => absurd h hg⟩
  choose a ha using this
  exact ⟨a, fun g hg => ha g hg⟩

theorem kummer_eq_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k : ℤ) (w : (On p n)ˣ) (α β : On p n), IsDlog p n (w : On p n) α β →
  ∀ r : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w →
  ∀ a lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob1 n (Gn T n) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * ι α * ((lq g).val : Ω) -
      (p : Ω) ^ c * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) * ((lz g).val : Ω)) := by
  intro p _ hp2
  refine ⟨7, ?_⟩
  intro Ω _ _ hΩ T n hn ι hι k w α β hd r hr a lz lq ha hz hq
  haveI := hΩ.clo
  have hL := emb_mem_Lev hΩ hn hι
  have hI : ∀ x, IsInt p (ι x) := fun x => Lev_int T n _ (hL x)
  have hfix : ∀ g ∈ Gn T n, ∀ x, g (ι x) = ι x := fun g hg x =>
    (Lev_le_FixI T n le_rfl (hL x)).2 g hg
  have hπ : T.ζ n - 1 ≠ 0 := sub_ne_zero.2 ((T.prim n).ne_one
    (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt))
  have hww : ι w * ι (↑w⁻¹ : On p n) = 1 := by rw [← map_mul]; simp
  have hw0 : ι w ≠ 0 := left_ne_zero_of_mul_eq_one hww
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (T.ζ n - 1) (ppow_pos (p := p) n)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hπ (by rw [← hs, zero_pow (ppow_pos (p := p) n).ne'])
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (ppow_pos (p := p) n).ne'] at hr
    exact mul_ne_zero (zpow_ne_zero k hπ) hw0 hr.symm
  have hr' : (r / s ^ k) ^ (p ^ n) = ι w := by
    rw [div_pow, hr, ← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, hs,
      mul_div_cancel_left₀ _ (zpow_ne_zero k hπ)]
  have hs' : s ^ (p ^ n) = ι (xn p n - 1) := by rw [hs, map_sub, hι.1, map_one]
  have hr0' : r / s ^ k ≠ 0 := div_ne_zero hr0 (zpow_ne_zero k hs0)
  obtain ⟨b, hb⟩ := exists_kum T n hs0 (fun g hg => by rw [hs', hfix g hg])
  obtain ⟨a', ha'⟩ := exists_kum T n hr0' (fun g hg => by rw [hr', hfix g hg])
  obtain ⟨x1, i1, e1⟩ := core hp2 hΩ T n hn ι hι w (w * α) (w * β) (by
    rw [hd, mul_left_comm, mul_left_comm (yn p n), mul_assoc, mul_assoc]) hr' ha' hz hq
  obtain ⟨x2, i2, e2⟩ := core hp2 hΩ T n hn ι hι (xn p n - 1) 0 (xn p n) (by
    simp [mul_comm]) hs' hb hz hq
  have hpπ : IsInt p ((p : Ω) / (T.ζ n - 1)) := by
    simpa using GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T n 1 hn (Nat.totient_pos.2 (ppow_pos n))
  have j1 := int_mul (int_nat (Ω := Ω) (p := p) p) (hI (↑w⁻¹ : On p n))
  have j2 := int_mul (int_int (Ω := Ω) (p := p) k) hpπ
  refine ⟨_, int_add (int_mul j1 i1) (int_mul j2 i2), fun g hg => ?_⟩
  obtain ⟨z1, l1, f1⟩ := e1 g hg
  obtain ⟨z2, l2, f2⟩ := e2 g hg
  have z0 := zeta_ne T n
  have hdvd : ((p ^ n : ℕ) : ℤ) ∣ ((a g).val : ℤ) - (a' g).val - k * (b g).val := by
    rw [← (T.prim n).zpow_eq_one_iff_dvd]
    have h1 := ha' g hg
    rw [map_div₀, map_zpow₀, ha g hg, hb g hg, mul_zpow, mul_div_mul_comm,
      mul_left_inj' hr0'] at h1
    rw [zpow_sub₀ z0, zpow_sub₀ z0, mul_comm k, zpow_mul]
    simp only [zpow_natCast]
    rw [div_right_comm, h1, div_self (pow_ne_zero _ z0)]
  obtain ⟨t, ht⟩ := hdvd
  have ht' : ((a g).val : Ω) - (a' g).val - k * (b g).val = (p : Ω) ^ n * t := by
    have := congrArg (Int.cast : ℤ → Ω) ht
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_pow, Int.cast_pow] using this
  refine ⟨_, int_add (int_add (int_mul j1 l1) (int_mul j2 l2))
    (int_mul (int_pow (int_nat p) 7) (int_int t)), ?_⟩
  simp only [map_add, map_sub, map_mul, map_div₀, map_natCast, map_intCast, map_one, map_zero,
    hfix g hg, hι.1, (mem_Gn.1 hg).1] at f1 f2 ⊢
  have hinv : (T.ζ n - 1) * (T.ζ n - 1)⁻¹ = 1 := mul_inv_cancel₀ hπ
  simp only [div_eq_mul_inv]
  generalize (T.ζ n - 1)⁻¹ = V at *
  linear_combination ((p : Ω) * ι (↑w⁻¹ : On p n)) * f1 + ((k : Ω) * (p * V)) * f2 + (p : Ω) ^ 7 * ht' -
    (p : Ω) ^ 7 * (((a' g).val : Ω) - ι α * ((lq g).val : Ω) - ι β * ((lz g).val : Ω)) * hww -
    (p : Ω) ^ 7 * k * ((b g).val : Ω) * hinv

end GlobalTheory.KumDlog
end
end

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCochain_eq_dlog_combination_finiteLevel : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k : ℤ) (w : (On p n)ˣ) (α β : On p n), IsDlog p n (w : On p n) α β →
  ∀ r : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w →
  ∀ a lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob1 n (Gn T n) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * ι α * ((lq g).val : Ω) -
      (p : Ω) ^ c * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) * ((lz g).val : Ω)) := by
  atlas_forward_decl GlobalTheory.KumDlog.kummer_eq_dlog
end
