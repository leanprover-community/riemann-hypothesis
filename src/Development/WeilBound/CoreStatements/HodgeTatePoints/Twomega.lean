module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Twomega

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT

section Complete

variable {p : ℕ} {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

theorem cong_iff {ι : Type} [Finite ι] (b : Module.Basis ι O M) (n : ℕ) (w w' : M) :
    (∃ u : M, w' = w + (p ^ n) • u) ↔ ∀ i, (p : O) ^ n ∣ b.equivFun w' i - b.equivFun w i := by
  constructor
  · rintro ⟨u, rfl⟩ i
    refine ⟨b.equivFun u i, ?_⟩
    rw [map_add (f := _), map_nsmul, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, add_sub_cancel_left]
  · intro h
    choose c hc using h
    refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
    rw [map_add (f := _), map_nsmul, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow,
      LinearEquiv.apply_symm_apply, ← hc, add_sub_cancel]

theorem smod_iff (n : ℕ) (a b : O) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔ (p : O) ^ n ∣ b - a := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    dvd_sub_comm]

theorem eq_zero_of_cong [Module.Free O M] [Module.Finite O M] (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
    (w : M) (h : ∀ n, ∃ u : M, w = 0 + (p ^ n) • u) : w = 0 := by
  let b := Module.Free.chooseBasis O M
  refine b.equivFun.injective (funext fun i => ?_)
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})).2 fun n => SModEq.symm ?_
  exact (smod_iff n _ _).2 ((cong_iff b n 0 w).1 (h n) i)

theorem exists_lim [Module.Free O M] [Module.Finite O M] (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
    (w : ℕ → M) (h : ∀ n, ∃ u : M, w (n + 1) = w n + (p ^ n) • u) :
    ∃ W : M, ∀ n, ∃ u : M, W = w n + (p ^ n) • u := by
  let b := Module.Free.chooseBasis O M
  have key : ∀ i, ∃ c : O, ∀ n, (p : O) ^ n ∣ c - b.equivFun (w n) i := by
    intro i
    have h1 : ∀ n, b.equivFun (w n) i ≡ b.equivFun (w (n + 1)) i
        [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] :=
      fun n => (smod_iff n _ _).2 ((cong_iff b n _ _).1 (h n) i)
    obtain ⟨c, hc⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => b.equivFun (w n) i)
      fun {m n} hmn => by
        induction n, hmn using Nat.le_induction with
        | base => rfl
        | succ n hmn ih =>
          exact ih.trans ((h1 n).mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)))
    exact ⟨c, fun n => (smod_iff n _ _).1 (hc n)⟩
  choose c hc using key
  exact ⟨b.equivFun.symm c, fun n => (cong_iff b n _ _).2 fun i => by
    rw [LinearEquiv.apply_symm_apply]; exact hc i n⟩

end Complete

variable {p : ℕ} {O : Type} [CommRing O] {La : Type} [AddCommGroup La]
  {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

theorem der_smul (n : ℕ) (r : O) (f : LevGrp La p n → O) (w : Module.Dual O L) (h : X.der n f w) :
    X.der n (r • f) (r • w) := by
  have := X.der_mul n _ _ _ _ (X.der_const n r) h
  rw [smul_zero, add_zero] at this
  exact this

theorem der_sub (n : ℕ) (f g : LevGrp La p n → O) (w w' : Module.Dual O L) (h : X.der n f w)
    (h' : X.der n g w') : X.der n (f - g) (w - w') := by
  have := X.der_add n _ _ _ _ h (der_smul X n (-1) g w' h')
  simpa only [neg_smul, one_smul, ← sub_eq_add_neg] using this

theorem der_of_mem_sq (n : ℕ) (f : X.A n) (hf : f ∈ BT.augIdeal (X.A n) ^ 2) : X.der n f.1 0 := by
  rw [sq] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨w, hw⟩ := X.der_ex n a.1 a.2
    obtain ⟨w', hw'⟩ := X.der_ex n b.1 b.2
    have ha0 : a.1 1 = 0 := ha
    have hb0 : b.1 1 = 0 := hb
    have := X.der_mul n _ _ _ _ hw hw'
    rw [ha0, hb0, zero_smul, zero_smul, add_zero] at this
    exact this
  · have := X.der_add n _ _ _ _ ha hb
    rw [add_zero] at this
    exact this

variable [Fact p.Prime] {X} {G : PDivGroup p O} {e : ∀ n, G.A n ≃ₐ[O] X.A n} {τ : La →+ G.Tate}

end PositivityTheory.HtPt.Twomega

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

