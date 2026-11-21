import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiGammaModelExtensionCocyclePair
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightSubquotientModelMemResidues
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChain
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CloseVectorNeZero
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesIndependentModCoboundariesLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt

section
section
noncomputable section
namespace GlobalTheory.PhiGam.QuotShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section lin
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

theorem mem_iSup_comap_pow (S : Module.End k U) (Q : Submodule k U) (hQ : ∀ q ∈ Q, S q ∈ Q) (p : U) :
    p ∈ ⨆ m : ℕ, Q.comap (S ^ m) ↔ ∃ m : ℕ, (S ^ m) p ∈ Q := by
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m y hy => ?_
    rw [Submodule.mem_comap, pow_succ', Module.End.mul_apply]
    exact hQ _ hy
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  rfl

theorem gmult_transport (T T' : Module.End k U) (e : U ≃ₗ[k] U) (P Q P' Q' : Submodule k U)
    (hP' : ∀ p, e p ∈ P' ↔ p ∈ P) (hQ' : ∀ p, e p ∈ Q' ↔ p ∈ Q)
    (hTP : ∀ p ∈ P, T p ∈ P) (hTQ : ∀ p ∈ Q, T p ∈ Q) (hTQ' : ∀ p ∈ Q', T' p ∈ Q') (x y : k)
    (h : ∀ p ∈ P, (T' (e p) - x • e p) - e (T p - y • p) ∈ Q') :
    gmult T' P' Q' x = gmult T P Q y := by
  set S := T - algebraMap k (Module.End k U) y with hS
  set S' := T' - algebraMap k (Module.End k U) x with hS'
  have hSa : ∀ p, S p = T p - y • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have hSa' : ∀ p, S' p = T' p - x • p := fun p => by simp [hS', Module.algebraMap_end_apply]
  have hSP : ∀ p ∈ P, S p ∈ P := fun p hp => by rw [hSa]; exact P.sub_mem (hTP p hp) (P.smul_mem _ hp)
  have hSQ : ∀ p ∈ Q, S p ∈ Q := fun p hp => by rw [hSa]; exact Q.sub_mem (hTQ p hp) (Q.smul_mem _ hp)
  have hSQ' : ∀ p ∈ Q', S' p ∈ Q' := fun p hp => by
    rw [hSa']; exact Q'.sub_mem (hTQ' p hp) (Q'.smul_mem _ hp)
  have key : ∀ p ∈ P, ∀ m : ℕ, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q' := by
    intro p hp m
    induction m with
    | zero => simpa using hp
    | succ m ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      refine ⟨hSP _ ih.1, ?_⟩
      have h1 := hSQ' _ ih.2
      have h2 := h _ ih.1
      rw [← hSa, ← hSa'] at h2
      have h3 := Q'.add_mem h1 h2
      rwa [map_sub, sub_add_sub_cancel] at h3
  have hmem : ∀ p, e p ∈ (P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)) ↔ p ∈ (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) := by
    intro p
    rw [Submodule.mem_inf, Submodule.mem_inf, mem_iSup_comap_pow S Q hSQ, mem_iSup_comap_pow S' Q' hSQ', hP']
    refine and_congr_right fun hp => exists_congr fun m => ?_
    rw [← hQ']
    have := (key p hp m).2
    constructor
    · intro h1; simpa using Q'.sub_mem h1 this
    · intro h1; simpa using Q'.add_mem this h1
  unfold gmult
  rw [← hS, ← hS']
  set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)
  set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)
  have hA : A.map (e : U →ₗ[k] U) = A' := by
    ext z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [hmem]
    exact Submodule.map_equiv_eq_comap_symm e A ▸ by simp
  let e' : A ≃ₗ[k] A' := e.ofSubmodules A A' hA
  refine (Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') e' ?_).finrank_eq.symm
  ext z
  obtain ⟨w, rfl⟩ := e'.surjective z
  have : (e' w ∈ Q'.submoduleOf A') ↔ w ∈ Q.submoduleOf A := hQ' w
  rw [this]
  exact Submodule.map_equiv_eq_comap_symm e' _ ▸ by simp

theorem fin_of_le {A B C : Submodule k U} (h : C ≤ B) (hf : FiniteDimensional k (A.map C.mkQ)) :
    FiniteDimensional k (A.map B.mkQ) := by
  have : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [this]; infer_instance

theorem fin_trans {A B C : Submodule k U} (h : C ≤ B) (h1 : FiniteDimensional k (A.map B.mkQ))
    (h2 : FiniteDimensional k (B.map C.mkQ)) : FiniteDimensional k (A.map C.mkQ) := by
  have e : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [e] at h1
  have hle : A.map C.mkQ ⊓ LinearMap.ker (Submodule.factor h) ≤ B.map C.mkQ := by
    rintro _ ⟨⟨a, -, rfl⟩, ha⟩
    exact ⟨a, (Submodule.Quotient.mk_eq_zero B).1 ha, rfl⟩
  have h3 := Submodule.finiteDimensional_of_le hle
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor h)
    (Module.Finite.iff_fg.1 h1) (Module.Finite.iff_fg.1 h3))

theorem fin_quot {A B : Submodule k U} (h : FiniteDimensional k (A.map B.mkQ)) :
    FiniteDimensional k (↥A ⧸ B.submoduleOf A) := by
  have e := LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at e
  exact e.symm.finiteDimensional

theorem gmult_self (T : Module.End k U) (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  rw [Submodule.submoduleOf_eq_top.2 inf_le_left]
  exact Module.finrank_zero_of_subsingleton

end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_sup_le {P Q : Submodule k⟦X⟧ V} {m : ℕ} (h : sh ((m + 1 : ℕ) : ℤ) P ≤ Q) :
    sh (m : ℤ) (Q ⊔ sh 1 P) ≤ Q := by
  have : sh (m : ℤ) (Q ⊔ sh 1 P) = sh (m : ℤ) Q ⊔ sh (m : ℤ) (sh 1 P) := Submodule.map_sup _ _ _
  rw [this, sh_sh_eq]
  refine sup_le ?_ (by exact_mod_cast h)
  simpa [sh_zero_eq] using sh_le_sh_of_le (Int.natCast_nonneg m) Q

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_one_le (P : Submodule k⟦X⟧ V) : sh 1 P ≤ P := by
  simpa [sh_zero_eq] using sh_le_sh_of_le (zero_le_one' ℤ) P

theorem fin_lat (m : ℕ) : ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → sh (m : ℤ) P ≤ Q →
    FiniteDimensional k ((P.restrictScalars k).map (Q.restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    intro P Q _ _ h
    have : (P.restrictScalars k).map (Q.restrictScalars k).mkQ = ⊥ := by
      rw [← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
      rw [Nat.cast_zero, sh_zero_eq] at h
      exact h
    rw [this]; infer_instance
  | succ m ih =>
    intro P Q hP hQ h
    refine fin_trans (B := (Q ⊔ sh 1 P).restrictScalars k) (fun y hy => Submodule.mem_sup_left hy) ?_
      (ih _ _ (hQ.sup (hP.map _)) hQ (sh_sup_le h))
    exact fin_of_le (fun y hy => Submodule.mem_sup_right hy) (Window.finite_quot hP)

theorem step {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {P Q : Submodule k⟦X⟧ V}
    (hP : CondC g P) (hQ : CondC g Q) (h : sh 1 P ≤ Q) (x : k) :
    qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  have hv := vv_ne_zero k
  let e : V ≃ₗ[k] V := (LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k) hv).restrictScalars k
  have he : ∀ p, e p = vv k • p := fun p => rfl
  have hN : ∀ (N : Submodule k⟦X⟧ V) p, e p ∈ (sh 1 N).restrictScalars k ↔ p ∈ N.restrictScalars k := by
    intro N p
    rw [Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, mem_sh_iff_smul_mem, he, smul_smul,
      zpow_neg_one, inv_mul_cancel₀ hv, one_smul]
  refine gmult_transport _ _ e _ _ _ _ (hN P) (hN Q) (fun p hp => Window.nab_mem hP hp)
    (fun p hp => Window.nab_mem hQ hp) (fun p hp => Window.nab_mem_sh R hg hQ 1 hp) _ _ fun p hp => ?_
  obtain ⟨n', hn', hs⟩ := Window.nab_shift R hg hP 1 hp
  rw [zpow_one, ← he, ← he] at hs
  rw [hs, ← map_smul, ← map_sub, ← map_sub, hN]
  have : nab g p - ((1 : ℤ) : k) • p + vv k • n' - x • p - (nab g p - (x + 1) • p) = vv k • n' := by
    rw [Int.cast_one, add_smul]; abel
  rw [this]
  exact h (mem_sh_iff_exists.2 ⟨n', hn', by rw [zpow_one]⟩)

theorem qmult_add (g : V →ₗ[k] V) (m : ℕ) {P Q S : Submodule k⟦X⟧ V} (hP : P.FG) (hS : S.FG) (h1 : S ≤ Q)
    (h2 : Q ≤ P) (cP : ∀ p ∈ P, nab g p ∈ P) (cQ : ∀ p ∈ Q, nab g p ∈ Q) (cS : ∀ p ∈ S, nab g p ∈ S)
    (h : sh (m : ℤ) P ≤ S) (x : k) : qmult g P S x = qmult g P Q x + qmult g Q S x :=
  GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k) (S.restrictScalars k) h1 h2 cP cQ cS
    (fin_quot (fin_lat m P S hP hS h)) x

theorem shift_of_le {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) (x : k) (m : ℕ) :
    ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → Q ≤ P → CondC g P → CondC g Q → sh (m : ℤ) P ≤ Q →
      qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  induction m with
  | zero =>
    intro P Q _ _ hle _ _ h
    rw [Nat.cast_zero, sh_zero_eq] at h
    rw [le_antisymm hle h, qmult, qmult, gmult_self, gmult_self]
  | succ m ih =>
    intro P Q hP hQ hle cP cQ h
    have hle' : Q ⊔ sh 1 P ≤ P := sup_le hle (sh_one_le P)
    have cQ' : CondC g (Q ⊔ sh 1 P) := by
      rw [condC_iff_nab_mem]
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add]
      exact Submodule.add_mem_sup (Window.nab_mem cQ ha) (Window.nab_mem_sh R hg cP 1 hb)
    have h' : sh ((m + 1 : ℕ) : ℤ) (sh 1 P) ≤ sh 1 Q := by
      rw [sh_sh_eq, add_comm, ← sh_sh_eq]; exact sh_le_sh 1 h
    have a1 := qmult_add g (m + 1) hP hQ (le_sup_left (b := sh 1 P)) hle' (fun p hp => Window.nab_mem cP hp)
      (fun p hp => Window.nab_mem cQ' hp) (fun p hp => Window.nab_mem cQ hp) h (x + 1)
    have a2 := qmult_add g (m + 1) (P := sh 1 P) (Q := sh 1 (Q ⊔ sh 1 P)) (S := sh 1 Q) (hP.map _) (hQ.map _)
      (sh_le_sh 1 le_sup_left) (sh_le_sh 1 hle') (fun p hp => Window.nab_mem_sh R hg cP 1 hp)
      (fun p hp => Window.nab_mem_sh R hg cQ' 1 hp) (fun p hp => Window.nab_mem_sh R hg cQ 1 hp) h' x
    rw [a1, a2, step R hg cP cQ' le_sup_right,
      ih (Q ⊔ sh 1 P) Q (hQ.sup (hP.map _)) hQ le_sup_left cQ' cQ (sh_sup_le h)]

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ x : k, qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hle cP cQ x
  obtain ⟨m, hm⟩ := Close.exists_pow hP.1 hQ.2
  exact shift_of_le R hg x m P Q hP.1 hQ.1 hle cP cQ (Close.sh_le hm)

end GlobalTheory.PhiGam.QuotShift
end
end

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMultiplicity_shift_lattice_quotient : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ x : k, qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  atlas_forward_decl GlobalTheory.PhiGam.QuotShift.main
end

section
section
noncomputable section
namespace GlobalTheory.PhiGam.Count
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

theorem exists_le_sup (P Q : Submodule k U) [FiniteDimensional k (P.map Q.mkQ)] :
    ∃ F : Submodule k U, FiniteDimensional k F ∧ P ≤ F ⊔ Q := by
  obtain ⟨σ, hσ⟩ := Q.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ Q)
  refine ⟨(P.map Q.mkQ).map σ, inferInstance, fun p hp => ?_⟩
  refine Submodule.mem_sup.2 ⟨σ (Q.mkQ p), ⟨_, ⟨p, hp, rfl⟩, rfl⟩, p - σ (Q.mkQ p), ?_, by abel⟩
  have h : Q.mkQ (σ (Q.mkQ p)) = Q.mkQ p := LinearMap.congr_fun hσ _
  exact (Submodule.Quotient.eq _).mp h.symm

theorem finite_of_le_sup {P Q F : Submodule k U} [FiniteDimensional k F] (h : P ≤ F ⊔ Q) :
    FiniteDimensional k (↥P ⧸ Q.submoduleOf P) := by
  have hker : LinearMap.ker (Q.mkQ ∘ₗ P.subtype) = Q.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hle : LinearMap.range (Q.mkQ ∘ₗ P.subtype) ≤ F.map Q.mkQ := by
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨f, hf, q, hq, rfl⟩ := Submodule.mem_sup.1 (h hp)
    refine ⟨f, hf, ?_⟩
    change Q.mkQ f = Q.mkQ (f + q)
    rw [map_add, show Q.mkQ q = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hq, add_zero]
  haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P.subtype)) :=
    Submodule.finiteDimensional_of_le hle
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_eq_zero (T : Module.End k U) {P Q M : Submodule k U} (hPM : P ≤ M) (hM : ∀ p ∈ M, T p ∈ M)
    (x : k) (h : ∀ p ∈ M, T p - x • p ∈ Q → p ∈ Q) (hQ : ∀ p ∈ Q, T p ∈ Q) : gmult T P Q x = 0 := by
  set S : Module.End k U := T - algebraMap k (Module.End k U) x with hS
  have hSa : ∀ p, S p = T p - x • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have key : ∀ m : ℕ, ∀ p ∈ M, (S ^ m) p ∈ Q → p ∈ Q := by
    intro m
    induction m with
    | zero => intro p _ hp; simpa using hp
    | succ m ih =>
      intro p hp hq
      rw [pow_succ, Module.End.mul_apply] at hq
      have h1 : S p ∈ M := by rw [hSa]; exact M.sub_mem (hM p hp) (M.smul_mem _ hp)
      exact h p hp (hSa p ▸ ih _ h1 hq)
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply, hSa]
    exact Q.sub_mem (hQ _ hp) (Q.smul_mem _ hp)
  have hle : P ⊓ ⨆ m : ℕ, Q.comap (S ^ m) ≤ Q := by
    rintro p ⟨hp, hq⟩
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 hq
    exact key m p (hPM hp) hm
  unfold gmult
  rw [← hS, Submodule.submoduleOf_eq_top.2 hle]
  exact Module.finrank_zero_of_subsingleton

end

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem exists_le_sup_sh {N : Submodule k⟦X⟧ V} (hN : IsLat N) (m : ℕ) :
    ∃ F : Submodule k V, FiniteDimensional k F ∧
      N.restrictScalars k ≤ F ⊔ (sh m N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp [sh_zero_eq]⟩
  | succ m ih =>
    obtain ⟨F, hF, h⟩ := ih
    haveI := Window.finite_quot (hN.shift m).1
    obtain ⟨F', hF', h'⟩ := exists_le_sup ((sh m N).restrictScalars k) ((sh 1 (sh m N)).restrictScalars k)
    rw [sh_sh_eq, add_comm] at h'
    refine ⟨F ⊔ F', inferInstance, h.trans ?_⟩
    rw [sup_assoc, Nat.cast_succ]
    exact sup_le_sup_left h' _

theorem graded_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (x : k) (h : sen g N (x + b) = 0) :
    ∀ y ∈ sh b N, nab g y - x • y ∈ sh (b + 1) N → y ∈ sh (b + 1) N := by
  haveI := Window.finite_quot hN
  obtain ⟨h1, -⟩ := Window.bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (x + b) h
  have hv : vv k ≠ 0 := vv_ne_zero k
  intro y hx hx'
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff_exists.mp hx
  obtain ⟨n', hn', e⟩ := Window.nab_shift R hg hC b hn
  obtain ⟨t, ht, e'⟩ := mem_sh_iff_exists.mp hx'
  have hc : x • vv k ^ b • n = vv k ^ b • x • n := by
    rw [← smul_assoc, const_smul_eq, mul_comm, mul_smul, ← mul_one (algebraMap k k⸨X⸩ x), ← const_smul_eq,
      smul_assoc, one_smul]
  rw [e, hc, zpow_add_one₀ hv, mul_smul, ← smul_sub] at e'
  have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
  have : n ∈ sh 1 N := h1 n hn (mem_sh_iff_exists.mpr ⟨t - n', N.sub_mem ht hn', by
    rw [zpow_one, smul_sub, e2, add_smul]; abel⟩)
  obtain ⟨r, hr, rfl⟩ := mem_sh_iff_exists.mp this
  exact mem_sh_iff_exists.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩

theorem window_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (x : k) (s : ℕ) (h : ∀ j : ℕ, 1 ≤ j → j ≤ s → sen g N (x - j) = 0) :
    ∀ y ∈ sh (-s) N, nab g y - x • y ∈ N → y ∈ N := by
  induction s with
  | zero => intro y hy _; simpa [sh_zero_eq] using hy
  | succ s ih =>
    intro y hy hy'
    refine ih (fun j h1 h2 => h j h1 (Nat.le_succ_of_le h2)) y ?_ hy'
    have e : (-((s + 1 : ℕ) : ℤ)) + 1 = -(s : ℤ) := by push_cast; ring
    have := graded_inj R hg hN hC (-((s + 1 : ℕ) : ℤ)) x (by
      rw [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg]; exact h _ (Nat.succ_pos s) le_rfl) y hy
    rw [e] at this
    refine this (sh_le_sh_of_le (a := 0) (by omega) N ?_)
    rwa [sh_zero_eq]

theorem sen_count : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ s : ℕ, P ≤ sh (-s) Q → ∀ x : k, sen g P x + qmult g P Q (x + 1) = sen g Q x + qmult g P Q x ∧ (qmult g P Q x ≠ 0 → ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ sen g Q (x - j) ≠ 0) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hQP cP cQ s hs x
  constructor
  · have h1 : ∀ N : Submodule k⟦X⟧ V, sh 1 N ≤ N := fun N => by
      have := sh_le_sh_of_le (a := 1) (b := 0) (by norm_num) N
      rwa [sh_zero_eq] at this
    obtain ⟨F, hF, hle⟩ := exists_le_sup_sh hP (s + 1)
    have h2 : sh ((s + 1 : ℕ) : ℤ) P ≤ sh 1 Q := by
      have := sh_le_sh ((s + 1 : ℕ) : ℤ) hs
      rwa [sh_sh_eq, show ((s + 1 : ℕ) : ℤ) + -(s : ℤ) = 1 by push_cast; ring] at this
    have hfin : FiniteDimensional k (↥(P.restrictScalars k) ⧸
        ((sh 1 Q).restrictScalars k).submoduleOf (P.restrictScalars k)) :=
      finite_of_le_sup (F := F) (hle.trans (sup_le_sup_left (fun _ hy => h2 hy) _))
    have a1 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) ((sh 1 P).restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => sh_le_sh 1 hQP hy) (fun _ hy => h1 P hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem_sh R hg cP 1 hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    have a2 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => h1 Q hy) (fun _ hy => hQP hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem cQ hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    rw [← GlobalTheory.T.quotientMultiplicity_shift_lattice_quotient R g hg P Q hP hQ hQP cP cQ x]
    unfold sen qmult
    omega
  · intro hne
    by_contra hno
    push Not at hno
    exact hne (gmult_eq_zero (nab g) (M := (sh (-s) Q).restrictScalars k) (fun _ hy => hs hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ _ hy) x (window_inj R hg hQ.1 cQ x s hno)
      (fun _ hy => Window.nab_mem cQ hy))

end GlobalTheory.PhiGam.Count
end
end

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senMultiplicity_lattice_count_relation : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ s : ℕ, P ≤ sh (-s) Q → ∀ x : k, sen g P x + qmult g P Q (x + 1) = sen g Q x + qmult g P Q x ∧ (qmult g P Q x ≠ 0 → ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ sen g Q (x - j) ≠ 0) := by
  atlas_forward_decl GlobalTheory.PhiGam.Count.sen_count
end

section
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.ModelCount

theorem telescope (S S₀ m : ℤ → ℕ) (h : ∀ y, S y + m (y + 1) = S₀ y + m y) (a : ℤ) (L : ℕ) :
    ∑ j ∈ Finset.range L, S (a + j) + m (a + L) = ∑ j ∈ Finset.range L, S₀ (a + j) + m a := by
  induction L with
  | zero => simp
  | succ L ih =>
    have step := h (a + L)
    have e : a + ((L + 1 : ℕ) : ℤ) = a + L + 1 := by push_cast; ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, e]
    omega

theorem eq_of_cast_eq {k : Type} [Field k] (l : ℕ) [CharP k l] {u y : ℤ} (h : (u : k) = (y : k))
    (h1 : u - y < l) (h2 : y - u < l) : u = y := by
  have hd : (l : ℤ) ∣ y - u := ((CharP.intCast_eq_intCast k l).mp h).dvd
  have hz : y - u = 0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

theorem sum_resCount {k : Type} [Field k] (U : Multiset ℤ) (w a : ℤ) (L : ℕ) (p : ℤ → Prop) [DecidablePred p]
    (h : ∀ u ∈ U, (p u → a ≤ u ∧ u < a + L) ∧
      ∀ y : ℤ, a ≤ y → y < a + L → (u : k) = (y : k) → u = y ∧ p u) :
    ∑ j ∈ Finset.range L, resCount U w ((a + j - w : ℤ) : k) = Multiset.card (U.filter p) := by
  classical
  induction U using Multiset.induction_on with
  | empty => simp [resCount]
  | cons u U ih =>
    have hU := ih (fun v hv => h v (Multiset.mem_cons_of_mem hv))
    have hu := h u (Multiset.mem_cons_self u U)
    have split : ∀ x : k, resCount (u ::ₘ U) w x =
        (if ((u - w : ℤ) : k) = x then 1 else 0) + resCount U w x := by
      intro x
      unfold resCount
      rw [Multiset.filter_cons, Multiset.card_add]
      split_ifs <;> simp
    simp only [split]
    rw [Finset.sum_add_distrib, hU, Multiset.filter_cons, Multiset.card_add]
    congr 1
    have tr : ∀ j : ℕ, (((u - w : ℤ) : k) = ((a + j - w : ℤ) : k)) ↔ ((u : k) = ((a + j : ℤ) : k)) := by
      intro j
      push_cast
      exact sub_left_inj
    by_cases hp : p u
    · rw [if_pos hp, Multiset.card_singleton]
      obtain ⟨ha, hb⟩ := hu.1 hp
      rw [Finset.sum_eq_single (u - a).toNat]
      · rw [if_pos]
        rw [tr]
        congr 1
        omega
      · intro j _ hj
        rw [if_neg]
        intro hc
        have := (hu.2 (a + j) (by omega) (by have := Finset.mem_range.mp ‹j ∈ Finset.range L›; omega) ((tr j).mp hc)).1
        omega
      · intro hn
        exfalso
        exact hn (Finset.mem_range.mpr (by omega))
    · rw [if_neg hp, Multiset.card_zero]
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro hc
      have hj' := Finset.mem_range.mp hj
      exact hp (hu.2 (a + j) (by omega) (by omega) ((tr j).mp hc)).2

theorem exists_of_resCount_ne {k : Type} [Field k] {U : Multiset ℤ} {w : ℤ} {x : k} (h : resCount U w x ≠ 0) :
    ∃ u ∈ U, ((u - w : ℤ) : k) = x := by
  classical
  unfold resCount at h
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero h)
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

theorem count : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ N : Lats k n M.T.m, M.Model M.T N → (∀ i, M.Nstd i ≤ N i) → ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen ((F.D M.T).γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) = r) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 N hN hle i
  have hNabc := (GlobalTheory.T.obj_and_abc_of_model F M M.T N hN).2
  have hSabc := (GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model).2
  have hs : Dt.sg l i = GlobalTheory.PhiGam.sg l Dt.h i := rfl
  have hsh := GlobalTheory.T.phiGamma_lattice_families_shift_inclusion (F.D M.T) Dt.h Dt.w N M.Nstd hNabc.1 hSabc.1 hNabc.2.1 hSabc.2.1 i
  rw [← hs] at hsh
  have hP : N i ≤ sh (-(Dt.sg l i : ℤ)) (M.Nstd i) := by
    have h' := sh_le_sh (-(Dt.sg l i : ℤ)) hsh
    rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h'
  have tel := fun y : ℤ => GlobalTheory.T.senMultiplicity_lattice_count_relation R ((F.D M.T).γ i) ((F.D M.T).γ_semi i) (N i) (M.Nstd i)
    (hNabc.1 i) (hSabc.1 i) (hle i) (hNabc.2.2 i) (hSabc.2.2 i) (Dt.sg l i) hP (y : k)
  have rel : ∀ y : ℤ, sen ((F.D M.T).γ i) (N i) (y : k) + qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((y + 1 : ℤ) : k) =
      sen ((F.D M.T).γ i) (M.Nstd i) (y : k) + qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k) := by
    intro y
    rw [Int.cast_add, Int.cast_one]
    exact (tel y).1
  have mz : ∀ y : ℤ, qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k) ≠ 0 →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ Dt.sg l i ∧ ∃ u ∈ Dt.U i, (u : k) = ((y - j + Dt.w i : ℤ) : k) := by
    intro y hy
    obtain ⟨j, hj1, hj2, hj⟩ := (tel y).2 hy
    rw [M.std_sen] at hj
    obtain ⟨u, hu, hux⟩ := exists_of_resCount_ne hj
    refine ⟨j, hj1, hj2, u, hu, ?_⟩
    push_cast at hux ⊢
    linear_combination hux
  have sz : ∀ y : ℤ, sen ((F.D M.T).γ i) (N i) (y : k) ≠ 0 → ∃ u ∈ Dt.U i, (u : k) = ((y + Dt.w i : ℤ) : k) := by
    intro y hy
    obtain ⟨u, hu, hux⟩ := GlobalTheory.T.senWeight_subquotient_model_mem_residues F M h1 h2 h3 M.T M.T LinearMap.id LinearMap.id N (fun _ _ => rfl)
      (fun _ _ hab => hab) (fun _ _ => rfl) (fun b => ⟨b, rfl⟩) hN i (y : k) hy
    refine ⟨u, hu, ?_⟩
    push_cast at hux ⊢
    linear_combination hux
  obtain ⟨-, hwin, hG, hB⟩ := GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt h1 h2 h3 i
  have hT1 := h1 i
  have ht := Dt.one_le_letterBlockLength
  have e1 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((0 : ℤ) : k) = 0 := by
    by_contra hne
    obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz 0 hne
    exact hwin u hu _ (by omega) (by omega) hux
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    by_contra hne
    obtain ⟨u, hu, hux⟩ := sz a (by simpa using hne)
    exact hwin u hu _ (by omega) (by omega) hux
  · intro hG'
    obtain ⟨hGU, hGc, hw1, hwt⟩ := hG hG'
    have hL : ((Dt.w i).toNat : ℤ) = Dt.w i := Int.toNat_of_nonneg (by omega)
    have tl := telescope (fun y => sen ((F.D M.T).γ i) (N i) (y : k)) (fun y => sen ((F.D M.T).γ i) (M.Nstd i) (y : k))
      (fun y => qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k)) rel (-Dt.w i) (Dt.w i).toNat
    have e0 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((-Dt.w i + ((Dt.w i).toNat : ℤ) : ℤ) : k) = 0 := by
      rw [hL, neg_add_cancel]
      exact e1
    have e2 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((-Dt.w i : ℤ) : k) = 0 := by
      by_contra hne
      obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz (-Dt.w i) hne
      exact hGU u hu _ (by omega) (by omega) hux
    have hsum := sum_resCount (k := k) (Dt.U i) (Dt.w i) 0 (Dt.w i).toNat (· < Dt.w i) (by
      intro u hu
      have hr := Dt.range i u (Multiset.mem_add.mpr (Or.inl hu))
      refine ⟨fun _ => ⟨by omega, by omega⟩, fun y hy0 hyL hc => ?_⟩
      rcases Multiset.mem_add.mp hu with hlow | hcl
      · have hb := Dt.lowG i hG' u (Multiset.mem_add.mpr (Or.inl hlow))
        have hy := eq_of_cast_eq l hc (by omega) (by omega)
        exact ⟨hy, by omega⟩
      · exact absurd hc (hGc u hcl y hy0 (by omega)))
    have e3 : ∀ j : ℕ, ((0 : ℤ) + (j : ℤ) - Dt.w i) = -Dt.w i + j := fun j => by ring
    simp only [e3] at hsum
    have hsum' : ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (M.Nstd i) ((-Dt.w i + j : ℤ) : k) = Dt.d i := by
      change _ = Multiset.card ((Dt.U i).filter (· < Dt.w i))
      rw [← hsum]
      exact Finset.sum_congr rfl (fun j _ => M.std_sen i _)
    rw [e0, e2, hsum'] at tl
    omega
  · intro hB'
    obtain ⟨hBU, hBc, htw, hwη⟩ := hB hB'
    have hwst : Dt.wst i = (Dt.h i : ℤ) - Dt.w i := rfl
    have hL : ((Dt.wst i).toNat : ℤ) = Dt.wst i := Int.toNat_of_nonneg (by omega)
    have tl := telescope (fun y => sen ((F.D M.T).γ i) (N i) (y : k)) (fun y => sen ((F.D M.T).γ i) (M.Nstd i) (y : k))
      (fun y => qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k)) rel 0 ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1))
    have e0 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i)
        (((0 : ℤ) + (((Dt.wst i).toNat + 1 + (Dt.sg l i + 1) : ℕ) : ℤ) : ℤ) : k) = 0 := by
      by_contra hne
      obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz _ hne
      exact hBU u hu _ (by push_cast; omega) (by push_cast; omega) hux
    rw [e0, e1, Finset.sum_range_add] at tl
    have hz : ∑ j ∈ Finset.range (Dt.sg l i + 1),
        sen ((F.D M.T).γ i) (N i) (((0 : ℤ) + (((Dt.wst i).toNat + 1 + j : ℕ) : ℤ) : ℤ) : k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      by_contra hne
      obtain ⟨u, hu, hux⟩ := sz _ hne
      exact hBU u hu _ (by push_cast; omega) (by push_cast; omega) hux
    rw [hz] at tl
    have hsum := sum_resCount (k := k) (Dt.U i) (Dt.w i) (Dt.w i) ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1))
      (fun u => ¬ u < Dt.w i) (by
      intro u hu
      have hr := Dt.range i u (Multiset.mem_add.mpr (Or.inl hu))
      refine ⟨fun _ => ⟨by omega, by push_cast; omega⟩, fun y hy0 hyL hc => ?_⟩
      push_cast at hyL
      rcases Multiset.mem_add.mp hu with hlow | hcl
      · have hb := Dt.lowBd i hB' u (Multiset.mem_add.mpr (Or.inl hlow))
        have hy := eq_of_cast_eq l hc (by omega) (by omega)
        exact ⟨hy, by omega⟩
      · by_cases hyh : y ≤ (Dt.h i : ℤ)
        · exact absurd hc (hBc u hcl y (by omega) hyh)
        · exact absurd hc (hBU u (Multiset.mem_add.mpr (Or.inr hcl)) y (by omega) (by omega)))
    have e3 : ∀ j : ℕ, (Dt.w i + (j : ℤ) - Dt.w i) = 0 + j := fun j => by ring
    simp only [e3] at hsum
    have hsum' : ∑ j ∈ Finset.range ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1)),
        sen ((F.D M.T).γ i) (M.Nstd i) (((0 : ℤ) + j : ℤ) : k) = Multiset.card ((Dt.U i).filter (fun u => ¬ u < Dt.w i)) := by
      rw [← hsum]
      exact Finset.sum_congr rfl (fun j _ => M.std_sen i _)
    rw [hsum'] at tl
    have hfirst : ∑ j ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (((0 : ℤ) + j : ℤ) : k) =
        ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp
    have hsplit := congrArg Multiset.card (Multiset.filter_add_not (· < Dt.w i) (Dt.U i))
    rw [Multiset.card_add] at hsplit
    have hU : Multiset.card (Dt.U i) = r := Dt.card_eq i
    have hd : Dt.d i = Multiset.card ((Dt.U i).filter (· < Dt.w i)) := rfl
    rw [hfirst] at tl
    omega

end GlobalTheory.ModelCount
end

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPhiGammaModel_sen_weight_count : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ N : Lats k n M.T.m, M.Model M.T N → (∀ i, M.Nstd i ≤ N i) → ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen ((F.D M.T).γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) = r) := by
  atlas_forward_decl GlobalTheory.ModelCount.count
end

section
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SupModel

variable {k G : Type} [Field k] [Group G]

theorem isHom_comp {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) :=
  fun s x => by simp only [LinearMap.comp_apply]; rw [hf, hg]

theorem isHom_add {A B : Ob k G} {f g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    (hf : IsHom A B f) (hg : IsHom A B g) : IsHom A B (f + g) :=
  fun s x => by simp only [LinearMap.add_apply, map_add]; rw [hf, hg]

theorem exists_sum (A B : Ob k G) : ∃ (C : Ob k G) (i : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), IsHom A C i ∧ IsHom B C j ∧ Function.Bijective (i.coprod j) := by
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.prod B.ρ)
  refine ⟨C, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e.toLinearMap ∘ₗ LinearMap.inr k _ _, ?_, ?_, ?_⟩
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · have : (e.toLinearMap ∘ₗ LinearMap.inl k _ _).coprod (e.toLinearMap ∘ₗ LinearMap.inr k _ _)
        = e.toLinearMap := by
      rw [← LinearMap.comp_coprod, LinearMap.coprod_inl_inr, LinearMap.comp_id]
    rw [this]; exact e.bijective

theorem exists_proj {A B C : Ob k G} {i : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    {j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hi : IsHom A C i) (hj : IsHom B C j)
    (hb : Function.Bijective (i.coprod j)) :
    ∃ (π : (Fin C.m → k) →ₗ[k] (Fin A.m → k)) (π' : (Fin C.m → k) →ₗ[k] (Fin B.m → k)),
      IsHom C A π ∧ IsHom C B π' ∧ (∀ x, π (i x) = x) ∧ (∀ x, π (j x) = 0) ∧ (∀ x, π' (i x) = 0) ∧
      (∀ x, π' (j x) = x) ∧ ∀ x, i (π x) + j (π' x) = x := by
  let e := LinearEquiv.ofBijective _ hb
  have h1 : ∀ x y, e.symm (i x + j y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; simp [e]
  have h2 : ∀ x, i (e.symm x).1 + j (e.symm x).2 = x := fun x => by
    exact e.apply_symm_apply x
  have h3 : ∀ g x, e.symm (C.ρ g x) = (A.ρ g (e.symm x).1, B.ρ g (e.symm x).2) := fun g x => by
    rw [← h1, hi, hj, ← map_add, h2]
  refine ⟨LinearMap.fst k _ _ ∘ₗ e.symm.toLinearMap, LinearMap.snd k _ _ ∘ₗ e.symm.toLinearMap,
    fun g x => ?_, fun g x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => h2 x⟩
  · simp [h3]
  · simp [h3]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]

variable {l n : ℕ} {R : RingPG k l}

theorem map_comp_apply (F : DFun R n G) {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} {h : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    (hA : F.Obj A) (hB : F.Obj B) (hC : F.Obj C) (hf : IsHom A B f) (hg : IsHom B C g)
    (hh : ∀ x, g (f x) = h x) (i : ZMod n) (x : Vc k A.m) :
    F.map B C g i (F.map A B f i x) = F.map A C h i x := by
  have : h = g ∘ₗ f := LinearMap.ext fun x => (hh x).symm
  rw [this, F.map_comp A B C f g hA hB hC hf hg]; rfl

theorem map_zero' (F : DFun R n G) {A B : Ob k G} (hA : F.Obj A) (hB : F.Obj B) (i : ZMod n) (x : Vc k A.m) :
    F.map A B 0 i x = 0 := by
  have := F.map_smul A B 0 0 hA hB (fun g x => by simp) i x
  simpa using this

theorem model_sup : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N N' : Lats k n A.m), M.Model A N → M.Model A N' → M.Model A (fun i => N i ⊔ N' i) := by
  intro k G _ _ l n _ _ _ R F r Dt M A N N' hN hN'
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨B', Nb', A₂, j', p', hB', hj', hji', hp', hps', rfl⟩ := hN'
  obtain ⟨C, i, i', hi, hi', hb, hC⟩ := M.base_sum B Nb B' Nb' hB hB'
  obtain ⟨π, π', hπ, hπ', e1, e2, e3, e4, -⟩ := exists_proj hi hi' hb
  obtain ⟨S, a, a', ha, ha', hab⟩ := exists_sum A₁ A₂
  obtain ⟨q, q', hq, hq', d1, d2, d3, d4, d5⟩ := exists_proj ha ha' hab
  have oB := M.base_obj _ _ hB
  have oB' := M.base_obj _ _ hB'
  have oC := M.base_obj _ _ hC
  have o1 := F.obj_sub _ _ _ hj hji oB
  have o2 := F.obj_sub _ _ _ hj' hji' oB'
  have oS := F.obj_sum _ _ _ _ _ ha ha' hab.2 o1 o2
  have oA := F.obj_quot _ _ _ hp hps o1
  have hJ : IsHom S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') :=
    isHom_add (isHom_comp (isHom_comp hq hj) hi) (isHom_comp (isHom_comp hq' hj') hi')
  have hP : IsHom S A (p ∘ₗ q + p' ∘ₗ q') := isHom_add (isHom_comp hq hp) (isHom_comp hq' hp')
  refine ⟨C, _, S, _, _, hC, hJ, ?_, hP, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := congrArg π hx
    have h2 := congrArg π' hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, e1, e2, e3, e4, map_zero, add_zero,
      zero_add] at h1 h2
    have h1' : q x = 0 := hji (by simpa using h1)
    have h2' : q' x = 0 := hji' (by simpa using h2)
    rw [← d5 x, h1', h2']; simp
  · intro y
    obtain ⟨x, rfl⟩ := hps y
    exact ⟨a x, by simp [d1, d3]⟩
  · funext t
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₁ S a t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₁ S a t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i ∘ₗ j) o1 oS oC ha hJ (fun x => by simp [d1, d3]),
            ← map_comp_apply F o1 oB oC hj hi (fun _ => rfl)]
          exact Submodule.mem_sup_left ⟨_, hy, rfl⟩
        · exact map_comp_apply F o1 oS oA ha hP (fun x => by simp [d1, d3]) t y
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₂ S a' t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₂ S a' t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i' ∘ₗ j') o2 oS oC ha' hJ (fun x => by simp [d2, d4]),
            ← map_comp_apply F o2 oB' oC hj' hi' (fun _ => rfl)]
          exact Submodule.mem_sup_right ⟨_, hy, rfl⟩
        · exact map_comp_apply F o2 oS oA ha' hP (fun x => by simp [d2, d4]) t y
    · rintro _ ⟨s, hs, rfl⟩
      change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t s ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t at hs
      obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨u', hu', rfl⟩, h⟩ := Submodule.mem_sup.1 hs
      change F.map B C i t u + F.map B' C i' t u' = _ at h
      have h1 := congrArg (F.map C B π t) h
      have h2 := congrArg (F.map C B' π' t) h
      rw [map_add, map_comp_apply F (h := LinearMap.id) oB oC oB hi hπ e1,
        map_comp_apply F (h := 0) oB' oC oB hi' hπ e2, F.map_id B oB, map_zero' F oB' oB,
        map_comp_apply F (h := j ∘ₗ q) oS oC oB hJ hπ (fun x => by simp [e1, e2]),
        ← map_comp_apply F oS o1 oB hq hj (fun _ => rfl), add_zero, LinearMap.id_apply] at h1
      rw [map_add, map_comp_apply F (h := LinearMap.id) oB' oC oB' hi' hπ' e4,
        map_comp_apply F (h := 0) oB oC oB' hi hπ' e3, F.map_id B' oB', map_zero' F oB oB',
        map_comp_apply F (h := j' ∘ₗ q') oS oC oB' hJ hπ' (fun x => by simp [e3, e4]),
        ← map_comp_apply F oS o2 oB' hq' hj' (fun _ => rfl), zero_add, LinearMap.id_apply] at h2
      change F.map S A _ t s ∈ _
      rw [F.map_add S A _ _ oS oA (isHom_comp hq hp) (isHom_comp hq' hp'),
        ← map_comp_apply F oS o1 oA hq hp (fun _ => rfl), ← map_comp_apply F oS o2 oA hq' hp' (fun _ => rfl)]
      refine Submodule.add_mem_sup ⟨_, ?_, rfl⟩ ⟨_, ?_, rfl⟩
      · change F.map A₁ B j t _ ∈ Nb t
        rw [← h1]; exact hu
      · change F.map A₂ B' j' t _ ∈ Nb' t
        rw [← h2]; exact hu'

end GlobalTheory.Models.SupModel
end

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_sup_alt : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N N' : Lats k n A.m), M.Model A N → M.Model A N' → M.Model A (fun i => N i ⊔ N' i) := by
  atlas_forward_decl GlobalTheory.Models.SupModel.model_sup
end

section
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem exists_greatest_of_sup_closed {S V ι : Type} [CommRing S] [IsNoetherianRing S] [AddCommGroup V]
    [Module S V] [Finite ι] (C : (ι → Submodule S V) → Prop) (P N₀ : ι → Submodule S V) (h₀ : C N₀)
    (hP : ∀ i, (P i).FG) (hle : ∀ N, C N → ∀ i, N i ≤ P i)
    (hsup : ∀ N N', C N → C N' → C (fun i => N i ⊔ N' i)) :
    ∃ N, C N ∧ ∀ N', C N' → ∀ i, N' i ≤ N i := by
  classical
  have one : ∀ i, ∃ N, C N ∧ ∀ N', C N' → N' i ≤ N i := by
    intro i
    haveI : IsNoetherian S (P i) := isNoetherian_of_fg_of_noetherian _ (hP i)
    obtain ⟨_, ⟨N, hN, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 this
      {Q : Submodule S (P i) | ∃ N, C N ∧ (N i).comap (P i).subtype = Q} ⟨_, N₀, h₀, rfl⟩
    refine ⟨N, hN, fun N' hN' x hx => ?_⟩
    have h1 := hmax _ ⟨_, hsup N N' hN hN', rfl⟩
    have h2 : (N i).comap (P i).subtype = (N i ⊔ N' i).comap (P i).subtype :=
      (Submodule.comap_mono le_sup_left).eq_of_not_lt h1
    have h3 : (⟨x, hle N' hN' i hx⟩ : P i) ∈ (N i ⊔ N' i).comap (P i).subtype :=
      Submodule.mem_sup_right hx
    rw [← h2] at h3
    exact h3
  have all : ∀ s : Finset ι, ∃ N, C N ∧ ∀ N', C N' → ∀ i ∈ s, N' i ≤ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨N₀, h₀, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨N, hN, h⟩ := ih
      obtain ⟨N₁, hN₁, h₁⟩ := one a
      refine ⟨_, hsup N N₁ hN hN₁, fun N' hN' i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_sup_of_le_right (h₁ N' hN')
      · exact le_sup_of_le_left (h N' hN' i hi)
  haveI := Fintype.ofFinite ι
  obtain ⟨N, hN, h⟩ := all Finset.univ
  exact ⟨N, hN, fun N' hN' i => h N' hN' i (Finset.mem_univ i)⟩

theorem exists_largest_model : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N₀ : Lats k n A.m), M.Model A N₀ → ∃ N, M.Model A N ∧ ∀ N', M.Model A N' → ∀ i, N' i ≤ N i := by
  intro k G _ _ l n _ _ _ R F r Dt M A N₀ h₀
  obtain ⟨-, hl₀, hab₀, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M A N₀ h₀
  refine exists_greatest_of_sup_closed (fun N => M.Model A N)
    (fun i => sh (-(sg l Dt.h i : ℤ)) (N₀ i)) N₀ h₀ (fun i => ((hl₀ i).shift _).1) (fun N hN i => ?_)
    (fun N N' => GlobalTheory.T.model_sup_alt F M A N N')
  obtain ⟨-, hl, hab, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M A N hN
  have h := sh_le_sh (-(sg l Dt.h i : ℤ)) (GlobalTheory.T.phiGamma_lattice_families_shift_inclusion (F.D A) Dt.h Dt.w N N₀ hl hl₀ hab hab₀ i)
  rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h

end GlobalTheory.Models
end

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_largest_model' : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N₀ : Lats k n A.m), M.Model A N₀ → ∃ N, M.Model A N ∧ ∀ N', M.Model A N' → ∀ i, N' i ≤ N i := by
  atlas_forward_decl GlobalTheory.Models.exists_largest_model
end

section
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.AdmBound

theorem inZZ_mono {k : Type} [Field k] {l n m r : ℕ} {R : RingPG k l} (D : ModPG R n (Vc k m)) (Dt : TopData n r)
    {N N' : Lats k n m} (h : ∀ i, N i ≤ N' i) {b g : ZMod n → Vc k m} (hz : InZZ D Dt N b g) :
    InZZ D Dt N' b g := by
  intro i
  obtain ⟨h0, h1, h2, h3⟩ := hz i
  refine ⟨h0, sh_le_sh 1 (h i) h1, fun hG => sh_le_sh _ (h i) (h2 hG), fun hB => ?_⟩
  obtain ⟨hb, x, hx, hx'⟩ := h3 hB
  exact ⟨sh_le_sh _ (pull_le_pull _ (h (i - 1))) hb, x, h i hx, sh_le_sh _ (h i) hx'⟩

theorem repr_sum {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {ι : Type} (z : ι → G → Fin A.m → k)
    (b g : ι → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a)) (a₀ : ι) (c : ι → k) (t : Finset ι) :
    Repr F A (∑ a ∈ t, c a • z a) (∑ a ∈ t, c a • b a) (∑ a ∈ t, c a • g a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 := GlobalTheory.T.repr_smul_add F A (-1) (z a₀) (z a₀) (b a₀) (g a₀) (b a₀) (g a₀) (h a₀) (h a₀)
    simpa only [neg_one_smul, neg_add_cancel, Finset.sum_empty] using h0
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.repr_smul_add F A (c a) (z a) _ (b a) (g a) _ _ (h a) ih

theorem indep_pairs {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {s : ℕ} (z : Fin s → G → Fin A.m → k)
    (b g : Fin s → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a))
    (hz : LinearIndependent k (fun a => (cob A).mkQ (z a))) :
    LinearIndependent k (fun a => (herrB (F.D A)).mkQ (b a, g a)) := by
  classical
  rw [linearIndependent_iff'] at hz ⊢
  intro t c hc a ha
  have e1 : ∑ a ∈ t, c a • (herrB (F.D A)).mkQ (b a, g a) =
      (herrB (F.D A)).mkQ (∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) := by
    rw [show ((∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) : (ZMod n → Vc k A.m) × (ZMod n → Vc k A.m)) =
        ∑ a ∈ t, c a • (b a, g a) by ext <;> simp [Prod.fst_sum, Prod.snd_sum]]
    simp only [map_sum, map_smul]
  rw [e1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
  have hcob := GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F A _ _ _ (repr_sum F A z b g h a c t) hc
  refine hz t c ?_ a ha
  have e2 : ∑ a ∈ t, c a • (cob A).mkQ (z a) = (cob A).mkQ (∑ a ∈ t, c a • z a) := by
    simp only [map_sum, map_smul]
  rw [e2, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hcob

private theorem exists_ne_zero_smul_mem_of_mem_span' (hψ : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi) {k : Type} [Field k] {l n m r : ℕ} [Fact l.Prime]
    [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n r)
    (N : Lats k n m) (hr : m = r) (hc : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (h1 : Dt.T1 l) (h2 : Dt.T2 l)
    (h3 : Dt.T3 l) (habc : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧
      (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧
      (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = r ∧
        EPoly (D.γ i) (N i) (Dt.wst i + 1)))
    (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : ∀ a, InZZ D Dt N (z a).1 (z a).2)
    (hind : LinearIndependent k (fun a => (herrB D).mkQ (z a))) : s ≤ Dt.dsum := by
  subst hr
  exact GlobalTheory.T.card_cocycles_independent_mod_coboundaries_le hψ D ι Dt N hc h1 h2 h3 habc hsen s z hz hind

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (s : ℕ) (z : Fin s → G → Fin M.T.m → k), (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) → LinearIndependent k (fun a => (cob M.T).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hψ k G _ _ l n _ _ _ R F r Dt M ι hc h1 h2 h3 s z hz hind
  choose N b g hN hR hZ using fun a => GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 M.T (z a) (hz a)
  obtain ⟨Nm, hNm, hmax⟩ := GlobalTheory.T.exists_largest_model' F M M.T M.Nstd M.std_model
  have hS := GlobalTheory.T.twistedPhiGammaModel_sen_weight_count F M h1 h2 h3 Nm hNm (hmax _ M.std_model)
  refine exists_ne_zero_smul_mem_of_mem_span' hψ (F.D M.T) ι Dt Nm M.T_m hc h1 h2 h3 (GlobalTheory.T.obj_and_abc_of_model F M M.T Nm hNm).2
    (fun i => ⟨(hS i).1, (hS i).2.1, fun hB => ⟨(hS i).2.2 hB,
      GlobalTheory.Models.EPolyModel.model_ePoly F M h1 h3 M.T Nm hNm i hB⟩⟩)
    s (fun a => (b a, g a)) (fun a => inZZ_mono _ _ (hmax _ (hN a)) (hZ a)) (indep_pairs F M.T z b g hR hind)

end GlobalTheory.Models.AdmBound
end

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_cocycles_card_le_sum_dims : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (s : ℕ) (z : Fin s → G → Fin M.T.m → k), (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) → LinearIndependent k (fun a => (cob M.T).mkQ (z a)) → s ≤ Dt.dsum := by
  atlas_forward_decl GlobalTheory.Models.AdmBound.main
end

section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1)

namespace GlobalTheory.ResidueBound

theorem exists_residue (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [FaithfulSMul ℤ_[l] O] (lam : O) (h : Irreducible lam) :
    Finite (O ⧸ Ideal.span {lam}) ∧ ∃ (k : Type) (_ : Field k) (_ : Algebra O k), CharP k l ∧
      Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ lam ∣ x := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {lam} := h.maximalIdeal_eq
  have hl : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    have h1 : ((IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    have h2 := IsLocalRing.eq_maximalIdeal h1
    have h3 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [← h2, Ideal.mem_comap, map_natCast] at h3
    exact h3
  have hloc : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  have hfin : Finite (IsLocalRing.ResidueField O) := by
    have : Finite (IsLocalRing.ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).toEquiv.symm
    exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[l])
  refine ⟨?_, IsLocalRing.ResidueField O, inferInstance, inferInstance, ?_, IsLocalRing.residue_surjective, fun x => ?_⟩
  · rw [← hm]; exact hfin
  · rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (IsLocalRing.residue O),
      IsLocalRing.residue_eq_zero_iff]
    exact hl
  · rw [← Ideal.mem_span_singleton, ← hm]
    exact IsLocalRing.residue_eq_zero_iff x

variable {O G k : Type} [CommRing O] [Group G] [Field k] [Algebra O k] {lam : O}

theorem exists_tensor_equiv {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (q : M →ₗ[O] N) (hq : Function.Surjective q) (hk : KerIs lam q) :
    ∃ φ : (M ⊗[O] (O ⧸ Ideal.span {lam})) ≃ₗ[O] N, ∀ m y, φ (m ⊗ₜ Ideal.Quotient.mk _ y) = y • q m := by
  have hN : ∀ x : N, lam • x = 0 := fun x => by
    obtain ⟨m, rfl⟩ := hq x
    rw [← map_smul]; exact (hk _).2 ⟨m, rfl⟩
  let f : (M ⊗[O] (O ⧸ Ideal.span {lam})) →ₗ[O] N := TensorProduct.lift ((cycMap hN).comp q)
  have hf : ∀ m y, f (m ⊗ₜ Ideal.Quotient.mk _ y) = y • q m := fun _ _ => rfl
  have h1 : ∀ x : M ⊗[O] (O ⧸ Ideal.span {lam}), ∃ m : M, x = m ⊗ₜ Ideal.Quotient.mk _ 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m y =>
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨y • m, ?_⟩
      rw [TensorProduct.smul_tmul]
      congr 1
      change _ = Ideal.Quotient.mk _ (y * 1)
      rw [mul_one]
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, (TensorProduct.add_tmul _ _ _).symm⟩
  refine ⟨LinearEquiv.ofBijective f ⟨?_, fun x => ?_⟩, hf⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := h1 x
    rw [hf, one_smul] at hx
    obtain ⟨y, rfl⟩ := (hk m).1 hx
    rw [TensorProduct.smul_tmul]
    have : lam • Ideal.Quotient.mk (Ideal.span {lam}) 1 = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    rw [this, TensorProduct.tmul_zero]
  · obtain ⟨m, rfl⟩ := hq x
    exact ⟨m ⊗ₜ Ideal.Quotient.mk _ 1, by rw [hf, one_smul]⟩

theorem exists_ext (T : Ob k G) (z : G → Fin T.m → k) (hz : ∀ g h, z (g * h) = z g + T.ρ g (z h)) :
    ∃ (E : Ob k G) (e : ((Fin T.m → k) × k) ≃ₗ[k] (Fin E.m → k)), IsExt T E z ∧
      ∀ g v y, E.ρ g (e (v, y)) = e (T.ρ g v + y • z g, y) := by
  have hz1 : z 1 = 0 := by simpa using hz 1 1
  let π : Representation k G ((Fin T.m → k) × k) :=
    { toFun := fun g => ((T.ρ g).coprod (LinearMap.toSpanSingleton k _ (z g))).prod (LinearMap.snd k _ _)
      map_one' := by
        refine LinearMap.ext fun x => ?_
        simp [hz1]
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        simp [hz g h]
        abel }
  obtain ⟨E, e, he⟩ := exists_ob π
  have he' : ∀ g v y, E.ρ g (e (v, y)) = e (T.ρ g v + y • z g, y) := fun g v y => (he g (v, y)).symm
  refine ⟨E, e, ⟨?_, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e (0, 1), fun g x => ?_, ?_, ?_, fun g => ?_⟩, he'⟩
  · have := e.finrank_eq
    simpa using this.symm
  · simp [he']
  · exact e.injective.comp LinearMap.inl_injective
  · rintro ⟨x, hx⟩
    have := congrArg Prod.snd (e.injective hx)
    simp at this
  · rw [he']
    change _ = e (0, 1) + e (z g, 0)
    rw [← map_add]
    simp

variable [TopologicalSpace G]

theorem linearIndependent_of_indepMod (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) {N : Type} [AddCommGroup N] [Module O N]
    (π : Representation O G N) (T : Ob k G) (φ : N ≃ₗ[O] (Fin T.m → k)) (hφ : ∀ g x, φ (π g x) = T.ρ g (φ x))
    {s : ℕ} (z : Fin s → ↥(Z1 π ⊤)) (hz : IndepMod lam fun a => (Submodule.Quotient.mk (z a) : H1 π ⊤)) :
    LinearIndependent k fun a => (cob T).mkQ fun g => φ ((z a : G → N) g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  choose x hx using fun a => hs (c a)
  rw [← hx, hk]
  refine hz x ?_ a
  simp only [← map_smul, ← map_sum] at hc
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hc
  have h1 : ∑ a, x a • (Submodule.Quotient.mk (z a) : H1 π ⊤) = Submodule.Quotient.mk (∑ a, x a • z a) := by
    change ∑ a, x a • Submodule.mkQ _ (z a) = Submodule.mkQ _ _
    simp only [map_smul, map_sum]
  rw [h1, Submodule.Quotient.mk_eq_zero]
  refine ⟨φ.symm b, Submodule.mem_top, ?_⟩
  funext g
  apply φ.injective
  have h2 := congrFun hb g
  change φ (π g (φ.symm b) - φ.symm b) = _
  rw [map_sub, hφ, φ.apply_symm_apply]
  refine Eq.trans h2 ?_
  simp [← hx]

theorem exists_ext_Ea (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x)
    {M X : Type} [AddCommGroup M] [Module O M] [AddCommGroup X] [Module O X] (W : Representation O G M)
    (χ : G →* Oˣ) (T : Ob k G) (φ : (M ⊗[O] X) ≃ₗ[O] (Fin T.m → k))
    (hφ : ∀ g x, φ (twCoef W χ X g x) = T.ρ g (φ x)) (ha : ∀ x : X, lam ^ 1 • x = 0)
    (z : ↥(Z1 (twCoef W χ X) ⊤)) :
    ∃ (E : Ob k G) (e : ((M ⊗[O] X) × (O ⧸ Ideal.span {lam ^ 1})) ≃ₗ[O] (Fin E.m → k)),
      IsExt T E (fun g => φ ((z : G → M ⊗[O] X) g)) ∧
      ∀ g x, e (twistRep (Ea W χ ha z) χ⁻¹ g x) = E.ρ g (e x) := by
  obtain ⟨E, e, hE, he⟩ := exists_ext T (fun g => φ ((z : G → M ⊗[O] X) g)) (fun g h => by
    rw [cocycle_mul, map_add, hφ])
  have hker : Ideal.span {lam ^ 1} = LinearMap.ker (Algebra.linearMap O k) := by
    ext x
    rw [pow_one, Ideal.mem_span_singleton, ← hk]
    rfl
  let ψ : (O ⧸ Ideal.span {lam ^ 1}) ≃ₗ[O] k :=
    (Submodule.quotEquivOfEq _ _ hker).trans ((Algebra.linearMap O k).quotKerEquivOfSurjective hs)
  have hψ : ∀ y, ψ (Ideal.Quotient.mk _ y) = algebraMap O k y := fun _ => rfl
  refine ⟨E, (φ.prodCongr ψ).trans (e.restrictScalars O), hE, ?_⟩
  rintro g ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : twistRep (Ea W χ ha z) χ⁻¹ g (m, Ideal.Quotient.mk _ y) =
      (twCoef W χ X g m + y • (z : G → M ⊗[O] X) g, Ideal.Quotient.mk _ y) := by
    rw [twistRep_apply, Ea, twistRep_apply, smul_smul, extRep_apply]
    simp
  rw [h1]
  change e (φ _, ψ _) = E.ρ g (e (φ _, ψ _))
  rw [he, map_add, hφ, map_smul, hψ, algebraMap_smul]

omit [TopologicalSpace G] in

theorem exists_coef_equiv {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M)
    (χ : G →* Oˣ) (T : Ob k G) (q : M →ₗ[O] (Fin T.m → k)) (hq : Function.Surjective q) (hk : KerIs lam q)
    (he : ∀ σ x, q (twistRep W χ⁻¹ σ x) = T.ρ σ (q x)) :
    ∃ φ : (M ⊗[O] (O ⧸ Ideal.span {lam})) ≃ₗ[O] (Fin T.m → k),
      ∀ g x, φ (twCoef W χ (O ⧸ Ideal.span {lam}) g x) = T.ρ g (φ x) := by
  obtain ⟨φ, hφ⟩ := exists_tensor_equiv q hq hk
  refine ⟨φ, fun g x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y =>
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [coefRep_tmul, hφ, hφ, he, LinearMap.map_smul_of_tower]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem exists_independent_admissible_cocycles_residue {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    [Algebra O LL] [TopologicalSpace LL] {n r l : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (Γ : GalData G Qp LL O) (D : TopData n r) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {R : RingPG k l} (F : DFun R n G) (M : ModTh F D)
    (q : ↥Γ.T₀.L.T →ₗ[O] (Fin M.T.m → k)) (hq : Function.Surjective q) (hker : KerIs Γ.lam q)
    (hqe : ∀ σ x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x))
    (hmod : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
      (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
      (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    (h0 : ∀ (a : ℕ) (ha : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ, Γ.lam ^ a • x = 0), 1 ≤ a →
      adm PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) =
        admAt PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) a ha)
    (s : ℕ) (c : Fin s → H1 (twCoef Γ.W₀ Γ.χ₁ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) ⊤)
    (hc : ∀ a, c a ∈ adm PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) (hi : IndepMod Γ.lam c) :
    ∃ z : Fin s → G → Fin M.T.m → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) ∧
      LinearIndependent k (fun a => (cob M.T).mkQ (z a)) := by
  obtain ⟨φ, hφ⟩ := exists_coef_equiv Γ.W₀ Γ.χ₁ M.T q hq hker hqe
  have ha : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ, Γ.lam ^ 1 • x = 0 := fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [h0 1 ha le_rfl] at hc
  choose z hz hadm using hc
  obtain rfl : c = fun a => Submodule.Quotient.mk (z a) := funext fun a => (hz a).symm
  refine ⟨_, fun a => ?_, linearIndependent_of_indepMod hs hk _ M.T φ hφ z hi⟩
  obtain ⟨E, e, hE, he⟩ := exists_ext_Ea hs hk Γ.W₀ Γ.χ₁ M.T φ hφ ha (z a)
  obtain ⟨L, hL⟩ := hmod E _ _ e (hadm a) he
  exact ⟨E, L, hE, hL⟩

theorem resBound_dsum : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P),
    S.Real → S.Lem0 S.Γ.W₀ → S.ResBound S.Γ.W₀ S.D.dsum := by
  intro hψ l _ P S hR h0 s c hc hi
  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hfinO : Module.Finite ℤ_[l] S.O :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥S.LL.1 ↥(integralClosure ℤ_[l] ↥S.LL.1)
  have hfa : FaithfulSMul ℤ_[l] S.O := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h1 : Function.Injective (algebraMap ℤ_[l] ↥S.LL.1) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥S.LL.1]
      exact (algebraMap ℚ_[l] ↥S.LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [IsScalarTower.algebraMap_eq ℤ_[l] S.O ↥S.LL.1, RingHom.coe_comp] at h1
    exact h1.of_comp
  obtain ⟨hst, -, hT1, hT2, hT3⟩ := S.hyp
  obtain ⟨hfin, k, _, _, hch, hs, hk⟩ := exists_residue l S.O S.Γ.lam hst.2.2.2.2.2
  obtain ⟨R, ι, hι, F, M, -, ⟨q, hq, hker, hqe⟩, hmod⟩ := hR k ⟨hs, hk⟩
  obtain ⟨z, hz, hli⟩ := exists_independent_admissible_cocycles_residue (P.PD S.K) S.emb S.Γ S.D hs hk F M q hq hker hqe hmod
    (@h0 (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK S.Γ) _ _ hfin).2.1 s c hc hi
  exact GlobalTheory.T.admissible_cocycles_card_le_sum_dims hψ F M ι hι hT1 hT2 hT3 s z hz hli

end GlobalTheory.ResidueBound
end
