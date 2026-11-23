module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvXPowMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLetterOfHodgeJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdGammaSubJumpUnitsAnnihilatesQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNInvQPowGammaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.IntegralScalarUnits

def GoodP {L M : Type} [Field L] [AddCommGroup M] [Module L M] (Sub : ℤ → Submodule L M) (y : ℕ)
    (k : ℤ) (d : M) (f : ℤ → M) (lam : L) : Prop :=
  (∃ m : ℤ, ∀ j < m, f j = 0) ∧ (∀ j, f j ∈ Sub j) ∧ (∀ j < k, f j ∈ Sub (j - y)) ∧
    f k - lam • d ∈ Sub (k - y)

theorem goodP_conv_sub_smul {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M]
    (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M) (hS : Monotone Sub) (y : ℕ) (k : ℤ)
    (d : M) (f : ℤ → M) (lam c' : L) (hf : GoodP Sub y k d f lam) :
    GoodP Sub y k d (conv w (fun m => u ^ m • f m) - c' • f)
      ((PowerSeries.constantCoeff w * u ^ k - c') * lam) := by
  obtain ⟨hb, h1, h2, h3⟩ := hf
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.NL.Twist.tri w u Sub hS y f hb h1 k h2
  obtain ⟨m1, hm1⟩ := t1
  obtain ⟨m2, hm2⟩ := hb
  refine ⟨⟨min m1 m2, fun j hj => ?_⟩, fun j => ?_, fun j hj => ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply]
    rw [hm1 j (lt_of_lt_of_le hj (min_le_left _ _)), hm2 j (lt_of_lt_of_le hj (min_le_right _ _)),
      smul_zero, sub_zero]
  · exact Submodule.sub_mem _ (t2 j) (Submodule.smul_mem _ _ (h1 j))
  · exact Submodule.sub_mem _ (t3 j hj) (Submodule.smul_mem _ _ (h2 j hj))
  · have e : (conv w (fun m => u ^ m • f m) - c' • f) k -
        ((PowerSeries.constantCoeff w * u ^ k - c') * lam) • d =
        (conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k) +
          (PowerSeries.constantCoeff w * u ^ k - c') • (f k - lam • d) := by
      simp only [Pi.sub_apply, Pi.smul_apply]
      module
    rw [e]
    exact Submodule.add_mem _ t4 (Submodule.smul_mem _ _ h3)

theorem algebraMap_units_zpow {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (v : Oˣ) (m : ℤ) :
    algebraMap O LL ((v ^ m : Oˣ) : O) = (algebraMap O LL (v : O)) ^ m := by
  have e := map_zpow (Units.map (algebraMap O LL : O →* LL)) v m
  calc algebraMap O LL ((v ^ m : Oˣ) : O)
      = ((Units.map (algebraMap O LL : O →* LL) (v ^ m) : LLˣ) : LL) := rfl
    _ = (((Units.map (algebraMap O LL : O →* LL) v) ^ m : LLˣ) : LL) := by rw [e]
    _ = (algebraMap O LL (v : O)) ^ m := by rw [Units.val_zpow_eq_zpow_val]; rfl

theorem algebraMap_units_ne_zero {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (v : Oˣ) :
    algebraMap O LL (v : O) ≠ 0 :=
  (Units.map (algebraMap O LL : O →* LL) v).ne_zero


private theorem expansion_smul_scalar {O L A X M : Type}
    [CommRing O] [Field L] [TopologicalSpace L] [Algebra O L] [CommRing A] [Algebra O A]
    [AddCommGroup X] [Module O X] [Module A X] [IsScalarTower O A X]
    [AddCommGroup M] [Module L M] (lev : A →ₐ[O] PowerSeries L) (E : X → ℤ → M)
    (hE : ∀ a x, E (a • x) = conv (lev a) (E x)) (c : O) (x : X) :
    E (c • x) = algebraMap O L c • E x := by
  rw [← smul_one_smul A c x, hE, ← Algebra.algebraMap_eq_smul_one, lev.commutes,
    PowerSeries.algebraMap_apply]
  exact GlobalTheory.NL.LevInj.conv_C _ _


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 20000000 in
theorem ex_smul_O (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL)
    (hT : IsCrys ((D.loc l).PD K) T.ρ) (i : Let K) (ζ : ↥LL.1) (hprim : IsPrimitiveRoot ζ (l ^ s))
    (c' : ↥(OL LL)) (x : ↥(((HW l).W K s LL h).N T)) :
    ex (Cm l) h T i ζ (c' • x) = algebraMap ↥(OL LL) ↥LL.1 c' • ex (Cm l) h T i ζ x := by
  have hfull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hprim
  have hlin := (GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hprim⟩ hfull).1
  exact expansion_smul_scalar (((HW l).W K s LL h).lev i ζ) (ex (Cm l) h T i ζ) hlin c' x

theorem goodP_prod {O L M X : Type} [CommRing O] [Field L] [TopologicalSpace L] [Algebra O L]
    [AddCommGroup M] [Module L M] [AddCommGroup X] [Module O X]
    (γ : X →ₗ[O] X) (P : Submodule O X) (hP : ∀ x ∈ P, γ x ∈ P) (E : X → ℤ → M)
    (w : PowerSeries L) (u : L)
    (hE : ∀ x ∈ P, ∀ c : O, E (γ x - c • x) = conv w (fun m => u ^ m • E x m) - algebraMap O L c • E x)
    (Sub : ℤ → Submodule L M) (hS : Monotone Sub) (y : ℕ) (k : ℤ) (d : M) (x₀ : X) (hx₀ : x₀ ∈ P)
    (lam₀ : L) (h₀ : GoodP Sub y k d (E x₀) lam₀) (S : Finset Oˣ) :
    Polynomial.aeval γ (∏ c ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c : O))) x₀ ∈ P ∧
    GoodP Sub y k d (E (Polynomial.aeval γ (∏ c ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c : O))) x₀))
      (lam₀ * ∏ c ∈ S, (PowerSeries.constantCoeff w * u ^ k - algebraMap O L (c : O))) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ⟨hx₀, h₀⟩
  | insert c S hc ih =>
    obtain ⟨hm, hg⟩ := ih
    have e : Polynomial.aeval γ (∏ c' ∈ insert c S, ((Polynomial.X : Polynomial O) - Polynomial.C (c' : O))) x₀ =
        γ (Polynomial.aeval γ (∏ c' ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c' : O))) x₀) -
          (c : O) • Polynomial.aeval γ (∏ c' ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c' : O))) x₀ := by
      rw [Finset.prod_insert hc, map_mul, Module.End.mul_apply]
      simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
        Module.algebraMap_end_apply]
    rw [e, Finset.prod_insert hc, mul_left_comm, hE _ hm]
    exact ⟨P.sub_mem (hP _ hm) (P.smul_mem _ hm), goodP_conv_sub_smul w u Sub hS y k d _ _ _ hg⟩

theorem ex_sub {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL)
    (i : Let K) (ζ : ↥LL.1) (x x' : ↥((H.W K s LL h).N T)) :
    ex C h T i ζ (x - x') = ex C h T i ζ x - ex C h T i ζ x' :=
  ((C.C K s LL h).tie.levB T i ζ).map_sub x x'


private theorem tensor_range_mono {R L V B : Type} [CommSemiring R] [CommSemiring L]
    [Algebra R L] [AddCommMonoid V] [Module R V] [Module L V] [IsScalarTower R L V]
    [AddCommMonoid B] [Module R B] {U U' : Submodule R B} (h : U ≤ U') :
    LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) U.subtype) ≤
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) U'.subtype) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) (Submodule.inclusion h) x, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
  rfl

private theorem goodP_of_single_approx {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (Sub : ℤ → Submodule L M) (y : ℕ) (k : ℤ) (d : M) (c : L) (n f : ℤ → M)
    (hn : (∃ m : ℤ, ∀ j < m, n j = 0) ∧ ∀ j, n j ∈ Sub j)
    (hf : ∀ j, f j ∈ Sub j) (happrox : ∀ j, n j - c • (Pi.single k d : ℤ → M) j = f (j - y)) :
    GoodP Sub y k d n c := by
  refine ⟨hn.1, hn.2, fun j hj => ?_, ?_⟩
  · have e := happrox j
    rw [Pi.single_eq_of_ne hj.ne, smul_zero, sub_zero] at e
    exact e.symm ▸ hf (j - y)
  · have e := happrox k
    rw [Pi.single_eq_same] at e
    exact e.symm ▸ hf (k - y)

private theorem quotient_eigenvector_of_expansion {O L M X : Type}
    [CommRing O] [Field L] [TopologicalSpace L] [Algebra O L]
    [AddCommGroup M] [Module L M] [AddCommGroup X] [Module O X]
    (γ q : X →ₗ[O] X) (P N : Submodule O X) (hP : ∀ x, x ∈ P ↔ q x ∈ N)
    (hγ : ∀ x, q x ∈ N → q (γ x) ∈ N) (expansion : N → ℤ → M)
    (hsub : ∀ v v', expansion (v - v') = expansion v - expansion v')
    (hsmul : ∀ (c : O) v, expansion (c • v) = algebraMap O L c • expansion v)
    (w : PowerSeries L) (u : L)
    (htwist : ∀ x (hx : q x ∈ N) (hx' : q (γ x) ∈ N),
      expansion ⟨q (γ x), hx'⟩ = conv w (fun m => u ^ m • expansion ⟨q x, hx⟩ m))
    (Sub : ℤ → Submodule L M) (hMono : Monotone Sub) (y : ℕ) (k : ℤ) (d : M)
    (hd : d ∉ Sub (k - y))
    (hcoeff : ∀ z (hz : q z ∈ N), z ∈ N → expansion ⟨q z, hz⟩ k ∈ Sub (k - y))
    (x₀ : X) (n : N) (hq : q x₀ = (n : X)) (c : L) (hc : c ≠ 0)
    (hbase : GoodP Sub y k d (expansion n) c)
    (S : Finset Oˣ) (r : Oˣ) (hr : r ∈ S) (hinj : Function.Injective (algebraMap O L))
    (hu : PowerSeries.constantCoeff w * u ^ k = algebraMap O L (r : O))
    (hkill : Polynomial.aeval γ (∏ v ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (v : O))) x₀ ∈ N) :
    ∃ z ∈ P, z ∉ N ∧ γ z - (r : O) • z ∈ N := by
  classical
  let E : X → ℤ → M := fun x => if hx : q x ∈ N then expansion ⟨q x, hx⟩ else 0
  have hEval (x : X) (hx : q x ∈ N) : E x = expansion ⟨q x, hx⟩ := dite_eq_left hx
  have hstep (x : X) (hx : x ∈ P) (v : O) :
      E (γ x - v • x) = conv w (fun m => u ^ m • E x m) - algebraMap O L v • E x := by
    have hx' := (hP x).1 hx
    have hγx := hγ x hx'
    have hm : q (γ x - v • x) ∈ N := by
      rw [map_sub, LinearMap.map_smul]
      exact N.sub_mem hγx (N.smul_mem v hx')
    have e : (⟨q (γ x - v • x), hm⟩ : N) = ⟨q (γ x), hγx⟩ - v • ⟨q x, hx'⟩ :=
      Subtype.ext (by simp only [map_sub, LinearMap.map_smul, Submodule.coe_sub, Submodule.coe_smul])
    rw [hEval _ hm, hEval _ hx', e, hsub, hsmul, htwist x hx' hγx]
  have hq₀ : q x₀ ∈ N := hq.symm ▸ n.2
  have hbase' : GoodP Sub y k d (E x₀) c := by
    rw [hEval x₀ hq₀, show (⟨q x₀, hq₀⟩ : N) = n from Subtype.ext hq]
    exact hbase
  let z := Polynomial.aeval γ (∏ v ∈ S.erase r, ((Polynomial.X : Polynomial O) - Polynomial.C (v : O))) x₀
  obtain ⟨hz, hzG⟩ := goodP_prod γ P (fun x hx => (hP _).2 (hγ x ((hP x).1 hx))) E w u
    hstep Sub hMono y k d x₀ ((hP x₀).2 hq₀) c hbase' (S.erase r)
  change z ∈ P at hz
  have hzq := (hP z).1 hz
  refine ⟨z, hz, ?_, ?_⟩
  · intro hzN
    change GoodP Sub y k d (E z) _ at hzG
    rw [hEval z hzq] at hzG
    have hd' := (Sub (k - y)).sub_mem (hcoeff z hzq hzN) hzG.2.2.2
    rw [sub_sub_cancel] at hd'
    let lam := c * ∏ v ∈ S.erase r, (PowerSeries.constantCoeff w * u ^ k - algebraMap O L (v : O))
    change lam • d ∈ Sub (k - y) at hd'
    have hlam : lam ≠ 0 := mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun v hv => by
      rw [hu, sub_ne_zero]
      exact fun he => Finset.ne_of_mem_erase hv (Units.ext (hinj he)).symm)
    have := (Sub (k - y)).smul_mem lam⁻¹ hd'
    rw [inv_smul_smul₀ hlam] at this
    exact hd this
  · rw [← Finset.mul_prod_erase S _ hr, map_mul, mul_apply_eq_comp] at hkill
    simpa only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
      Module.algebraMap_end_apply] using hkill

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 20000000 in
theorem occ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → ∃ x ∈ invN W T (W.Q ^ y), x ∉ W.N T ∧ W.γ T x - (((uU W ^ (-(a + j)) : (↥(OL LL))ˣ) : ↥(OL LL))) • x ∈ W.N T := by
  intro D HW F Cm l _ K s LL h W T hT y hy a ha j hj1 hjy
  classical
  obtain ⟨τ, hτ⟩ := ha
  have hpts := GlobalTheory.NL.Points.points D HW l K s LL h
  obtain ⟨i, ζ, hPt⟩ := hpts.2.2.1 τ
  have hprim : IsPrimitiveRoot ζ (l ^ s) := (hpts.2.1 i ζ τ hPt).1
  obtain ⟨d, hdD, hdA, hdA1⟩ :=
    GlobalTheory.NL.JumpVec.exists_letter_of_jump D HW l K s LL h T hT i ζ τ hPt a hτ
  have hQ := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
  simp only [pow_zero, AlgHom.one_apply] at hQ
  have hJ := GlobalTheory.NL.JumpsFinite.jumps_finite D HW l K s LL h T hT
  let Fs : Finset (↥(OL LL))ˣ := (hJ.toFinset ×ˢ Finset.Icc 1 y).image
    (fun p : ℤ × ℕ => uU W ^ (-(p.1 + (p.2 : ℤ))))
  have hFs : ∀ a' ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j' : ℕ, 1 ≤ j' → j' ≤ y →
      uU W ^ (-(a' + j')) ∈ Fs := by
    intro a' ha' j' h1 h2
    exact Finset.mem_image.2 ⟨(a', j'), Finset.mem_product.2
      ⟨hJ.mem_toFinset.2 ha', Finset.mem_Icc.2 ⟨h1, h2⟩⟩, rfl⟩
  have hFAnti : Antitone (FilAt ((D.loc l).PD K) T τ) := by
    apply antitone_int_of_succ_le
    intro b
    apply sup_le_sup_right
    apply inf_le_inf_left
    exact tensor_range_mono (V := T.V) (((D.loc l).PD K).Fil_anti b :
      (((D.loc l).PD K).Fil (b + 1)).restrictScalars ℚ_[l] ≤
        (((D.loc l).PD K).Fil b).restrictScalars ℚ_[l])
  let k : ℤ := (y : ℤ) - a - j
  let g : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B := Pi.single k d
  have hlat := GlobalTheory.NL.LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hPt
  have hg : g ∈ Lat (Cm l) h T i ζ := by
    refine (hlat g).2 ⟨⟨k, fun j' hj' => Pi.single_eq_of_ne hj'.ne _⟩, fun j' => ?_⟩
    by_cases hj' : j' = k
    · simp only [hj', g, Pi.single_eq_same]
      exact ⟨hdD, hFAnti (show -k ≤ a by dsimp [k]; omega) hdA⟩
    · rw [show g j' = 0 from Pi.single_eq_of_ne hj' _, map_zero]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  obtain ⟨n, c, hc, f, hf, hfe⟩ :=
    GlobalTheory.NL.Approx.approx D HW F Cm l K s LL h T hT i ζ hprim g hg y
  let q : W.DD T →ₗ[↥(OL LL)] W.DD T := (smulA W T (W.Q ^ y)).restrictScalars ↥(OL LL)
  let N := (W.N T).restrictScalars ↥(OL LL)
  let P := (invN W T (W.Q ^ y)).restrictScalars ↥(OL LL)
  let expansion : N → ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B := ex (Cm l) h T i ζ
  have hP (x : W.DD T) : x ∈ P ↔ q x ∈ N := Iff.rfl
  have hgam := GlobalTheory.NL.GamQ.gam_Q_pow D HW F Cm l K s LL h T hT y
  obtain ⟨w, hw0, hwE⟩ := hgam.2 i ζ hprim
  let Sub : ℤ → Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] (D.loc l).R.B) := fun m =>
    Di (HW l) h T i ⊓ (FilAt ((D.loc l).PD K) T τ (-m)).comap
      (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))
  have hSubMono : Monotone Sub := fun _ _ hmm =>
    inf_le_inf_left _ (Submodule.comap_mono (hFAnti (neg_le_neg hmm)))
  have hLatSub (v) (hv : v ∈ Lat (Cm l) h T i ζ) :
      (∃ m : ℤ, ∀ j < m, v j = 0) ∧ ∀ j, v j ∈ Sub j := (hlat v).1 hv
  have hn := hLatSub _ (Submodule.subset_span ⟨1, n, (GlobalTheory.NL.LatFil.conv_one _).symm⟩)
  have hbase : GoodP Sub y k d (expansion n) c :=
    goodP_of_single_approx Sub y k d c (expansion n) f hn (hLatSub f hf).2 hfe
  have hd : d ∉ Sub (k - y) := fun hmem =>
    hdA1 (hFAnti (show a + 1 ≤ -(k - (y : ℤ)) by dsimp [k]; omega) hmem.2)
  have hcoeff (z : W.DD T) (hz : q z ∈ N) (hzN : z ∈ N) :
      expansion ⟨q z, hz⟩ k ∈ Sub (k - y) := by
    obtain ⟨f', hf', he⟩ := (GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion
      D HW F Cm l K s LL h T hT y z hz).1 hzN i ζ hprim
    rw [show expansion ⟨q z, hz⟩ k = f' (k - y) from he k]
    exact (hLatSub f' hf').2 (k - y)
  obtain ⟨e, he⟩ : ∃ e : W.EE, algebraMap (AA K LL) W.EE (W.Q ^ y) * e = 1 := by
    rw [map_pow]
    exact (hQ.pow y).exists_right_inv
  let x₀ : W.DD T := e • (n : W.DD T)
  have hx₀Q : q x₀ = (n : W.DD T) := by
    change W.Q ^ y • (e • (n : W.DD T)) = _
    rw [← smul_assoc, Algebra.smul_def, he, one_smul]
  let r : (↥(OL LL))ˣ := uU W ^ (-(a + j))
  have hr : r ∈ Fs := hFs a ⟨τ, hτ⟩ j hj1 hjy
  let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))
  have hu : PowerSeries.constantCoeff w * u ^ k = algebraMap ↥(OL LL) ↥LL.1 (r : ↥(OL LL)) := by
    have hune : u ≠ 0 := algebraMap_units_ne_zero (W.χΓ W.gam)
    have hexp : -(y : ℤ) + k = -(a + (j : ℤ)) := by dsimp [k]; omega
    calc
      PowerSeries.constantCoeff w * u ^ k = u ^ (-(y : ℤ) + k) :=
        (congrArg (· * u ^ k) hw0).trans (zpow_add₀ hune _ _).symm
      _ = u ^ (-(a + (j : ℤ))) := congrArg (u ^ ·) hexp
      _ = algebraMap ↥(OL LL) ↥LL.1 (r : ↥(OL LL)) :=
        (algebraMap_units_zpow (W.χΓ W.gam) (-(a + (j : ℤ)))).symm
  exact quotient_eigenvector_of_expansion (W.γ T) q P N hP hgam.1 expansion
    (ex_sub (Cm l) h T i ζ) (ex_smul_O D HW F Cm l K s LL h T hT i ζ hprim)
    w u (fun x hx hx' => funext (hwE x hx hx')) Sub hSubMono y k d hd hcoeff
    x₀ n hx₀Q c hc hbase Fs r hr Subtype.val_injective hu
    (GlobalTheory.NL.KillLevels.annihilate D HW F Cm l K s LL h T hT y hy
      Fs hFs x₀ ((hP x₀).2 (hx₀Q.symm ▸ n.2)))

end GlobalTheory.NL.IntegralScalarUnits
