import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelHodgeRelay
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtAfTypeMain
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestOrderSections
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ValAtSpecMap
import Development.WeilBound.CoreStatements.HodgeTatePoints.WeilfunCore
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairGeo
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionFamilyIdempotent
import Development.WeilBound.CoreStatements.HodgeTatePoints.Weilreg
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ReducesAtOfWithE
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceFamilyPairing
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceLocalizationExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceDifferentialsExist
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDualOf
import Development.WeilBound.CoreStatements.HodgeTatePoints.ValCastSub

section
noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor PositivityTheory.HtPt.Weilfun

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

private theorem cubN_succ_chow_mahler_families (k : ℕ) (a m x : A) :
    cubN θ (k + 1) a m x = cubN θ k a m x * θ (a * m ^ k) m x := by
  simp only [cubN, Finset.prod_range_succ]

theorem cubN_add (h : IsCub θ) (a b : ℕ) (y x : A) :
    cubN θ (a + b) 1 y x = cubN θ a 1 y x * (θ (y ^ a) (y ^ b) x * cubN θ b 1 y x) := by
  induction b with
  | zero =>
    have e : θ (y ^ a) 1 x = 1 := by rw [h.s01, h.face]
    simp [cubN, e]
  | succ b ih =>
    rw [← Nat.add_assoc, cubN_succ_chow_mahler_families (a + b), cubN_succ_chow_mahler_families b, ih, _root_.one_mul, _root_.one_mul]
    have c := h.coc (y ^ a) (y ^ b) y x
    rw [← pow_add, ← pow_succ] at c
    calc cubN θ a 1 y x * (θ (y ^ a) (y ^ b) x * cubN θ b 1 y x) * θ (y ^ (a + b)) y x
        = cubN θ a 1 y x * cubN θ b 1 y x * (θ (y ^ (a + b)) y x * θ (y ^ a) (y ^ b) x) := by ac_rfl
      _ = cubN θ a 1 y x * cubN θ b 1 y x * (θ (y ^ a) (y ^ (b + 1)) x * θ (y ^ b) y x) := by rw [c]
      _ = _ := by ac_rfl

theorem cubN_mul (h : IsCub θ) (N M : ℕ) (y x : A) :
    cubN θ (N * M) 1 y x = cubN θ N 1 (y ^ M) x * cubN θ M 1 y x ^ N := by
  induction N with
  | zero => simp [cubN]
  | succ N ih =>
    rw [Nat.succ_mul, cubN_add h (N * M) M y x, ih, cubN_succ_chow_mahler_families N, pow_succ (cubN θ M 1 y x) N,
      _root_.one_mul, show (y ^ M) ^ N = y ^ (N * M) by rw [← pow_mul, mul_comm]]
    ac_rfl

theorem cubN_mul_of_pow (h : IsCub θ) (N M : ℕ) {x : A} (hx : x ^ N = 1) (y : A) :
    cubN θ (N * M) 1 x y = cubN θ N 1 x y ^ M := by
  rw [show N * M = M * N from Nat.mul_comm N M, cubN_mul h M N x y, hx]
  have e : cubN θ M 1 1 y = 1 := by
    unfold cubN
    exact Finset.prod_eq_one fun i _ => by rw [one_pow, _root_.one_mul, h.face]
  rw [e, _root_.one_mul]

private theorem cubN_eq_theta_pow_mul_cubN_one (h : IsCub θ) (k : ℕ) (a x z : A) :
    cubN θ k a x z = θ a (x ^ k) z * cubN θ k 1 x z := by
  induction k with
  | zero =>
    have e : θ a 1 z = 1 := by rw [h.s01, h.face]
    simp [cubN, e]
  | succ k ih =>
    rw [cubN_succ_chow_mahler_families k a, cubN_succ_chow_mahler_families k 1, ih, _root_.one_mul]
    have c := h.coc a (x ^ k) x z
    rw [← pow_succ] at c
    calc θ a (x ^ k) z * cubN θ k 1 x z * θ (a * x ^ k) x z
        = cubN θ k 1 x z * (θ (a * x ^ k) x z * θ a (x ^ k) z) := by ac_rfl
      _ = cubN θ k 1 x z * (θ a (x ^ (k + 1)) z * θ (x ^ k) x z) := by rw [c]
      _ = _ := by ac_rfl

private theorem theta_pow_mul_prod_range_eq_prod (h : IsCub θ) (a x y : A) (M : ℕ) :
    θ a x (y ^ M) * ∏ j ∈ Finset.range M, θ (y ^ j) x y = ∏ j ∈ Finset.range M, θ (a * y ^ j) x y := by
  induction M with
  | zero =>
    rw [pow_zero, Finset.prod_range_zero, Finset.prod_range_zero, _root_.mul_one, h.s12, h.s01, h.face]
  | succ M ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← ih]
    have c := h.coc a (y ^ M) y x
    rw [← pow_succ, h.s12 (a * y ^ M) y x, h.s12 a (y ^ M) x, h.s12 a (y ^ (M + 1)) x,
      h.s12 (y ^ M) y x] at c
    calc θ a x (y ^ (M + 1)) * ((∏ j ∈ Finset.range M, θ (y ^ j) x y) * θ (y ^ M) x y)
        = (∏ j ∈ Finset.range M, θ (y ^ j) x y) * (θ a x (y ^ (M + 1)) * θ (y ^ M) x y) := by ac_rfl
      _ = (∏ j ∈ Finset.range M, θ (y ^ j) x y) * (θ (a * y ^ M) x y * θ a x (y ^ M)) := by rw [c]
      _ = _ := by ac_rfl

theorem cubN_pow (h : IsCub θ) (N M : ℕ) {x : A} (hx : x ^ N = 1) (y : A) :
    cubN θ N 1 x (y ^ M) * cubN θ M 1 y x ^ N = cubN θ N 1 x y ^ M := by
  have hD : cubN θ M 1 y x = ∏ j ∈ Finset.range M, θ (y ^ j) x y := by
    unfold cubN
    exact Finset.prod_congr rfl fun j _ => by rw [_root_.one_mul, h.s12]
  have hC : cubN θ N 1 x (y ^ M) * cubN θ M 1 y x ^ N =
      ∏ i ∈ Finset.range N, ∏ j ∈ Finset.range M, θ (x ^ i * y ^ j) x y := by
    rw [hD, show (∏ j ∈ Finset.range M, θ (y ^ j) x y) ^ N =
        ∏ _i ∈ Finset.range N, ∏ j ∈ Finset.range M, θ (y ^ j) x y by
      rw [Finset.prod_const, Finset.card_range]]
    unfold cubN
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [_root_.one_mul, theta_pow_mul_prod_range_eq_prod h]
  rw [hC, Finset.prod_comm,
    show cubN θ N 1 x y ^ M = ∏ _j ∈ Finset.range M, cubN θ N 1 x y by
      rw [Finset.prod_const, Finset.card_range]]
  refine Finset.prod_congr rfl fun j _ => ?_
  have e := cubN_eq_theta_pow_mul_cubN_one h N (y ^ j) x y
  rw [hx, h.s01 (y ^ j) 1 y, h.face, _root_.one_mul] at e
  rw [← e]
  unfold cubN
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

theorem wq_level (h : IsCub θ) (N M : ℕ) {x : A} (hx : x ^ N = 1) (y : A) :
    wq θ (N * M) x y = wq θ N x (y ^ M) := by
  unfold wq
  rw [cubN_mul h N M y x, cubN_mul_of_pow h N M hx y, ← cubN_pow h N M hx y,
    mul_inv_rev, _root_.mul_assoc, mul_inv_cancel_left]

end Alg

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}

theorem weilUnit_level (c : CubicalStr G L) (N M n : ℕ) (hn : n = N * M) {T : Over S} {x y x' y' : T ⟶ G}
    (hx : x ^ N = 1) (hy : y ^ N = 1) (hx' : x' ^ n = 1) (hy' : y' ^ n = 1) (e₁ : x = x') (e₂ : y = y' ^ M) :
    weilUnit c N T x y hx hy = weilUnit c n T x' y' hx' hy' := by
  subst hn e₁ e₂
  apply Units.ext
  apply fn_ext
  intro z _
  obtain ⟨J, hJ⟩ := exists_good_at L z
  have h1 := gm_id_weilUnit c N hx hy z hJ
  have h2 := gm_id_weilUnit c (N * M) hx' hy' z hJ
  rw [wq_level (isCub_cubV c hJ) N M hx] at h2
  have h3 := congrArg Units.val (h1.trans h2.symm)
  simp only [gm_val (𝟙 T.left) z ⊤ trivial] at h3
  simp only [gs, dif_pos (show (𝟙 T.left : T.left ⟶ T.left) z ∈ (⊤ : T.left.Opens) from trivial)]
  exact h3

end PositivityTheory.Xgn.TestGroupPoint
end
end

section
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem exists_der_gen {R RC C N L U : Type} [CommRing R] [IsDomain R] [CommRing RC] [IsDomain RC] [Field C]
    [Algebra RC C] [AddCommGroup N] [Finite N] [AddCommGroup L] [Module R L] [AddCommGroup U] [Module R U]
    (σ : R →+* RC) (h1 : Function.Injective σ) (h2 : Function.Injective (algebraMap RC C))
    (φ : R →+* C) (hφ : ∀ r, algebraMap RC C (σ r) = φ r)
    {A : Subalgebra R (Multiplicative N → R)} (hA : IsHopfOrder A) (p : ℕ) {g : ℕ} (θ : L →ₗ[R] omega A)
    (hθs : Function.Surjective θ) (hθk : ∀ w, θ w = 0 → ∃ u, w = p • u) (j : L →ₗ[R] U)
    (io : U →ₛₗ[σ] (Fin g → RC)) (M : Submodule RC (N → C))
    (hM : M = Submodule.span RC {f | ∃ g ∈ A, f = fun x => φ (g (Multiplicative.ofAdd x))}) :
    ∃ Dv : M →ₗ[RC] ReciprocityTheory.PGsh.Up.LieDualModP p RC g, IsDerAt0 M Dv ∧
      ∀ (a : A) (f : M) (w : L), (∀ x, f.1 x = φ (a.1 (Multiplicative.ofAdd x))) → cotMap A a = θ w →
        Dv f = Submodule.Quotient.mk (io (j w)) := by
  letI : Algebra R RC := σ.toAlgebra
  let k₀ : L →ₗ[R] ReciprocityTheory.PGsh.Up.LieDualModP p RC g :=
    { toFun := fun w => Submodule.Quotient.mk (io (j w))
      map_add' := fun a b => by rw [map_add, map_add, Submodule.Quotient.mk_add]
      map_smul' := fun r a => by
        rw [map_smul, io.map_smulₛₗ, Submodule.Quotient.mk_smul]
        exact algebraMap_smul RC r _ }
  have hk : LinearMap.ker θ ≤ LinearMap.ker k₀ := by
    intro w hw
    obtain ⟨u, rfl⟩ := hθk w hw
    change Submodule.Quotient.mk (io (j (p • u))) = 0
    rw [map_nsmul, map_nsmul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul RC]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  let d₀ : omega A →ₗ[R] ReciprocityTheory.PGsh.Up.LieDualModP p RC g :=
    ((LinearMap.ker θ).liftQ k₀ hk) ∘ₗ (θ.quotKerEquivOfSurjective hθs).symm.toLinearMap
  have hd₀ : ∀ w, d₀ (θ w) = k₀ w := fun w => by
    have : (θ.quotKerEquivOfSurjective hθs).symm (θ w) = Submodule.Quotient.mk w :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp only [d₀, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  obtain ⟨Dv, hD1, hD2⟩ := exists_der_ext h1 h2 φ hφ hA (d₀ ∘ₗ cotMap A)
    (fun a b => by simp only [LinearMap.comp_apply, cotMap_mul, map_add, map_smul]) M hM
  refine ⟨Dv, hD1, fun a f w hf hw => ?_⟩
  rw [hD2 a f hf, LinearMap.comp_apply, hw, hd₀]
  rfl

theorem cotMap_aug {R T : Type} [CommRing R] [CommGroup T] (A : Subalgebra R (T → R)) (a : augIdeal A) :
    cotMap A a.1 = (augIdeal A).toCotangent a := by
  have ha1 : a.1.1 1 = 0 := a.2
  exact cotMap_apply _ _ a (by rw [ha1, map_zero, sub_zero])

theorem cotMap_char {R T : Type} [CommRing R] [CommGroup T] (A : Subalgebra R (T → R)) (χ : T →* Rˣ)
    (hm : (fun t => ((χ t : Rˣ) : R)) ∈ A) : cotMap A ⟨_, hm⟩ = dlogChar A χ := by
  rw [OrderApi.dlogChar_of_mem _ _ hm]
  refine cotMap_apply _ _ _ ?_
  simp

end PositivityTheory.Xgn.TestGroupPoint
end
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem bichar_mem {C RC : Type} [Field C] [IsAlgClosed C] [CommRing RC] [IsDomain RC] [Algebra RC C]
    {v : Valuation C NNReal} (hv : v.Integers RC) {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup RC T)
    (β : T →* T →* RCˣ) (s : Γ((Γ.G ⊗ Γ.G).left, ⊤))
    (hs : ∀ a b, valAt (lift (Γ.pt a) (Γ.pt b)).left ⊤ le_top s = algebraMap RC _ ((β a b : RCˣ) : RC)) :
    (fun z : T × T => ((β z.1 z.2 : RCˣ) : RC)) ∈ prodSpan (Γ.btOrder ⊤) := by
  haveI : ValuationRing RC := ValuationRing.of_integers v hv
  exact PositivityTheory.HtPt.Twpair.bichar_mem_prodSpan (PositivityTheory.HtPt.Twpair.henselian hv)
    (fun P => (PositivityTheory.HtPt.Twpair.prime_eq_bot_or_maximal hv P.asIdeal).imp id fun h => PrimeSpectrum.ext h)
    Γ β s hs

theorem tens_of_bc {R RC C N : Type} [CommRing R] [CommRing RC] [Field C] [Algebra R RC] [Algebra RC C]
    [AddCommGroup N] (φ : R →+* C) (hφ : ∀ r, algebraMap RC C (algebraMap R RC r) = φ r)
    {A : Subalgebra R (Multiplicative N → R)} {A' : Subalgebra RC (Multiplicative N → RC)}
    (ee : RC ⊗[R] A ≃ₐ[RC] A') (hee : ∀ (a : A) t, (ee (1 ⊗ₜ a)).1 t = algebraMap R RC (a.1 t))
    (M : Submodule RC (N → C))
    (hM : M = Submodule.span RC {f | ∃ g ∈ A, f = fun x => φ (g (Multiplicative.ofAdd x))}) :
    ∀ g ∈ prodSpan A', (fun z : N × N =>
      algebraMap RC C (g (Multiplicative.ofAdd z.1, Multiplicative.ofAdd z.2))) ∈ GR.tens M M := by
  have lem : ∀ x : RC ⊗[R] A, (fun y => algebraMap RC C ((ee x).1 (Multiplicative.ofAdd y))) ∈ M := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      convert M.zero_mem using 1
      funext y
      simp
    | tmul r a =>
      have e1 : r ⊗ₜ[R] a = r • ((1 : RC) ⊗ₜ[R] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e2 : (fun y => algebraMap RC C ((ee (r ⊗ₜ[R] a)).1 (Multiplicative.ofAdd y))) =
          r • fun y => φ (a.1 (Multiplicative.ofAdd y)) := by
        funext y
        rw [e1, map_smul]
        simp [hee, hφ, Algebra.smul_def]
      rw [e2, hM]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a.1, a.2, rfl⟩)
    | add x y hx hy =>
      have e2 : (fun t => algebraMap RC C ((ee (x + y)).1 (Multiplicative.ofAdd t))) =
          (fun t => algebraMap RC C ((ee x).1 (Multiplicative.ofAdd t))) +
            (fun t => algebraMap RC C ((ee y).1 (Multiplicative.ofAdd t))) := by
        funext t
        simp
      rw [e2]
      exact M.add_mem hx hy
  have lem' : ∀ a ∈ A', (fun y => algebraMap RC C (a (Multiplicative.ofAdd y))) ∈ M := by
    intro a ha
    obtain ⟨x, hx⟩ := ee.surjective ⟨a, ha⟩
    have k := lem x
    rw [hx] at k
    exact k
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    refine Submodule.subset_span ⟨_, lem' a ha, _, lem' b hb, ?_⟩
    funext z
    simp
  | zero =>
    convert (GR.tens M M).zero_mem using 1
    funext z
    simp
  | add g₁ g₂ _ _ h₁ h₂ =>
    convert (GR.tens M M).add_mem h₁ h₂ using 1
    funext z
    simp
  | smul r g _ h =>
    convert (GR.tens M M).smul_mem r h using 1
    funext z
    simp [Algebra.smul_def]

end PositivityTheory.Xgn.TestGroupPoint
end
end

section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}
  {C : Type} [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] {RC : Subalgebra O C}

set_option maxHeartbeats 800000 in

theorem kernel_mem [Fact p.Prime] (hpS : p ∈ S) [CharZero Ω] [IsLocallyNoetherian 𝔐.X]
    [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    (P : ChartPack G O c') (hT : IsTestPt p (CR O y c') RC) :
    ∃ Kf ∈ GR.tens (TestPt.testOrd P RC) (TestPt.testOrd P RC), ∀ x x' : Fin (D.p + D.q) → 𝓞 E,
      Kf (mkN p x, mkN p x') = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x x').val := by
  obtain ⟨halg, ⟨v, hv, hvp⟩, -, hR⟩ := hT
  have hp : p.Prime := Fact.out
  have hR1 : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  have hpow : p ^ 𝔐.R p = p * p ^ (𝔐.R p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hR1]
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hvI : v.Integers RC :=
    ⟨Subtype.val_injective, fun x => (hv x).1 x.2, fun r hr => ⟨⟨r, (hv r).2 hr⟩, rfl⟩⟩
  haveI : IsFractionRing RC C := hvI.isFractionRing
  haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero
  letI : Algebra (CR O y c') RC := (toRC _ RC hR).toAlgebra
  have hφ : Function.Injective (algebraMap (CR O y c') RC) := fun a b h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  let κ : FractionRing RC ≃+* C := (FractionRing.algEquiv RC C).toRingEquiv
  have hκ : ∀ r : RC, κ (algebraMap RC _ r) = r := (FractionRing.algEquiv RC C).commutes
  haveI : IsAlgClosed (FractionRing RC) := IsAlgClosed.of_ringEquiv C _ κ.symm
  let ik : Ω →+* FractionRing RC := κ.symm.toRingHom.comp (algebraMap Ω C)
  have hik : ∀ r : CR O y c', ik r = algebraMap RC _ (algebraMap (CR O y c') RC r) := fun r =>
    (RingEquiv.symm_apply_eq κ).2 (hκ (algebraMap (CR O y c') RC r)).symm
  have hfr : ik.comp (fracToField (CR O y c')) = PositivityTheory.UnitarySelfGeneration.fracMap hφ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CR O y c'))
    rw [PositivityTheory.UnitarySelfGeneration.fracMap_comp]
    ext r
    exact (congrArg ik (IsFractionRing.lift_algebraMap _ r)).trans (hik r)
  let Γ' := PositivityTheory.UnitarySelfGeneration.bcGroup P.Γ₁ hφ
  let F : Γ'.G.left ⟶ P.Γ₁.G.left := pullback.fst P.Γ₁.G.hom (spMap (algebraMap (CR O y c') RC))
  have hF : F ≫ P.Γ₁.G.hom = Γ'.G.hom ≫ spMap (algebraMap (CR O y c') RC) := pullback.condition
  have hbc : Γ'.IsBaseChange P.Γ₁ (algebraMap (CR O y c') RC) F := by
    have h := isGrpPullback_pullback P.Γ₁.G (spMap (algebraMap (CR O y c') RC))
    refine ⟨h.1, h.2, FractionRing (CR O y c'), inferInstance, algebraMap _ _,
      RingHom.id _, PositivityTheory.UnitarySelfGeneration.fracMap hφ, fun t => (P.Γ₁.pt t).left, Function.injective_id, rfl,
      PositivityTheory.UnitarySelfGeneration.fracMap_comp hφ, fun t => Over.w (P.Γ₁.pt t), fun t => ?_,
      fun t => (PositivityTheory.UnitarySelfGeneration.bcPt_fst P.Γ₁ hφ t).symm⟩
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hpt : ∀ t, (Γ'.pt t).left ≫ F ≫ P.i₁ = spMap ik ≫ (G.t₁.pt t).left := fun t => by
    rw [P.pts₁, ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfr]
    exact congrArg (· ≫ P.i₁) (PositivityTheory.UnitarySelfGeneration.bcPt_fst P.Γ₁ hφ t)
  let ζ' : RCˣ := Units.map (algebraMap (CR O y c') RC).toMonoidHom (P.ζ ^ p ^ (𝔐.R p - 1))
  have hζ' : ((ζ' : RC) : C) = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1)) := by
    rw [← P.ζ_eq]; rfl
  have hζp : ζ' ^ p = 1 := Units.ext (Subtype.ext (by
    rw [Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ', ← map_pow, ← pow_mul, mul_comm, ← hpow,
      G.ζ_prim.pow_eq_one, map_one]; rfl))
  obtain ⟨bi, hbi⟩ := exists_bichar (D.p + D.q) p (p ^ 𝔐.R p) (dvd_pow_self p (by omega)) ζ' hζp G.e
  let Z : Over 𝔐.X := Over.mk ((Γ'.G ⊗ Γ'.G).hom ≫ spMap (algebraMap (CR O y c') RC) ≫ P.x)
  have hw : ∀ u : Γ'.G ⊗ Γ'.G ⟶ Γ'.G, (u.left ≫ F ≫ P.i₁) ≫ 𝔐.t.G.hom = Z.hom := fun u => by
    rw [Category.assoc, Category.assoc, P.tors₁.isOver, ← Category.assoc F, hF, Category.assoc,
      ← Category.assoc u.left, Over.w u]
    rfl
  let X : (Γ'.G ⊗ Γ'.G ⟶ Γ'.G) → (Z ⟶ 𝔐.t.G) := fun u => Over.homMk (u.left ≫ F ≫ P.i₁) (hw u)
  have hX : ∀ u, X u ^ p = 1 := fun u =>
    PositivityTheory.HtPt.Htat.tors_of_pt P.tors₁ (u.left ≫ F) (X u) (Category.assoc _ _ _).symm
  have hs : ∀ a b, valAt (lift (Γ'.pt a) (Γ'.pt b)).left ⊤ le_top
      (PositivityTheory.HtPt.Weilfun.weilUnit 𝔐.t.cub p Z (X (fst _ _)) (X (snd _ _)) (hX _) (hX _)).val =
      algebraMap RC _ ((bi a b : RCˣ) : RC) := by
    intro a b
    obtain ⟨x, rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p a
    obtain ⟨x', rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p b
    let f₀ := lift (Γ'.pt (qmk p x)) (Γ'.pt (qmk p x'))
    have hf₀ : f₀.left ≫ Z.hom = spMap ik ≫ 𝔐.ξ := by
      rw [← hw (fst _ _), ← Category.assoc, ← Category.assoc, ← Over.comp_left, lift_fst, hpt, Category.assoc,
        Over.w]
      rfl
    let f : Over.mk (spMap ik ≫ 𝔐.ξ) ⟶ Z := Over.homMk f₀.left hf₀
    let ψ : Over.mk (spMap ik ≫ 𝔐.ξ) ⟶ Over.mk 𝔐.ξ := Over.homMk (spMap ik) rfl
    have e1 : f ≫ X (fst _ _) = ψ ≫ G.t₂.pt (qmk _ (p ^ (𝔐.R p - 1) • x)) := by
      rw [G.compat]
      refine Over.OverMorphism.ext ?_
      change f₀.left ≫ (fst Γ'.G Γ'.G).left ≫ F ≫ P.i₁ = spMap ik ≫ _
      rw [← Category.assoc, ← Over.comp_left, lift_fst, hpt]
    have e2 : f ≫ X (snd _ _) = (ψ ≫ G.t₂.pt (qmk _ x')) ^ p ^ (𝔐.R p - 1) := by
      rw [← PositivityTheory.HtPt.Htat.comp_pow_pt, ← map_pow]
      have : (qmk (p ^ 𝔐.R p) x') ^ p ^ (𝔐.R p - 1) = qmk _ (p ^ (𝔐.R p - 1) • x') :=
        ((qhom _ (p ^ 𝔐.R p)).map_pow (Multiplicative.ofAdd x') _).symm
      rw [this, G.compat]
      refine Over.OverMorphism.ext ?_
      change f₀.left ≫ (snd Γ'.G Γ'.G).left ≫ F ≫ P.i₁ = spMap ik ≫ _
      rw [← Category.assoc, ← Over.comp_left, lift_snd, hpt]
    have t1 : ∀ u, (f ≫ X u) ^ p = 1 := fun u => by
      rw [← PositivityTheory.HtPt.Htat.comp_pow_pt, hX, MonObj.comp_one]
    have t2 : ∀ z, (ψ ≫ G.t₂.pt z) ^ p ^ 𝔐.R p = 1 := fun z => by
      rw [← PositivityTheory.HtPt.Htat.comp_pow_pt, (G.t₂.onto _).2 ⟨z, rfl⟩, MonObj.comp_one]
    have k1 := PositivityTheory.HtPt.Weilfun.weilUnit_comp 𝔐.t.cub p f (hX (fst _ _)) (hX (snd _ _)) (t1 _) (t1 _)
    let u : (FractionRing RC)ˣ := Units.map (algebraMap RC _).toMonoidHom (bi (qmk p x) (qmk p x'))
    have hu : (u : FractionRing RC) = ik (G.ζ ^ (G.e (p ^ (𝔐.R p - 1) • x) x').val) := by
      rw [map_nsmul, AddMonoidHom.nsmul_apply, pow_val_nsmul G.ζ_prim.pow_eq_one]
      refine ((RingEquiv.symm_apply_eq κ).2 ?_).symm
      change _ = κ (algebraMap RC _ ((bi (qmk p x) (qmk p x') : RCˣ) : RC))
      rw [hκ, hbi, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ', map_pow]
    have k2 := (G.weil (p ^ (𝔐.R p - 1) • x) x' _ ik (ψ ≫ G.t₂.pt (qmk _ _)) (ψ ≫ G.t₂.pt (qmk _ _)) u rfl rfl).2 hu
    haveI : Subsingleton (Over.mk (spMap ik ≫ 𝔐.ξ)).left :=
      inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing RC)))
    have k3 := PositivityTheory.HtPt.Weilfun.weilUnit_eq_of_weilIs 𝔐.t.cub (p ^ 𝔐.R p) (t2 _) (t2 _) (unitOn u)
      (by rw [Nat.cast_pow]; exact k2)
    rw [weilUnit_level 𝔐.t.cub p (p ^ (𝔐.R p - 1)) _ hpow (t1 _) (t1 _) (t2 _) (t2 _) e1 e2, k3] at k1
    rw [PositivityTheory.HtPt.Weilreg.valAt_top]
    refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing RC))).hom.hom k1.symm).trans ?_
    exact PositivityTheory.HtPt.Weilreg.val_unitOn _
  have hmem := bichar_mem hvI Γ' bi _ hs
  obtain ⟨ee, hee⟩ := (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.2.1 RC Γ' F hbc
  refine ⟨_, tens_of_bc (N := TestPt.NAdd E (D.p + D.q) p) (C := C) (RC := RC)
    ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω)) (fun _ => rfl) ee hee (TestPt.testOrd P RC) rfl _ hmem,
    fun x x' => ?_⟩
  change (((bi (qmk p x) (qmk p x') : RCˣ) : RC) : C) = _
  rw [hbi, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ']

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem exists_der [Fact p.Prime] (hpS : p ∈ S) [CharZero Ω]
    [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    (P : ChartPack G O c') (hR : ∀ a ∈ CR O y c', algebraMap Ω C a ∈ RC) {g : ℕ}
    (io : P.Dh.om →ₛₗ[toRC (CR O y c') RC hR] (Fin g → RC)) :
    ∃ Dv : TestPt.testOrd P RC →ₗ[RC] ReciprocityTheory.PGsh.Up.LieDualModP p RC g, IsDerAt0 _ Dv ∧
      (∀ u : P.Dh.om, ∃ f : TestPt.testOrd P RC, f.1 0 = 0 ∧ Dv f = Submodule.Quotient.mk (io u)) ∧
      ∀ (x : Fin (D.p + D.q) → 𝓞 E) (f : TestPt.testOrd P RC),
        (∀ x', f.1 (mkN p x') = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x x').val) →
        Dv f = Submodule.Quotient.mk (io ⟨P.Dh.h x, P.Dh.h_mem x⟩) := by
  have hp : p.Prime := Fact.out
  have hR1 : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero
  haveI : Finite (TestPt.NAdd E (D.p + D.q) p) := this
  haveI := FunctionFamilyIdempotent.frac_epi (CR O y c')
  have hφ : Function.Injective (toRC (CR O y c') RC hR) := fun a b h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  have hBT := GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁ 𝔐.t.semi.smooth
  obtain ⟨θ, ⟨hθs, -⟩, hθk, hθc⟩ := hBT.2.2.2.2.2 P.L P.M
  have hom : P.Dh.om = LinearMap.range P.j := P.isHT.1
  have hj : ∀ w, P.j w ∈ P.Dh.om := fun w => by rw [hom]; exact ⟨w, rfl⟩
  obtain ⟨Dv, hD1, hD2⟩ := exists_der_gen (N := TestPt.NAdd E (D.p + D.q) p) (C := C) _ hφ Subtype.val_injective
    ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω)) (fun _ => rfl) hBT.1 p θ hθs (fun w => (hθk w).1)
    (P.j.codRestrict _ hj) io (TestPt.testOrd P RC) rfl
  refine ⟨Dv, hD1, fun u => ?_, fun x f hf => ?_⟩
  · obtain ⟨w, hw⟩ : u.1 ∈ LinearMap.range P.j := by rw [← hom]; exact u.2
    obtain ⟨a, ha⟩ := (augIdeal (P.Γ₁.btOrder ⊤)).toCotangent_surjective (θ w)
    have ha1 : a.1.1 1 = 0 := a.2
    refine ⟨⟨_, Submodule.subset_span ⟨a.1.1, a.1.2, rfl⟩⟩, ?_, ?_⟩
    · change algebraMap Ω C ((a.1.1 1 : CR O y c') : Ω) = 0
      rw [ha1]; simp
    · refine (hD2 a.1 _ w (fun _ => rfl) ((cotMap_aug _ a).trans ha)).trans ?_
      exact congrArg (fun z => Submodule.Quotient.mk (io z)) (Subtype.ext hw)
  · obtain ⟨χ, w, hχ, hw, hHT⟩ := P.isHT.2.2 x
    obtain ⟨α, hα⟩ := exists_alpha (E := E) (D.p + D.q) p (𝔐.R p) hR1
    have h1 := isHT_res P.Γ₁ P.Γ₂ (dvd_pow_self p (by omega)) P.tors₁ P.tors₂ P.M α (fun t => by
      obtain ⟨z, rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p t
      rw [← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, ← P.pts₂, hα, G.compat]) χ w hHT
    have hval : ∀ z, ((((χ.comp α) (qmk p z) : (CR O y c')ˣ) : CR O y c') : Ω) =
        (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x z).val := fun z => by
      rw [MonoidHom.comp_apply, hα]
      have : χ (qmk _ (p ^ (𝔐.R p - 1) • z)) = P.ζ ^ (P.Dh.e x (p ^ (𝔐.R p - 1) • z)).val := hχ _
      rw [this, P.Dh_e, map_nsmul, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, P.ζ_eq,
        pow_val_nsmul G.ζ_prim.pow_eq_one]
    have hm : (fun t => (((χ.comp α) t : (CR O y c')ˣ) : CR O y c')) ∈ P.Γ₁.btOrder ⊤ := by
      obtain ⟨s, hs, -⟩ := h1
      exact char_mem _ _ s hs
    refine (hD2 ⟨_, hm⟩ f w (fun z => ?_) ((cotMap_char _ _ hm).trans (hθc _ _ h1).symm)).trans
      (congrArg (fun z => Submodule.Quotient.mk (io z)) (Subtype.ext hw.symm))
    obtain ⟨z', hz'⟩ := FunctionFamilyIdempotent.qmk_surj _ p (Multiplicative.ofAdd z)
    have : z = mkN p z' := (congrArg Multiplicative.toAdd hz').symm
    subst this
    rw [hf]
    exact ((congrArg (algebraMap Ω C) (hval z')).trans (map_pow _ _ _)).symm

theorem act_mem [Fact p.Prime]
    [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    (P : ChartPack G O c') (a : 𝓞 E) (f : TestPt.NAdd E (D.p + D.q) p → C) (hf : f ∈ TestPt.testOrd P RC) :
    (fun x : TestPt.NAdd E (D.p + D.q) p => f fun i => Ideal.Quotient.mk _ a * x i) ∈ TestPt.testOrd P RC := by
  have hp : p.Prime := Fact.out
  haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero
  haveI := FunctionFamilyIdempotent.frac_epi (CR O y c')
  haveI := 𝔐.t.act.hom a
  have h4 := (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.1 (𝔐.t.act.act a) (FunctionFamilyIdempotent.mulT _ p a) (by
      intro t
      obtain ⟨x, rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p t
      rw [← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, FunctionFamilyIdempotent.mulT_qmk,
        G.t₁.lin, Over.comp_left, P.pts₁]
      simp only [Category.assoc])
  have : TestPt.testOrd P RC ≤ (TestPt.testOrd P RC).comap (LinearMap.funLeft RC C
      fun (x : TestPt.NAdd E (D.p + D.q) p) i => Ideal.Quotient.mk _ a * x i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact Submodule.subset_span ⟨_, h4 g hg, rfl⟩
  exact this hf

end PositivityTheory.Xgn.TestGroupPoint
end
end

section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.Xgn.exists_cm_type_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 t
  have uniq : ∀ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) →
      ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
    intro σ hσ σ' hσ'
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      (RingHom.ext fun a => (hσ' a).trans (hσ a).symm)
  rcases t with τ | τ
  · let φ : E →+* Ω := 𝔐.cst.comp ((τ : E →+* ℂ).codRestrict c.F (c.conj τ))
    have h1 : ∀ a : 𝓞 E, φ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
    refine ⟨φ, h1, fun a => ?_, uniq φ h1⟩
    show φ (IsCMField.complexConj E (a : E)) = φ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq]
  · let φ : E →+* Ω := 𝔐.cst.comp ((τ : E →+* ℂ).codRestrict c.F (c.conj τ))
    have h1 : ∀ a : 𝓞 E, (φ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb (Sum.inr τ) a := by
      intro a
      show φ (IsCMField.complexConj E (a : E)) = φ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq]
    refine ⟨φ.comp (HT.cmConj E).toRingHom, h1, fun a => ?_, uniq _ h1⟩
    show φ (IsCMField.complexConj E (IsCMField.complexConj E (a : E))) = φ (a : E)
    rw [IsCMField.complexConj_apply_apply]
end

section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem smul_mem_spanOver {o C V : Type} [CommRing o] [Field C] [Algebra o C] [AddCommGroup V] [Module C V]
    (RC : Subalgebra o C) (S : Set V) {a : C} (ha : a ∈ RC) {x : V} (hx : x ∈ spanOver RC S) :
    a • x ∈ spanOver RC S := by
  refine AddSubgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ h1 h2 => ?_) (fun x _ h => ?_) hx
  · obtain ⟨b, hb, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, RC.mul_mem ha hb, e, he, smul_smul a b e⟩
  · rw [smul_zero]; exact AddSubgroup.zero_mem _
  · rw [smul_add]; exact AddSubgroup.add_mem _ h1 h2
  · rw [smul_neg]; exact AddSubgroup.neg_mem _ h

theorem exists_dual_family (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] :
    ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual A M), ∀ m, ∑ i, f i m • e i = m := by
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin' A M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property t LinearMap.id ht
  refine ⟨n, fun i => t (Pi.single i 1), fun i => LinearMap.proj i ∘ₗ s, fun m => ?_⟩
  have h := LinearMap.congr_fun hs m
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_rhs => rw [← h, pi_eq_sum_univ' (s m), map_sum]
  simp only [map_smul, LinearMap.comp_apply, LinearMap.proj_apply]

theorem lattices_alg {O Ω C : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω] [Algebra O C] [Algebra Ω C]
    (R : Subalgebra O Ω) (RC : Subalgebra O C) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
    {L Li : Type} [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L]
    [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li) (hbc : IsBaseChange Ω toLi)
    (j : Module.Dual R L →ₗ[R] Module.Dual Ω Li) (hj : ∀ u v, j u (toLi v) = algebraMap R Ω (u v))
    (om : Submodule R (Module.Dual Ω Li)) (hom : om = LinearMap.range j) {g : ℕ}
    (io : om →ₛₗ[toRC R RC hR] (Fin g → RC)) (ev : Li → ((Fin g → C) →ₗ[C] C))
    (hio : Submodule.span RC (Set.range io) = ⊤)
    (hev : ∀ v (u : om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    {r : ℕ} (b : Fin r → Li) (co : Li →ₗ[Ω] (Fin r → Ω)) (hco : ∀ k, co (b k) = Pi.single k 1)
    (W : AddSubgroup (Fin r → Ω)) (hW1 : ∀ v, co (toLi v) ∈ W)
    (hW2 : ∀ a ∈ W, ∀ u ∈ om, u (∑ k, a k • b k) ∈ R) :
    (∀ z : Fin r → C, z ∈ spanOver RC (bcMap Ω C _ '' dotDual R W) ↔
        ∃ u : Fin g → RC, ∀ k, z k = ev (b k) fun j => (u j : C)) ∧
    ∀ a : Fin r → C, a ∈ spanOver RC (bcMap Ω C _ '' W) ↔
      ∀ u : Fin g → RC, ∑ k, a k * ev (b k) (fun j => (u j : C)) ∈ RC := by
  classical
  have hadd : ∀ x (u u' : Fin g → RC), ev x (fun j => ((u + u') j : C)) =
      ev x (fun j => (u j : C)) + ev x fun j => (u' j : C) := fun x u u' => by
    rw [← map_add]; rfl
  have hsm : ∀ x (s : RC) (u : Fin g → RC), ev x (fun j => ((s • u) j : C)) =
      (s : C) * ev x (fun j => (u j : C)) := fun x s u => by
    rw [← smul_eq_mul, ← map_smul]; rfl
  have hzero : ∀ x, ev x (fun j => ((0 : Fin g → RC) j : C)) = 0 := fun x => map_zero (ev x)
  have hall : ∀ u : Fin g → RC, u ∈ Submodule.span RC (Set.range io) := fun u => by rw [hio]; trivial
  have hdd : ∀ m, m ∈ dotDual R W ↔ ∀ l ∈ W, l ⬝ᵥ m ∈ R := fun m => by
    simp only [dotDual, AddSubgroup.mem_iInf]
    rfl
  refine ⟨fun z => ⟨fun hz => ?_, ?_⟩, fun a => ⟨fun ha u => ?_, fun ha => ?_⟩⟩
  · refine AddSubgroup.closure_induction (p := fun z _ => ∃ u : Fin g → RC, ∀ k, z k = ev (b k) fun j => (u j : C))
      ?_ ⟨0, fun k => (hzero _).symm⟩ ?_ ?_ hz
    · rintro _ ⟨s, hs, _, ⟨m, hm, rfl⟩, rfl⟩
      let U : Module.Dual Ω Li := (Fintype.linearCombination Ω m) ∘ₗ co
      have hU : ∀ x, U x = co x ⬝ᵥ m := fun x => by
        simp [U, Fintype.linearCombination_apply, dotProduct]
      let w₀ : Module.Dual R L :=
        { toFun := fun v => ⟨U (toLi v), by rw [hU]; exact (hdd m).1 hm _ (hW1 v)⟩
          map_add' := fun a b => Subtype.ext (by simp)
          map_smul' := fun a b => Subtype.ext (by
            change U (toLi (a • b)) = (a : Ω) * U (toLi b)
            rw [toLi.map_smul, ← smul_eq_mul, ← U.map_smul]; rfl) }
      have hjw : j w₀ = U := hbc.algHom_ext _ _ fun v => by rw [hj]; rfl
      refine ⟨(⟨s, hs⟩ : RC) • io ⟨U, by rw [hom]; exact ⟨w₀, hjw⟩⟩, fun k => ?_⟩
      rw [hsm, hev]
      change s * algebraMap Ω C (m k) = s * algebraMap Ω C (U (b k))
      rw [hU, hco, single_one_dotProduct]
    · rintro x y _ _ ⟨u, hu⟩ ⟨u', hu'⟩
      exact ⟨u + u', fun k => by rw [hadd, ← hu, ← hu']; rfl⟩
    · rintro x _ ⟨u, hu⟩
      exact ⟨(-1 : RC) • u, fun k => by rw [hsm, ← hu]; simp⟩
  · rintro ⟨u, hu⟩
    obtain rfl : z = fun k => ev (b k) fun j => (u j : C) := funext hu
    clear hu
    induction hall u using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨y, rfl⟩ := h
      refine AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨fun k => y.1 (b k), (hdd _).2 fun l hl => ?_, rfl⟩, ?_⟩
      · have := hW2 l hl y.1 y.2
        rw [map_sum] at this
        simpa only [map_smul, smul_eq_mul, dotProduct] using this
      · rw [one_smul]
        exact funext fun k => hev _ _
    | zero => simp only [hzero]; exact AddSubgroup.zero_mem _
    | add x y _ _ hx hy => simp only [hadd]; exact AddSubgroup.add_mem _ hx hy
    | smul s x _ hx => simp only [hsm]; exact smul_mem_spanOver RC _ s.2 hx
  · refine AddSubgroup.closure_induction (p := fun a _ => ∑ k, a k * ev (b k) (fun j => (u j : C)) ∈ RC)
      ?_ (by simp) ?_ ?_ ha
    · rintro _ ⟨s, hs, _, ⟨a₀, ha₀, rfl⟩, rfl⟩
      have key : ∑ k, algebraMap Ω C (a₀ k) * ev (b k) (fun j => (u j : C)) ∈ RC := by
        refine Submodule.span_induction
          (p := fun u _ => ∑ k, algebraMap Ω C (a₀ k) * ev (b k) (fun j => ((u : Fin g → RC) j : C)) ∈ RC)
          ?_ ?_ ?_ ?_ (hall u)
        · rintro _ ⟨y, rfl⟩
          have := hR _ (hW2 a₀ ha₀ y.1 y.2)
          rw [map_sum, map_sum] at this
          simpa only [map_smul, smul_eq_mul, map_mul, hev] using this
        · simp only [hzero, mul_zero, Finset.sum_const_zero]; exact RC.zero_mem
        · intro x y _ _ hx hy
          simp only [hadd, mul_add, Finset.sum_add_distrib]
          exact RC.add_mem hx hy
        · intro s x _ hx
          simp only [hsm, mul_left_comm _ (s : C), ← Finset.mul_sum]
          exact RC.mul_mem s.2 hx
      have := RC.mul_mem hs key
      rw [Finset.mul_sum] at this
      convert this using 2 with k
      exact _root_.mul_assoc _ _ _
    · intro x y _ _ hx hy
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact RC.add_mem hx hy
    · intro x _ hx
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      exact RC.neg_mem hx
  · obtain ⟨n, e, f, hef⟩ := exists_dual_family R L
    have hid : (∑ m, (j (f m)).smulRight (toLi (e m)) : Li →ₗ[Ω] Li) = LinearMap.id :=
      hbc.algHom_ext _ _ fun v => by
        rw [LinearMap.id_apply, LinearMap.sum_apply]
        conv_rhs => rw [← hef v, map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [LinearMap.smulRight_apply, hj, map_smul, algebraMap_smul]
    have hk : ∀ k k', (Pi.single k 1 : Fin r → Ω) k' = ∑ m, j (f m) (b k) * co (toLi (e m)) k' := fun k k' => by
      have := congrArg co (LinearMap.congr_fun hid (b k))
      rw [LinearMap.id_apply, hco, LinearMap.sum_apply, map_sum] at this
      rw [← this, Finset.sum_apply]
      simp only [LinearMap.smulRight_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    have hjm : ∀ m, j (f m) ∈ om := fun m => by rw [hom]; exact ⟨_, rfl⟩
    have ha' : a = ∑ m, (∑ k, a k * ev (b k) (fun i => (io ⟨_, hjm m⟩ i : C))) • bcMap Ω C _ (co (toLi (e m))) := by
      funext k'
      rw [Finset.sum_apply]
      simp only [hev, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ k, ∑ m, a k * algebraMap Ω C (j (f m) (b k)) * bcMap Ω C _ (co (toLi (e m))) k' =
          a k * algebraMap Ω C ((Pi.single k 1 : Fin r → Ω) k') := fun k => by
        rw [hk, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul, _root_.mul_assoc]
        rfl
      simp only [this]
      rw [Finset.sum_eq_single k' (fun k _ h => by simp [Pi.single_eq_of_ne h.symm]) (by simp)]
      simp
    rw [ha']
    exact AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ⟨_, ha _, _, ⟨_, hW1 _, rfl⟩, rfl⟩

theorem lattices (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ) (hd : IsArithVar (mCoordIdeal y) (d + 1)) (hpq : 0 < D.p + D.q) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime] (hpm : (p : A) ∈ m) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k) (hc' : mseg y c' ≠ 0) (P : ChartPack G O c') (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr E) (hR : ∀ a ∈ CR O y c', algebraMap Ω C a ∈ RC) {g : ℕ}
    (io : P.Dh.om →ₛₗ[toRC (CR O y c') RC hR] (Fin g → RC)) (ev : 𝔐.Li → ((Fin g → C) →ₗ[C] C))
    (hio : Submodule.span RC (Set.range io) = ⊤)
    (hev : ∀ v (u : P.Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (t : CMType H ⊕ CMType H) {r : ℕ} (b : Fin r → 𝔐.Li) (hb : LinearIndependent Ω b)
    (hb' : Submodule.span Ω (Set.range b) = 𝔐.Vgen t) :
    (∀ z : Fin r → C,
      z ∈ spanOver RC (bcMap Ω C _ '' dotDual (CR O y c') (coordLat O y (𝔐.dR t) b c')) ↔
        ∃ u : Fin g → RC, ∀ k, z k = ev (b k) fun j => (u j : C)) ∧
    ∀ a : Fin r → C, a ∈ spanOver RC (bcMap Ω C _ '' coordLat O y (𝔐.dR t) b c') ↔
      ∀ u : Fin g → RC, ∑ k, a k * ev (b k) (fun j => (u j : C)) ∈ RC := by
  classical
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  haveI := 𝔐.t.semi.comm
  haveI := P.fin
  haveI := P.proj
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  obtain ⟨σ, hσ, -, -⟩ := PositivityTheory.Xgn.exists_cm_type_embedding E H D l Xo c O₀ β Y S Ω K J y 𝔐 t
  obtain ⟨hσO, x₀, hx₀, o₀, ho₀⟩ :=
    PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hdisc A m hpm O σ
  have hσR : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap (CR O y c') Ω).range := fun a => by
    obtain ⟨o, ho⟩ := hσO a
    exact ⟨algebraMap O _ o, ho⟩
  have hdual : ∀ k, σ (HT.dualInt E k) ∈ (algebraMap (CR O y c') Ω).range := fun k => by
    have := (HT.different_generator_dualInt (CR O y c') Ω E σ 1 hinj hσR (le_antisymm ?_ ?_)).2.1 k
    · rwa [map_one, _root_.one_mul] at this
    · rw [Submodule.span_singleton_le_iff_mem, map_one, ← ho₀]
      exact Submodule.smul_mem _ (algebraMap O (CR O y c') o₀) (Submodule.subset_span ⟨x₀, hx₀, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      obtain ⟨s, hs⟩ := hσR x
      exact Submodule.mem_span_singleton.2 ⟨s, by rw [map_one, Algebra.smul_def, _root_.mul_one, hs]⟩
  have heig : ∀ x, x ∈ HT.eigSp 𝔐.ρ σ ↔ x ∈ 𝔐.Vgen t := fun x => by
    rw [HT.LatBasic.mem_eigSp]
    simp [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, sub_eq_zero, hσ]
  have hπ : ∀ x, HT.eigProj 𝔐.ρ σ x ∈ Submodule.span Ω (Set.range b) := fun x => by
    rw [hb', ← heig]
    exact HT.LatBasic.eigProj_mem _ _ _
  let co : 𝔐.Li →ₗ[Ω] (Fin r → Ω) := (Finsupp.linearEquivFunOnFinite Ω Ω (Fin r)).toLinearMap ∘ₗ hb.repr ∘ₗ
    (HT.eigProj 𝔐.ρ σ).codRestrict _ hπ
  have hsum : ∀ x, ∑ k, co x k • b k = HT.eigProj 𝔐.ρ σ x := fun x => by
    have := hb.linearCombination_repr ⟨_, hπ x⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    exact this
  have hco : ∀ k, co (b k) = Pi.single k 1 := fun k => by
    have h1 : HT.eigProj 𝔐.ρ σ (b k) = b k :=
      HT.LatBasic.eigProj_of_mem ((heig _).2 (hb' ▸ Submodule.subset_span ⟨k, rfl⟩))
    refine funext (Fintype.linearIndependent_iffₛ.1 hb _ _ ?_)
    rw [hsum, h1, Finset.sum_eq_single k (fun i _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
    simp
  have hρ : ∀ a v, 𝔐.ρ a (P.toLi v) = P.toLi (P.ρ a v) := fun a v => by
    apply 𝔐.M.inj
    apply Over.OverMorphism.ext
    rw [𝔐.act a (P.toLi v), P.toLi_pt, P.act a v, Over.comp_left, P.toLi_pt, Over.comp_left, Category.assoc]
  refine lattices_alg (CR O y c') RC hR P.toLi P.toLi_bc P.j P.j_apply P.Dh.om P.isHT.1 io ev hio hev b co hco _
    (fun v => ?_) fun a ha u hu => ?_
  · rw [Fam.mem_coordLat_iff]
    intro q hq hO
    have hsub : ∀ a : CR O y c', algebraMap (CR O y c') Ω a ∈ regAt 𝔐.ξ q := fun a =>
      GlobalTheory.CompanionTheory.Ar.Fam.chartRing_le_regAt O y c' q hq hO a.2
    have hr : q.1 ∈ Set.range P.x := by
      obtain ⟨U, hU, hmem⟩ := 𝔐.tie.affine c' hc'
      exact PositivityTheory.Xgn.SequenceLocalization.mem_range hξ hU _ P.x P.x_gen (fun z => (hmem _).2 ⟨𝔐.all _,
        (PositivityTheory.Xgn.exists_function_at_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O G c' hc' P z).1⟩)
        q ((hmem _).2 ⟨q.2, hq⟩) hsub
    obtain ⟨Q, hQ⟩ : ∃ Q : PrimeSpectrum (CR O y c'), P.x Q = q.1 := hr
    obtain ⟨_, -, hzs, hg⟩ := GlobalTheory.CompanionTheory.HtLink.stalk_loc hξ _ hinj P.x P.x_gen Q q hQ hsub
    have hlat : ∀ v, P.toLi v ∈ 𝔐.M.lat q := fun v =>
      Submodule.subset_span (GlobalTheory.CompanionTheory.HtLink.tan_ext 𝔐.M P.M hzs (genMap 𝔐.ξ q) hg P.toLi P.toLi_pt v)
    rw [hsum]
    refine ⟨?_, (heig _).1 (HT.LatBasic.eigProj_mem _ _ _)⟩
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hρ]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨s, hs⟩ := hdual k
    exact (𝔐.M.lat q).smul_mem ⟨_, hs ▸ hsub s⟩ (hlat _)
  · exact PositivityTheory.Xgn.sequence_family_pairing E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P
      u hu _ fun q h1 h2 => ((Fam.mem_coordLat_iff O y _ b c' a).1 ha q h1 h2).1

end PositivityTheory.Xgn.TestGroupPoint
end
end

section
open GlobalTheory.CompanionTheory.Ar.Num
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem typed {O C : Type} [CommRing O] [Field C] [Algebra O C] (RC : Subalgebra O C) (v : Valuation C NNReal)
    (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (p w : C) (hw0 : w ≠ 0) (hw1 : v w < 1) (hpw : v p ≤ v w * v w) (c P : RC)
    (hc : v (c : C) = v w) (hP : (P : C) = p)
    {I : Type} [Fintype I] [DecidableEq I] {g n r s : ℕ} (AF : Submodule RC (I → RC))
    (Hm : Matrix (Fin g) I RC) (Eg Ei : Matrix I I RC) (hEi : Ei * Eg = 1)
    (h0 : ∀ l, c • l ∈ AF) (h1 : ∀ k, Hm k ∈ AF) (h2 : ∀ y, y ᵥ* Eg ∈ AF → ∃ u, Hm *ᵥ y = c • u)
    (h3 : ∀ u : Fin g → RC, ∃ (y : I → RC) (u' : Fin g → RC), y ᵥ* Eg ∈ AF ∧ Hm *ᵥ y = c • u + P • u')
    (h4 : ∀ u : Fin g → RC, ∃ x : I → C, (∀ l ∈ AF, v (∑ j, algebraMap RC C (l j) * x j) ≤ 1) ∧
      Hm.map (algebraMap RC C) *ᵥ x = fun k => algebraMap RC C (u k))
    (Pm : Matrix (Fin n) I RC) (Jm : Matrix I (Fin n) RC) (hPJ : Pm * Jm = 1)
    (hst : ∀ l ∈ AF, l ᵥ* (Jm * Pm) ∈ AF) (hh : AddSubgroup (Fin n → C))
    (hhh : ∀ u, u ∈ hh ↔ ∀ l ∈ AF, (∑ j, (l j : C) * (Jm.map (algebraMap RC C)).mulVec u j) ∈ RC)
    (evs : Fin s → ((Fin g → C) →ₗ[C] C)) (evr : Fin r → ((Fin g → C) →ₗ[C] C))
    (om : AddSubgroup (Fin s → C)) (lie W : AddSubgroup (Fin r → C))
    (hom : ∀ z, z ∈ om ↔ ∃ u : Fin g → RC, ∀ k, z k = evs k fun j => (u j : C))
    (hlie : ∀ a, a ∈ lie ↔ ∀ u : Fin g → RC, ∑ k, a k * evr k (fun j => (u j : C)) ∈ RC)
    (hlW : lie ≤ W) (hWl : ∀ a ∈ W, w • a ∈ lie)
    (q : (Fin n → C) →ₗ[C] (Fin s → C))
    (hq : ∀ m, ∃ u : Fin g → RC, ∀ k,
      evs k (fun j => (Hm j m : C)) - q (fun i => (Pm i m : C)) k = p * evs k fun j => (u j : C))
    (i' hb : (Fin r → C) →ₗ[C] (Fin n → C))
    (hdual : ∀ a ∈ W, ∀ m, v (∑ m', (Eg m m' : C) * (Jm.map (algebraMap RC C) *ᵥ i' a) m' +
      ∑ k, a k * evr k fun j => (Hm j m : C)) ≤ v w)
    (hW : (stdLat RC _).comap hb.toAddMonoidHom = W) (hcl : ∀ a ∈ W, hb a - i' a ∈ mulLat w (stdLat RC _)) :
    hh.map q.toAddMonoidHom = om ∧ hh.comap hb.toAddMonoidHom = divLat w lie := by
  have hvw : v w ≠ 0 := (Valuation.ne_zero_iff v).2 hw0
  have hvw' : 0 < v w := pos_iff_ne_zero.2 hvw
  have hle : ∀ a : RC, v (a : C) ≤ 1 := fun a => (hv _).1 a.2
  have htw : v (p / w) ≤ v w := by rw [map_div₀, div_le_iff₀ hvw']; exact hpw
  let t : RC := ⟨p / w, (hv _).2 (htw.trans hw1.le)⟩
  have hint : ∀ x : I → C, (∀ l ∈ AF, v (∑ j, (l j : C) * x j) ≤ 1) → ∀ m, w * x m ∈ RC := fun x hx m => by
    have := hx _ (h0 (Pi.single m 1))
    rw [Finset.sum_eq_single m (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at this
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_mul, hc] at this
    rw [hv, map_mul]
    exact this
  have hev : ∀ (f : (Fin g → C) →ₗ[C] C) (x : I → C),
      f (Hm.map (algebraMap RC C) *ᵥ x) = ∑ m, x m * f fun j => (Hm j m : C) := fun f x => by
    have : Hm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun j => (Hm j m : C) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [this, map_sum]
    simp only [map_smul, smul_eq_mul]
  have key : ∀ x : I → C, (∀ m, w * x m ∈ RC) → ∃ u : Fin g → RC, ∀ k,
      q (Pm.map (algebraMap RC C) *ᵥ x) k = evs k (Hm.map (algebraMap RC C) *ᵥ x) - (t : C) * evs k fun j => (u j : C) := by
    intro x hx
    choose U hU using hq
    refine ⟨∑ m, (⟨_, hx m⟩ : RC) • U m, fun k => ?_⟩
    have e1 : Pm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun i => (Pm i m : C) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have e2 : (fun j => (((∑ m, (⟨_, hx m⟩ : RC) • U m) j : RC) : C)) = ∑ m, (w * x m) • fun j => (U m j : C) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
    rw [hev, e1, e2, map_sum, map_sum, Finset.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    have e3 : (t : C) * w = p := div_mul_cancel₀ p hw0
    linear_combination (-x m) * hU m k + (x m * evs k fun j => (U m j : C)) * e3
  have hPJ' : ∀ u : Fin n → C, Pm.map (algebraMap RC C) *ᵥ (Jm.map (algebraMap RC C) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPJ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hdot : ∀ {K : Type} [Fintype K] (l : I → RC) (M : Matrix I K RC) (x : K → C),
      ∑ j, (l j : C) * (M.map (algebraMap RC C) *ᵥ x) j = ∑ j, ((l ᵥ* M) j : C) * x j := fun l M x => by
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.map_apply, mul_assoc]
    exact Finset.sum_comm
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨u₀, hu₀, rfl⟩
    have hu := (hhh u₀).1 hu₀
    obtain ⟨u, e⟩ := key _ (hint _ fun l hl => (hv _).1 (hu l hl))
    rw [hPJ'] at e
    refine (hom _).2 ⟨(fun j => ⟨_, hu _ (h1 j)⟩) - t • u, fun k => (e k).trans ?_⟩
    rw [← smul_eq_mul, ← map_smul, ← map_sub]
    rfl
  · let N : Submodule RC (Fin g → RC) :=
      { carrier := {u | ∃ x ∈ hh, ∀ k, q x k = evs k fun j => (u j : C)}
        add_mem' := by
          rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
          refine ⟨x + y, hh.add_mem hx hy, fun k => ?_⟩
          rw [map_add, Pi.add_apply, ha, hb, ← map_add]
          rfl
        zero_mem' := ⟨0, hh.zero_mem, fun k => by rw [map_zero]; exact (map_zero (evs k)).symm⟩
        smul_mem' := by
          rintro a b ⟨x, hx, hb⟩
          refine ⟨(a : C) • x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩
          · convert RC.mul_mem a.2 ((hhh _).1 hx l hl) using 1
            simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
          · rw [map_smul, Pi.smul_apply, hb, ← map_smul]
            rfl }
    have hjac : Ideal.span {t} ≤ (⊥ : Ideal RC).jacobson := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_jacobson_bot]
      intro y
      have h1 : v ((t * y + 1 : RC) : C) = 1 := by
        rw [add_comm]
        refine v.map_one_add_of_lt ?_
        change v ((t : C) * y) < 1
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (htw.trans_lt hw1) (hle y)
      have h0 : ((t * y + 1 : RC) : C) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
      refine IsUnit.of_mul_eq_one ⟨((t * y + 1 : RC) : C)⁻¹, (hv _).2 (by rw [map_inv₀, h1, inv_one])⟩ ?_
      exact Subtype.ext (mul_inv_cancel₀ h0)
    have hN : (⊤ : Submodule RC (Fin g → RC)) ≤ N := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac fun u _ => ?_
      obtain ⟨x, hx, hxu⟩ := h4 u
      obtain ⟨u', e⟩ := key x (hint x hx)
      refine Submodule.mem_sup.2 ⟨u - t • u', ⟨Pm.map (algebraMap RC C) *ᵥ x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩,
        t • u', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top, sub_add_cancel _ _⟩
      · rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hdot]
        exact (hv _).2 (hx _ (hst l hl))
      · rw [e, hxu, ← smul_eq_mul, ← map_smul, ← map_sub]
        rfl
    intro z hz
    obtain ⟨u, hu⟩ := (hom z).1 hz
    obtain ⟨x, hx, e⟩ := hN (Submodule.mem_top (x := u))
    exact ⟨x, hx, funext fun k => (e k).trans (hu k).symm⟩
  · have est : ∀ a : Fin r → C, w • a ∈ W → ∀ y : I → RC,
        (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j ∈ RC ↔
          v (∑ k, (w • a) k * evr k fun j => ((Hm *ᵥ y) j : C)) ≤ v w) := by
      intro a ha y
      obtain ⟨z, hz, e⟩ := hcl _ ha
      have hz' : ∀ k, z k ∈ RC := fun k => hz k (Set.mem_univ k)
      have e1 : w • hb a = i' (w • a) + w • z := by
        rw [← map_smul hb, ← sub_eq_iff_eq_add', ← e]; rfl
      have e2 : w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j =
          ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
            w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j := by
        have := congrArg (fun x => ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ x) j) e1
        simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib, mul_left_comm _ w, ← Finset.mul_sum] using this
      have e3 : v (w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j) ≤ v w := by
        rw [map_mul]
        refine mul_le_of_le_one_right zero_le ((hv _).1 ?_)
        rw [hdot]
        exact RC.sum_mem fun j _ => RC.mul_mem (Subtype.prop _) (hz' j)
      have e4 : ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
          ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) =
          ∑ m, (y m : C) * (∑ m', (Eg m m' : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) m' +
            ∑ k, (w • a) k * evr k fun j => (Hm j m : C)) := by
        have : (fun j => ((Hm *ᵥ y) j : C)) = Hm.map (algebraMap RC C) *ᵥ fun m => (y m : C) := by
          funext j
          simp only [Matrix.mulVec, dotProduct, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, Matrix.map_apply]
          rfl
        rw [this, ← hdot]
        simp only [hev, mul_add, Finset.sum_add_distrib]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [mul_left_comm]
      have e5 : v (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
          ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C))) ≤ v w := by
        rw [e4]
        refine v.map_sum_le fun m _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left zero_le (hle _)).trans (hdual _ ha m)
      have e6 := v.map_add_le e5 e3
      rw [add_right_comm, ← e2] at e6
      rw [hv, ← mul_le_mul_iff_right₀ hvw', mul_one, ← map_mul]
      constructor
      · intro h
        simpa using v.map_sub_le e6 h
      · intro h
        simpa using v.map_sub_le e6 h
    have hlin : ∀ (a : Fin r → C) (b : RC) (u : Fin g → RC), ∑ k, a k * evr k (fun j => ((b • u) j : C)) =
        (b : C) * ∑ k, a k * evr k (fun j => (u j : C)) := fun a b u => by
      have : (fun j => ((b • u) j : C)) = (b : C) • fun j => (u j : C) := rfl
      simp only [this, map_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
    ext a
    change hb a ∈ hh ↔ w • a ∈ lie
    rw [hhh]
    constructor
    · intro h
      have ha : w • a ∈ W := by
        rw [← hW]
        intro k _
        have h5 := (hv _).1 (h _ (h0 (Pm k)))
        have h6 : ∑ j, ((c • Pm k) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j = (c : C) * hb a k := by
          conv_rhs => rw [← hPJ' (hb a)]
          generalize Jm.map (algebraMap RC C) *ᵥ hb a = x
          simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, MulMemClass.coe_mul, Finset.mul_sum,
            mul_assoc, Matrix.map_apply]
          rfl
        rw [h6, map_mul, hc, ← map_mul] at h5
        change hb (w • a) k ∈ RC
        rw [map_smul]
        exact (hv _).2 h5
      refine (hlie _).2 fun u => ?_
      obtain ⟨y, u', hy, e⟩ := h3 u
      have h5 := (est a ha y).1 (h _ hy)
      have h6 : ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) =
          (c : C) * ∑ k, (w • a) k * evr k (fun j => (u j : C)) +
            (p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C)) := by
        have : (fun j => ((c • u + P • u') j : C)) = (fun j => ((c • u) j : C)) + fun j => ((P • u') j : C) := rfl
        rw [e, this]
        simp only [map_add, mul_add, Finset.sum_add_distrib, hlin, hP]
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc w, ← Finset.mul_sum]
        field_simp
      have h7 : v ((p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C))) ≤ v w := by
        rw [map_mul]
        exact (mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 (hWl _ ha) u'))).trans htw
      rw [h6] at h5
      have h8 := v.map_sub_le h5 h7
      rw [add_sub_cancel_right, map_mul, hc] at h8
      rw [hv]
      exact (mul_le_iff_le_one_right hvw').1 h8
    · intro h l hl
      have hl' : (l ᵥ* Ei) ᵥ* Eg = l := by rw [Matrix.vecMul_vecMul, hEi, Matrix.vecMul_one]
      rw [← hl'] at hl ⊢
      obtain ⟨u, e⟩ := h2 _ hl
      rw [est a (hlW h), e, hlin, map_mul, hc]
      exact mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 h u))

end PositivityTheory.Xgn.TestGroupPoint
end
end

section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.FamEx PositivityTheory.HtPt.Sgp
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem bcLin_apply {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω))
    (x : Fin m → C) (k : Fin n) : TestPt.bcLin C f x k = ∑ i, algebraMap Ω C (f (Pi.single i 1) k) * x i := by
  simp only [TestPt.bcLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrix'_apply]
  try (refine Finset.sum_congr rfl fun i _ => ?_; congr 4; funext j; simp [Pi.single_apply])

theorem bcLin_bc {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω))
    (x : Fin m → Ω) (k : Fin n) : TestPt.bcLin C f (fun i => algebraMap Ω C (x i)) k = algebraMap Ω C (f x k) := by
  rw [bcLin_apply]
  have h := congrFun (LinearMap.toMatrix'_mulVec f x) k
  rw [← h]
  simp [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, map_sum, map_mul]

theorem isUnit_of_val {O C : Type} [CommRing O] [Field C] [Algebra O C] {RC : Subalgebra O C} {v : Valuation C NNReal}
    (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (a : RC) (ha : v (a : C) = 1) : IsUnit a := by
  have h0 : (a : C) ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact zero_ne_one ha
  have hi : (a : C)⁻¹ ∈ RC := (hv _).2 (by rw [map_inv₀, ha, inv_one])
  refine ⟨⟨a, ⟨_, hi⟩, ?_, ?_⟩, rfl⟩
  · ext
    simp [h0]
  · ext
    simp [h0]

theorem chi_cong {E : Type} [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {C : Type} [Field C] [Algebra O C] (RC : Subalgebra O C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1)
    {F : Type} [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F)
    (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (hsec : IsSec pq sc)
    (σF : F →+* IsLocalRing.ResidueField O) (χ : F →*₀ C)
    (hχ : ∀ a (o : O), IsLocalRing.residue O o = σF a →
      χ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ a - algebraMap O C o) ≠ 1)
    (σ : 𝓞 E →+* RC)
    (hσ : ∀ a, ∃ o : O, algebraMap O C o = σ a ∧ IsLocalRing.residue O o = σF (pq (Ideal.Quotient.mk _ a))) :
    ∃ χ' : F → RC, (∀ a, χ a = χ' a) ∧ ∀ a, χ' (pq (Ideal.Quotient.mk _ a)) - σ a ∈ Ideal.span {(p : RC)} := by
  have hmem : ∀ a, χ a ∈ RC := by
    intro a
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σF a)
    have h1 := (hχ a o ho).1
    have h2 : algebraMap O C o ∈ RC := RC.algebraMap_mem o
    simpa using RC.add_mem h1 h2
  refine ⟨fun a => ⟨χ a, hmem a⟩, fun a => rfl, ?_⟩
  intro a
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨f, -, hq⟩ := FiniteField.card F p
  set x := pq (Ideal.Quotient.mk _ a) with hx
  set c0 : RC := ⟨χ x, hmem x⟩ with hc0
  set d : RC := c0 - σ a with hd
  have hdn : ¬ IsUnit d := by
    obtain ⟨o, ho1, ho2⟩ := hσ a
    rintro ⟨u, hu⟩
    apply (hχ x o ho2).2 (((u⁻¹ : RCˣ) : RC) : C) ((u⁻¹ : RCˣ) : RC).2
    have h3 : ((u⁻¹ : RCˣ) : RC) * d = 1 := by rw [← hu]; simp
    have h4 := congrArg (fun r : RC => (r : C)) h3
    simp only [hd, hc0, Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one] at h4
    rw [ho1]
    exact h4
  have hvd : v (d : C) < 1 := by
    refine lt_of_le_of_ne ((hv _).1 d.2) ?_
    intro h
    exact hdn (isUnit_of_val hv d h)
  by_cases hpu : IsUnit (p : RC)
  · rw [Ideal.span_singleton_eq_top.mpr hpu]
    trivial
  haveI : CharP (RC ⧸ Ideal.span {(p : RC)}) p := CharP.quotient RC p hpu
  have hσq : σ a ^ Fintype.card F - σ a ∈ Ideal.span {(p : RC)} := by
    obtain ⟨e', he'⟩ := Ideal.Quotient.mk_surjective (sc 1)
    have hker : (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) (a ^ Fintype.card F - a)) * sc 1 = 0 := by
      apply hsec.2
      simp [map_sub, map_pow, FiniteField.pow_card]
    rw [← he', ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hker
    obtain ⟨c, hc⟩ := hker
    have hσe : IsUnit (σ e') := by
      obtain ⟨o, ho1, ho2⟩ := hσ e'
      have hres : IsLocalRing.residue O o ≠ 0 := by
        rw [ho2, he', hsec.1, map_one]
        exact one_ne_zero
      have hu := (IsLocalRing.residue_ne_zero_iff_isUnit o).1 hres
      have h5 : σ e' = algebraMap O RC o := Subtype.ext (by rw [← ho1]; rfl)
      rw [h5]
      exact hu.map _
    obtain ⟨w, hw⟩ := hσe
    have h2 := congrArg σ hc
    simp only [map_mul, map_sub, map_pow, map_natCast] at h2
    have h6 : σ a ^ Fintype.card F - σ a = (p : RC) * (σ c * ↑w⁻¹) := by
      calc σ a ^ Fintype.card F - σ a = (σ a ^ Fintype.card F - σ a) * σ e' * ↑w⁻¹ := by
            rw [← hw, mul_assoc, Units.mul_inv, mul_one]
        _ = _ := by rw [h2, mul_assoc]
    rw [h6]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hχq : c0 ^ Fintype.card F = c0 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hc0]
    show χ x ^ Fintype.card F = χ x
    rw [← map_pow, FiniteField.pow_card]
  have key : ∀ y z : RC ⧸ Ideal.span {(p : RC)}, (y - z) ^ Fintype.card F = y ^ Fintype.card F - z ^ Fintype.card F := by
    intro y z
    rw [hq]
    exact sub_pow_char_pow y z f
  have hdq : d ^ Fintype.card F - d ∈ Ideal.span {(p : RC)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hσq ⊢
    rw [map_sub, map_pow] at hσq
    rw [map_sub, map_pow, hd, map_sub, key, ← map_pow, hχq, sub_eq_zero.mp hσq]
    ring
  have hunit : IsUnit (d ^ (Fintype.card F - 1) - 1) := by
    apply isUnit_of_val hv
    have h7 : ((d ^ (Fintype.card F - 1) - 1 : RC) : C) = (d : C) ^ (Fintype.card F - 1) - 1 := by
      push_cast
      rfl
    rw [h7, Valuation.map_sub_eq_of_lt_right, map_one]
    rw [map_one, map_pow]
    exact pow_lt_one₀ zero_le' hvd (by omega)
  obtain ⟨w, hw⟩ := hunit
  have e1 : d ^ Fintype.card F - d = d * (d ^ (Fintype.card F - 1) - 1) := by
    conv_lhs => rw [show Fintype.card F = (Fintype.card F - 1) + 1 by omega]
    ring
  have h8 : d = (d ^ Fintype.card F - d) * ↑w⁻¹ := by
    rw [e1, ← hw, mul_assoc, Units.mul_inv, mul_one]
  rw [h8]
  exact Ideal.mul_mem_right _ _ hdq

theorem gram_cong {E : Type} [Field E] [NumberField E] {R : Type} [CommRing R] {p Rr n : ℕ} [Fact p.Prime] (hRr : 1 ≤ Rr)
    (e : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) →+ ZMod (p ^ Rr)) (alt : ∀ x, e x x = 0) (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a, bar (bar a) = a) (hadj : ∀ a x y, e (a • x) y = e x (bar a • y)) (Eg : Matrix (Ix E n) (Ix E n) R)
    (hE : ∀ m m', Eg m m' - ((e (dl m) (dl m')).val : R) ∈ Ideal.span {(p : R)}) {σ' : 𝓞 E →+* R}
    {s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R} (hd : IsDualOf σ' s) (x' : Fin n → R) (m : Ix E n) :
    ∑ m', Eg m m' * (s m'.2 * x' m'.1) + σ' (bar (RingOfIntegers.basis E m.2)) * ∑ l, x' l * ∑ k, s k *
      ((e (Pi.single l (RingOfIntegers.basis E k)) (Pi.single m.1 1)).val : R) ∈ Ideal.span {(p : R)} := by
  by_cases hpu : IsUnit (p : R)
  · rw [Ideal.span_singleton_eq_top.mpr hpu]
    trivial
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p hpu
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ Rr) := ⟨pow_ne_zero _ hp0⟩
  let mk := Ideal.Quotient.mk (Ideal.span {(p : R)})
  let φ : ZMod (p ^ Rr) →+* (R ⧸ Ideal.span {(p : R)}) := ZMod.castHom (dvd_pow_self p (by omega)) _
  have hφ : ∀ z : ZMod (p ^ Rr), mk (z.val : R) = φ z := by
    intro z
    show _ = ZMod.cast z
    rw [map_natCast, ZMod.cast_eq_val]
  have hskew : ∀ x y, e x y = - e y x := by
    intro x y
    have h := alt (x + y)
    simp only [map_add, AddMonoidHom.add_apply, alt x, alt y, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)
  set B := RingOfIntegers.basis E with hB
  let L : Fin n → 𝓞 E →+ (R ⧸ Ideal.span {(p : R)}) := fun l =>
    φ.toAddMonoidHom.comp ((e.flip (Pi.single m.1 1)).comp (AddMonoidHom.single (fun _ => 𝓞 E) l))
  have hL : ∀ l c, L l c = φ (e (Pi.single l c) (Pi.single m.1 1)) := fun l c => rfl
  have hswap : ∀ l k, φ (e (dl m) (Pi.single l (B k))) = - L l (bar (B m.2) * B k) := by
    intro l k
    rw [hL, hskew, map_neg]
    congr 2
    have h1 : dl m = B m.2 • (Pi.single m.1 1 : Fin n → 𝓞 E) := by
      funext t
      by_cases h : t = m.1 <;> simp [dl, Pi.single_apply, h, hB]
    have h2 : (Pi.single l (bar (B m.2) * B k) : Fin n → 𝓞 E) = bar (B m.2) • (Pi.single l (B k) : Fin n → 𝓞 E) := by
      funext t
      by_cases h : t = l <;> simp [Pi.single_apply, h]
    rw [h1, h2, hadj, hbar]
  have hexp : ∀ l c, L l c = ∑ t, ((B.repr c t : ℤ) : R ⧸ Ideal.span {(p : R)}) * L l (B t) := by
    intro l c
    conv_lhs => rw [← B.sum_repr c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
  have hdual : ∀ l, ∑ k, mk (s k) * L l (bar (B m.2) * B k) = mk (σ' (bar (B m.2))) * ∑ t, mk (s t) * L l (B t) := by
    intro l
    have hx : ∀ k, L l (bar (B m.2) * B k) = ∑ t, ((B.repr (bar (B m.2) * B k) t : ℤ) : R ⧸ Ideal.span {(p : R)}) * L l (B t) :=
      fun k => hexp l _
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h3 := congrArg mk (hd.2 (bar (B m.2)) t)
    simp only [map_mul, map_sum, map_intCast] at h3
    rw [← mul_assoc, h3, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hE' : ∀ m', mk (Eg m m') = φ (e (dl m) (dl m')) := by
    intro m'
    rw [← hφ]
    exact Ideal.Quotient.eq.mpr (hE m m')
  have hfirst : ∀ l, ∑ k, φ (e (dl m) (Pi.single l (B k))) * (mk (s k) * mk (x' l)) =
      - (mk (σ' (bar (B m.2))) * (mk (x' l) * ∑ k, mk (s k) * L l (B k))) := by
    intro l
    simp_rw [hswap l]
    calc ∑ k, -L l (bar (B m.2) * B k) * (mk (s k) * mk (x' l))
        = -(mk (x' l) * ∑ k, mk (s k) * L l (bar (B m.2) * B k)) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = _ := by
          rw [hdual l]
          ring
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change mk _ = 0
  simp only [map_add, map_sum, map_mul, hE', hφ]
  rw [Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro l _
  change ∑ k, φ (e (dl m) (Pi.single l (B k))) * (mk (s k) * mk (x' l)) +
    mk (σ' (bar (B m.2))) * (mk (x' l) * ∑ k, mk (s k) * L l (B k)) = 0
  rw [hfirst l]
  exact neg_add_cancel _

section Chart

variable {E : Type} [Field E] [NumberField E] {O Ω C Li : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω]
  [Algebra O C] [Algebra Ω C] [AddCommGroup Li] [Module Ω Li] {R : Subalgebra O Ω} {RC : Subalgebra O C}
  {hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC} {cc : E ≃+* E} {p Rr n g : ℕ}
  (Dh : HT.HTChart R Ω cc p Rr n (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li) (bar : 𝓞 E ≃+* 𝓞 E)
  (io : Dh.om →ₛₗ[toRC R RC hR] (Fin g → RC)) (ev : Li → ((Fin g → C) →ₗ[C] C))
  (Hm : Matrix (Fin g) (Ix E n) RC)

theorem ev_col (hRr : 1 ≤ Rr) (hact : ∀ a u, Dh.ρΩ a u = u ∘ₗ ρ (bar a))
    (hev : ∀ v (u : Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (hH : ∀ m k, Hm k m - io ⟨Dh.h (dl m), Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)}) (m : Ix E n) :
    ∃ u : Fin g → RC, ∀ (V : Li) (t : Ω), ρ (bar (RingOfIntegers.basis E m.2)) V = t • V →
      ev V (fun j => (Hm j m : C)) =
        algebraMap Ω C (t * Dh.h (Pi.single m.1 1) V) + (p : C) * ev V fun j => (u j : C) := by
  choose w hw using fun k => Ideal.mem_span_singleton.1 (hH m k)
  obtain ⟨y, hy, hyeq⟩ := Dh.h_lin (RingOfIntegers.basis E m.2) (Pi.single m.1 1)
  refine ⟨fun k => w k + (p : RC) ^ (Rr - 1) * io ⟨y, hy⟩ k, ?_⟩
  intro V t hV
  have hdl : dl m = RingOfIntegers.basis E m.2 • (Pi.single m.1 1 : Fin n → 𝓞 E) := by
    funext j
    by_cases h : j = m.1 <;> simp [dl, Pi.single_apply, h]
  have hvec : (fun j => (Hm j m : C)) =
      (fun j => (io ⟨Dh.h (dl m), Dh.h_mem _⟩ j : C)) + (p : C) • (fun j => (w j : C)) := by
    funext j
    have h1 := congrArg (fun r : RC => (r : C)) (hw j)
    push_cast at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h1
  have hvec2 : (fun j => ((w j + (p : RC) ^ (Rr - 1) * io ⟨y, hy⟩ j : RC) : C)) =
      (fun j => (w j : C)) + ((p : C) ^ (Rr - 1)) • (fun j => (io ⟨y, hy⟩ j : C)) := by
    funext j
    simp
  have hhV : Dh.h (dl m) V = t * Dh.h (Pi.single m.1 1) V + (p : Ω) ^ Rr * y V := by
    rw [hdl, hyeq]
    simp [hact, hV, nsmul_eq_mul]
  rw [hvec, hvec2, map_add, map_smul, map_add, map_smul, hev, hev, smul_eq_mul, smul_eq_mul, hhV]
  have hRr' : (p : C) ^ Rr = p * p ^ (Rr - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  simp only [map_add, map_mul, map_pow, map_natCast]
  rw [hRr']
  ring

theorem hq_chart (hRr : 1 ≤ Rr) (hact : ∀ a u, Dh.ρΩ a u = u ∘ₗ ρ (bar a))
    (hev : ∀ v (u : Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (hH : ∀ m k, Hm k m - io ⟨Dh.h (dl m), Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)})
    (σ : E →+* Ω) (σ' : 𝓞 E →+* RC) (hσ : ∀ a, (σ' a : C) = algebraMap Ω C (σ a)) {s : ℕ} (vs : Fin s → Li)
    (hvs : ∀ a k, ρ (bar a) (vs k) = σ a • vs k) (m : Ix E n) :
    ∃ u : Fin g → RC, ∀ k, ev (vs k) (fun j => (Hm j m : C)) -
      TestPt.bcLin C (Fintype.linearCombination Ω fun (i : Fin n) (k : Fin s) => Dh.h (Pi.single i 1) (vs k))
        (fun i => ((Pm n σ' i m : RC) : C)) k = (p : C) * ev (vs k) fun j => (u j : C) := by
  obtain ⟨u, hu⟩ := ev_col Dh ρ bar io ev Hm hRr hact hev hH m
  refine ⟨u, fun k => ?_⟩
  rw [hu _ _ (hvs _ k), bcLin_apply, Finset.sum_eq_single m.1 (fun i _ hi => by simp [Pm, hi.symm]) (by simp)]
  simp [Pm, hσ, mul_comm]

theorem hdual_chart [Fact p.Prime] (hRr : 1 ≤ Rr) (hact : ∀ a u, Dh.ρΩ a u = u ∘ₗ ρ (bar a))
    (hev : ∀ v (u : Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (hH : ∀ m k, Hm k m - io ⟨Dh.h (dl m), Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)})
    (hbar : ∀ a, bar (bar a) = a) (hadj : ∀ a x y, Dh.e (a • x) y = Dh.e x (bar a • y))
    (Eg : Matrix (Ix E n) (Ix E n) RC)
    (hE : ∀ m m', Eg m m' - ((Dh.e (dl m) (dl m')).val : RC) ∈ Ideal.span {(p : RC)})
    (σ : E →+* Ω) (σ' : 𝓞 E →+* RC) (hσ : ∀ a, (σ' a : C) = algebraMap Ω C (σ a))
    (s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → RC) (hs : ∀ k, (s k : C) = algebraMap Ω C (σ (HT.dualInt E k)))
    (hd : IsDualOf σ' s) {r : ℕ} (b : Fin r → Li) (hb : ∀ a k, ρ a (b k) = σ a • b k)
    (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (w : C) (hw0 : w ≠ 0) (hw1 : v w ≤ 1)
    (hpw : v (p : C) ≤ v w * v w) (a : Fin r → Ω) (x : Fin n → Ω) (hx : ∀ l, x l ∈ R) {M : ℕ} (hM : 1 ≤ M)
    (hseq : ∀ j, ∃ z ∈ R, ∑ l, x l * Dh.gram σ 1 l j = Dh.h (Pi.single j 1) (∑ k, a k • b k) + (p : Ω) ^ M * z)
    (ha : ∀ u : Fin g → RC, ∑ k, (w * algebraMap Ω C (a k)) * ev (b k) (fun j => (u j : C)) ∈ RC) (m : Ix E n) :
    v (∑ m', (Eg m m' : C) * ((Jm n s).map (algebraMap RC C) *ᵥ fun l => algebraMap Ω C (x l)) m' +
      ∑ k, algebraMap Ω C (a k) * ev (b k) fun j => (Hm j m : C)) ≤ v w := by
  set Bj := RingOfIntegers.basis E m.2 with hBj
  let x' : Fin n → RC := fun l => toRC R RC hR ⟨x l, hx l⟩
  have hx' : ∀ l, (x' l : C) = algebraMap Ω C (x l) := fun l => rfl
  have hP1 := gram_cong hRr Dh.e Dh.alt bar hbar hadj Eg hE hd x' m
  obtain ⟨c1, hc1⟩ := Ideal.mem_span_singleton.1 hP1
  obtain ⟨u, hu⟩ := ev_col (Dh := Dh) (ρ := ρ) (bar := bar) (io := io) (ev := ev) (Hm := Hm) hRr hact hev hH m
  obtain ⟨z, hz, hzeq⟩ := hseq m.1
  set t : Ω := σ ((bar Bj : 𝓞 E) : E) with ht
  have hσ' : (σ' (bar Bj) : C) = algebraMap Ω C t := hσ _
  set S : C := ∑ k, algebraMap Ω C (a k) * ev (b k) (fun j => (u j : C)) with hS
  set G : C := ∑ l, algebraMap Ω C (x l) * ∑ k, (s k : C) *
    (((Dh.e (Pi.single l (RingOfIntegers.basis E k))) (Pi.single m.1 1)).val : C) with hGdef
  have hF1 : ∀ m', ((Jm n s).map (algebraMap RC C) *ᵥ fun l => algebraMap Ω C (x l)) m' =
      (s m'.2 : C) * algebraMap Ω C (x m'.1) := by
    intro m'
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Jm]
    rw [Finset.sum_eq_single m'.1]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
  have hc1C : ∑ m', (Eg m m' : C) * ((s m'.2 : C) * algebraMap Ω C (x m'.1)) + (σ' (bar Bj) : C) * G =
      (p : C) * (c1 : C) := by
    have h1 := congrArg (fun r : RC => (r : C)) hc1
    push_cast at h1
    simpa [hx', hGdef] using h1
  have hG : G = algebraMap Ω C (∑ l, x l * Dh.gram σ 1 l m.1) := by
    simp only [hGdef, HT.HTChart.gram, map_one, one_mul, map_sum, map_mul, map_natCast, hs]
  have hzC : algebraMap Ω C (∑ l, x l * Dh.gram σ 1 l m.1) =
      algebraMap Ω C (Dh.h (Pi.single m.1 1) (∑ k, a k • b k)) + (p : C) ^ M * algebraMap Ω C z := by
    rw [hzeq, map_add, map_mul, map_pow, map_natCast]
  have hsec : ∑ k, algebraMap Ω C (a k) * ev (b k) (fun j => (Hm j m : C)) =
      algebraMap Ω C t * algebraMap Ω C (Dh.h (Pi.single m.1 1) (∑ k, a k • b k)) + (p : C) * S := by
    rw [Finset.sum_congr rfl fun k _ => by rw [hu (b k) t (hb _ k)]]
    simp only [hS, map_sum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hT : ∑ m', (Eg m m' : C) * ((Jm n s).map (algebraMap RC C) *ᵥ fun l => algebraMap Ω C (x l)) m' +
      ∑ k, algebraMap Ω C (a k) * ev (b k) (fun j => (Hm j m : C)) =
      (p : C) * (c1 : C) - algebraMap Ω C t * ((p : C) ^ M * algebraMap Ω C z) + (p : C) * S := by
    simp only [hF1]
    rw [hsec]
    linear_combination hc1C - G * hσ' - algebraMap Ω C t * hG - algebraMap Ω C t * hzC
  rw [hT]
  have hvp : v (p : C) ≤ 1 := (hv _).1 (by simpa using (p : RC).2)
  have hvpw : v (p : C) ≤ v w := le_trans hpw (by
    calc v w * v w ≤ v w * 1 := by gcongr
      _ = v w := mul_one _)
  have hvc : v (c1 : C) ≤ 1 := (hv _).1 c1.2
  have hvt : v (algebraMap Ω C t) ≤ 1 := by
    rw [← hσ']
    exact (hv _).1 (σ' (bar Bj)).2
  have hvz : v (algebraMap Ω C z) ≤ 1 := (hv _).1 (hR z hz)
  have hwS : v w * v S ≤ 1 := by
    rw [← map_mul]
    apply (hv _).1
    have h2 := ha u
    convert h2 using 1
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  apply Valuation.map_add_le
  · apply Valuation.map_sub_le
    · rw [map_mul]
      calc v (p : C) * v (c1 : C) ≤ v (p : C) * 1 := by gcongr
        _ ≤ v w := by rw [mul_one]; exact hvpw
    · rw [map_mul, map_mul, map_pow]
      calc v (algebraMap Ω C t) * (v (p : C) ^ M * v (algebraMap Ω C z)) ≤ 1 * (v (p : C) ^ M * 1) := by
            gcongr
        _ = v (p : C) ^ M := by ring
        _ ≤ v (p : C) := pow_le_of_le_one zero_le' hvp (by omega)
        _ ≤ v w := hvpw
  · rw [map_mul]
    calc v (p : C) * v S ≤ (v w * v w) * v S := by gcongr
      _ = v w * (v w * v S) := by ring
      _ ≤ v w * 1 := by gcongr
      _ = v w := mul_one _

end Chart

end PositivityTheory.Xgn.TestGroupPoint
end
end

section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestGroupPoint

theorem spanOver_ind {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) (T : AddSubgroup (Fin r → C)) (hT : ∀ t ∈ RC, ∀ a ∈ T, t • a ∈ T)
    (h : ∀ a ∈ L, (fun k => algebraMap Ω C (a k)) ∈ T) : spanOver RC (bcMap Ω C _ '' L) ≤ T := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨t, ht, _, ⟨a, ha, rfl⟩, rfl⟩
  exact hT t ht _ (h a ha)

theorem mem_spanOver {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) {a : Fin r → Ω} (ha : a ∈ L) :
    (fun k => algebraMap Ω C (a k)) ∈ spanOver RC (bcMap Ω C _ '' L) :=
  AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨a, ha, rfl⟩, (one_smul _ _).symm⟩

def smallSub {C : Type} [Field C] (v : Valuation C NNReal) (t : NNReal) {r : ℕ} {I : Type}
    (f : I → ((Fin r → C) →ₗ[C] C)) : AddSubgroup (Fin r → C) where
  carrier := {a | ∀ m, v (f m a) ≤ t}
  add_mem' ha hb m := by rw [map_add]; exact v.map_add_le (ha m) (hb m)
  zero_mem' m := by simp
  neg_mem' ha m := by rw [map_neg, Valuation.map_neg]; exact ha m

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a :=
  RingOfIntegers.ext (by rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])

end PositivityTheory.Xgn.TestGroupPoint

open PositivityTheory.Xgn.TestGroupPoint PositivityTheory.HtPt.Sgp in
theorem PositivityTheory.Xgn.test_group_point_exists : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  intro hF _ _ hHD hOC E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd hpq p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _
    hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σF hO hsec G c' hc' P i hseq hbase C _ _ _ _ RC hT χ hχ _ _ _ v hv hvp
    τ hbm _ _ hW hcl
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hR4 := 𝔐.R_ge p hpS
  obtain ⟨h0, hNoe, hIC, hFr⟩ := Par.chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  obtain ⟨-, hN, -⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (Par.zp Ω p) (Par.mem_range_zp Ω p)
  obtain ⟨AA, AW, hAA, hAW, hM, hret, -⟩ := PositivityTheory.Xgn.test_order_sections E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ
  obtain ⟨-, htight⟩ := GlobalTheory.T.arith_variety_model_hodge_relay hHD hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ v hv hvp
  obtain ⟨g, io, ev, Hm, Eg, hio, hev, hcard, hEt, ⟨Ei, hEi, hiso⟩, hE, hH⟩ :=
    point_data hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC w hO.2.2.2.2.2.2.2 hT
  obtain ⟨Dv, hD, hDs, hDch⟩ := exists_der hpS P hT.2.2.2 io
  have hlat := fun t => lattices E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC hdisc
    hT.2.2.2 io ev hio hev t (b t) (hb t).1 (hb t).2
  haveI := hT.1
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap Ω C).injective
  have hint : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  obtain ⟨φN, hφN⟩ := exists_phiN E (D.p + D.q) p
  have hζ : IsPrimitiveRoot (algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1))) p :=
    (G.ζ_prim.pow (pow_pos hpp.pos _) (by rw [← pow_succ, Nat.sub_add_cancel (by omega)])).map_of_injective
      (algebraMap Ω C).injective
  let ih : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin g → RC) := io.toAddMonoidHom.comp (P.Dh.h.codRestrict P.Dh.om P.Dh.h_mem)
  obtain ⟨cp, hcp, k0, k1, k2, k3, k4⟩ := core_pull hint hvp hp2 φN hφN AA _ hAA htight hcard
    (dvd_pow_self p (show 𝔐.R p ≠ 0 by omega)) G.e hζ (kernel_mem hpS P hT) Dv hD (Set.range io) hio
    (by rintro _ ⟨u, rfl⟩; exact hDs u) ih hDch Hm Eg Ei hEt hEi hiso hE hH
  obtain ⟨σ, hσ, hσs, -⟩ := PositivityTheory.Xgn.exists_cm_type_embedding E H D l Xo c O₀ β Y S Ω K J y 𝔐 (e τ)
  obtain ⟨hσO, x₀, hx₀, o₀, ho₀⟩ := PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hdisc A m hpm O σ
  have hOC' : ∀ o : O, algebraMap Ω C (algebraMap O Ω o) = algebraMap O C o := fun o =>
    (IsScalarTower.algebraMap_apply O Ω C o).symm
  obtain ⟨σ', s, hσ', hs, hdu⟩ := exists_dualOf (R := RC) (C := C) Subtype.val_injective ((algebraMap Ω C).comp σ)
    (fun a => by
      obtain ⟨o, ho⟩ := hσO a
      exact ⟨algebraMap O RC o, by rw [RingHom.comp_apply, ← ho, hOC']; rfl⟩)
    (fun k => by
      obtain ⟨z, hz⟩ := HT.exists_different_mul_dualInt E x₀ hx₀ k
      obtain ⟨o, ho⟩ := hσO z
      refine ⟨algebraMap O RC (o₀ * o), ?_⟩
      have : algebraMap O Ω (o₀ * o) = σ (HT.dualInt E k) := by
        rw [map_mul, ho, hz, map_mul, ← _root_.mul_assoc, ho₀, _root_.one_mul]
      rw [RingHom.comp_apply, ← this, hOC']; rfl)
  obtain ⟨χ', hχ', hcong⟩ := chi_cong p RC v hv pq sc hsec (σF τ) (χ τ) (hχ τ) σ' fun a => by
    obtain ⟨o, ho, ho'⟩ := hO.2.2.2.2.1 τ a
    exact ⟨o, by rw [← hOC', ho, ← hσ]; exact (hσ' a).symm, ho'⟩
  have hst := afLat_stable hdu φN hφN AA.carrier (fun a f hf => by rw [hAA] at hf ⊢; exact act_mem P a f hf) _
    (mem_pull φN AA)
  have hhh := (pt_af_type_main RC p (ReciprocityTheory.PGsh.Up.hopfPull φN AA).carrier (ReciprocityTheory.PGsh.Up.hopfPull φN AA).le_int
    ((chartD e b pq sc w P i).bc RC) χ' (Subtype.ext (by rw [← hχ', map_zero]; rfl))
    (Subtype.ext (by rw [← hχ', map_one]; rfl))
    (φN.symm.toAddMonoidHom.comp (TestPt.toNAdd sc)) ((TestPt.fromNAdd pq).comp φN.toAddMonoidHom)
    (fun z => by
      change TestPt.fromNAdd pq (φN (φN.symm (TestPt.toNAdd sc z))) = z
      rw [AddEquiv.apply_symm_apply]
      exact funext fun k => hsec.1 (z k))
    (fun h hh => by
      obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
      refine (mem_pull φN AA _).2 ⟨_, hret f hf, funext fun x => ?_⟩
      change _ = f (φN (φN.symm _))
      rw [AddEquiv.apply_symm_apply]
      rfl)
    (by
      rw [← hM, hAW, TestPt.testOrdW, ← hAA]
      congr 1
      ext f
      constructor
      · rintro ⟨h, hh, rfl⟩
        obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
        refine ⟨f, hf, funext fun x => ?_⟩
        change _ = f (φN (φN.symm _))
        rw [AddEquiv.apply_symm_apply]
        rfl
      · rintro ⟨f, hf, rfl⟩
        refine ⟨_, (mem_pull φN AA _).2 ⟨f, hf, rfl⟩, funext fun x => ?_⟩
        change f (φN (φN.symm _)) = _
        rw [AddEquiv.apply_symm_apply]
        rfl)
    (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) (Pm_cong pq φN hφN χ' hcong) hst).2
  simp only [← hχ'] at hhh
  obtain ⟨u, hu, hwu⟩ := hO.2.2.2.2.2.2.1.2.1
  have hp3 : 2 ≤ p - 1 := by have := hpp.two_le; omega
  have hvw : v (algebraMap O C w) ^ (p - 1) = v (p : C) := by
    rw [← map_pow, ← map_pow, hwu, map_mul, map_mul, map_natCast,
      show v (algebraMap O C u) = 1 from hint.one_of_isUnit (hu.map (algebraMap O RC)), _root_.one_mul]
  have hw1 : v (algebraMap O C w) < 1 := lt_of_not_ge fun h => absurd (hvw ▸ one_le_pow₀ h) (not_le.2 hvp)
  have hw0 : algebraMap O C w ≠ 0 := fun h => by
    rw [h, map_zero, zero_pow (by omega), eq_comm, Valuation.zero_iff] at hvw
    exact Nat.cast_ne_zero.2 hpp.ne_zero hvw
  have hpw : v (p : C) ≤ v (algebraMap O C w) * v (algebraMap O C w) := by
    rw [← hvw, ← sq]
    exact pow_le_pow_of_le_one zero_le hw1.le hp3
  have hWl : ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, algebraMap O C w • a ∈ ((chartD e b pq sc w P i).bc RC).lie τ :=
    fun a ha => spanOver_ind RC _ (divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ))
      (fun t ht a ha => by
        simp only [divLat, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply] at ha ⊢
        rw [smul_comm]
        exact smul_mem_spanOver RC _ ht ha)
      (fun a ha => by
        have h1 : algebraMap O Ω w • a ∈ (chartD e b pq sc w P i).lie τ := (hbase.incl τ).2.1 ha
        have h2 := mem_spanOver RC _ h1
        have e : algebraMap O C w • (fun k => algebraMap Ω C (a k)) =
            fun k => algebraMap Ω C ((algebraMap O Ω w • a) k) := by
          funext k
          change _ = algebraMap Ω C (algebraMap O Ω w * a k)
          rw [map_mul, hOC']
          rfl
        simp only [divLat, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply]
        rw [e]
        exact h2) ha
  have heig : ∀ t a k, 𝔐.ρ a (b t k) = 𝔐.emb t a • b t k := fun t a k => by
    have : b t k ∈ 𝔐.Vgen t := (hb t).2 ▸ Submodule.subset_span ⟨k, rfl⟩
    simp only [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      sub_eq_zero] at this
    exact this a
  refine typed RC v hv (p : C) (algebraMap O C w) hw0 hw1 hpw cp (p : RC)
    ((pow_left_inj₀ zero_le zero_le (by omega)).1 (hcp.trans hvw.symm)) (SubringClass.coe_natCast _ _) _ Hm Eg Ei hEi
    k0 k1 k2 k3 k4 (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) hst _ hhh (fun k => ev (b (e τ).swap k)) (fun k => ev (b (e τ) k))
    _ _ _ (hlat (e τ).swap).1 (hlat (e τ)).2
    (spanOver_ind RC _ _ (fun t ht a ha => smul_mem_spanOver RC _ ht ha) fun a ha =>
      mem_spanOver RC _ ((hbase.incl τ).1 ha)) hWl _
    (hq_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH σ σ' hσ' (b (e τ).swap) fun a k => ?_)
    (TestPt.bcLin C (i τ)) hbm (fun a ha => ?_) hW hcl
  · rw [heig, ← hσs, H.bar_eq, RingHom.comp_apply]
    congr 2
    first
      | exact IsCMField.complexConj_apply_apply E _
      | simp [HT.cmConj]
  · let f : Ix E (D.p + D.q) → ((Fin (labelRk D (e τ)) → C) →ₗ[C] C) := fun m =>
      ∑ m', (Eg m m' : C) • (LinearMap.proj m' ∘ₗ ((Jm _ s).map (algebraMap RC C)).mulVecLin ∘ₗ TestPt.bcLin C (i τ)) +
        ∑ k, ev (b (e τ) k) (fun j => (Hm j m : C)) • LinearMap.proj k
    have hf : ∀ m a, f m a = ∑ m', (Eg m m' : C) * ((Jm _ s).map (algebraMap RC C)).mulVec (TestPt.bcLin C (i τ) a) m' +
        ∑ k, a k * ev (b (e τ) k) fun j => (Hm j m : C) := fun m a => by
      simp only [f, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Matrix.mulVecLin_apply, smul_eq_mul, mul_comm (a _)]
    intro m
    rw [← hf]
    refine spanOver_ind RC _ (smallSub v (v (algebraMap O C w)) f) (fun t ht a ha m => ?_) (fun a ha m => ?_) ha m
    · rw [map_smul, smul_eq_mul, map_mul]
      exact (mul_le_of_le_one_left zero_le ((hv _).1 ht)).trans (ha m)
    · rw [hf, show TestPt.bcLin C (i τ) (fun k => algebraMap Ω C (a k)) = fun l => algebraMap Ω C (i τ a l) from
        funext (bcLin_bc _ _)]
      exact hdual_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH (bar_bar H)
        (by rw [P.Dh_e]; exact G.adj) Eg (by rw [P.Dh_e]; exact hE) σ σ' hσ' s hs hdu (b (e τ))
        (fun a k => by rw [heig, hσ]) v hv _ hw0 hw1.le hpw a (i τ a)
        (fun l => (hseq τ).1.1 a ha l (Set.mem_univ l)) (M := 𝔐.R p - 2) (by omega) ((hseq τ).2 σ hσ a ha)
        ((hlat (e τ)).2 _ |>.1 (hWl _ (mem_spanOver RC _ ha))) m
end
