import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralIndependentOfCoefficient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionalChernIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbar

section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.EigWhole

variable {D : D7} (O : Setup D)

abbrev Var : Type := DV.Rt D.what₂.Tau O.N ⊕ (Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))

def fam (T : Finset ℕ) (R : ℝ) : Var O → Sym D.host.E →₀ ℤ
  | .inl x => rootSym O.S.Dw (ArIn.ind T) (some R) (DV.tauEmb D x.1) x.2
  | .inr l => wholeSym (ArIn.ind T) (some R) l

def diffPol : MvPolynomial (Var O) ℝ :=
  (C (1 / 2 : ℝ) * ∑ l, X (Sum.inr l) ^ 2 - ∑ x, X (Sum.inl x) ^ 2) *
    rename Sum.inl (curveCl D.what₂.Tau O.N O.j)

def AwayAgree (T : Finset ℕ) (R : ℝ) (c : O.s.Comp) : Prop :=
  ∀ (k : ℕ) (z : Letter O.S.Dw), (letters O.S.Dw)[k]? = some z →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (ε : GlobalTheory.TrueGeo.Ext v) (y : GlobalTheory.TrueGeo.AlgPt (O.var c)),
      ¬ resP v ∣ (NumberField.discr D.host.E).natAbs →
      lgOf (O.Φ.C c) (Finsupp.single (ArIn.ind T, some R, .inr k) 1) v ε y =
        lgOf (O.Φ.C c) (Finsupp.single (ArIn.ind T, some R, .inl (z.1, (z.2 : ℕ))) 1) v ε y

end GlobalTheory.EigWhole

namespace GlobalTheory.EigWhole

def RamModel : Prop :=
  ∀ (D : D7) (O : Setup D), O.Core → ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → ∀ c : O.s.Comp,
    AwayAgree O (Pad.setB O.κ B) R c →
    ∀ (M : GlobalTheory.TrueGeo.Model (O.var c)) (L : Var O → GlobalTheory.HermLB M.p) (m : ℕ+)
      (Ψ : MvPolynomial (Var O) ℝ →ₗ[ℝ] ℝ),
      (∀ i, (adlOf (O.Φ.C c) (O.met.hm c) (fam O (Pad.setB O.κ B) R i)).Induced M (L i) m 0) →
      (haveI := M.ar.isIntegral; GlobalTheory.ArInt.IsArFun L (O.var c).dim Ψ) →
      Ψ (diffPol O) = 0

end GlobalTheory.EigWhole

end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open Filter Topology

namespace GlobalTheory.LatChain

section Alg

variable {K : Type} [Field K] {N : ℕ}

def TriMod (R : Subring K) (h : K) (A : Matrix (Fin N) (Fin N) K) (d : Fin N → K) : Prop :=
  ∃ E ∈ R.matrix, (A - h • E).BlockTriangular id ∧ ∀ i, (A - h • E) i i = d i

def Small (R : Subring K) (h : K) : Prop := h ∈ R ∧ ∀ r ∈ R, ∃ s ∈ R, (1 + h * r) * s = 1

def Fr (R : Subring K) (M : Matrix (Fin N) (Fin N) K) : Prop := M.det ≠ 0 ∧ M ∈ R.matrix ∧ M⁻¹ ∈ R.matrix

def Lc (R : Subring K) {σ : Type} [Fintype σ] (f : σ → K) (a : K) : Prop :=
  ∃ α : σ → K, (∀ s, α s ∈ R) ∧ a = ∑ s, α s * f s

def Gen (R : Subring K) {σ : Type} [Fintype σ] (f : σ → K) (η : K) : Prop :=
  η ≠ 0 ∧ (∀ s, f s / η ∈ R) ∧ Lc R f η

def gens (γ : K) (y : Fin N → K) (i : Fin (N + 1)) : Option (Fin N) → K :=
  fun s => s.elim γ fun k => if (i : ℕ) ≤ k then y k else 0

def dg (j : Fin N) (γ : K) : Matrix (Fin N) (Fin N) K := Matrix.diagonal (Function.update 1 j γ)

def PInt (p : ℕ) (f : K) : Prop := ∃ r : ℕ, r.Coprime p ∧ IsIntegral ℤ ((r : K) * f)

theorem TriMod.of_mul {R : Subring K} {h b : K} {A : Matrix (Fin N) (Fin N) K} {d : Fin N → K} (H : TriMod R (h * b) A d)
    (hb : b ∈ R) : TriMod R h A d := by
  obtain ⟨E, hE, h₁, h₂⟩ := H
  refine ⟨b • E, fun i j => R.mul_mem hb (hE i j), ?_, ?_⟩ <;> rwa [smul_smul]

theorem Fr.mul {R : Subring K} {A B : Matrix (Fin N) (Fin N) K} (hA : Fr R A) (hB : Fr R B) : Fr R (A * B) :=
  ⟨by rw [Matrix.det_mul]; exact mul_ne_zero hA.1 hB.1, mul_mem hA.2.1 hB.2.1,
    by rw [Matrix.mul_inv_rev]; exact mul_mem hB.2.2 hA.2.2⟩

theorem Fr.inv {R : Subring K} {A : Matrix (Fin N) (Fin N) K} (hA : Fr R A) : Fr R A⁻¹ :=
  ⟨by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hA.1, hA.2.2,
    by rw [Matrix.nonsing_inv_nonsing_inv _ hA.1.isUnit]; exact hA.2.1⟩

variable {K' : Type} [Field K'] {R : Subring K} {R' : Subring K'} (φ : K →+* K') (hφ : ∀ f ∈ R, φ f ∈ R')
include hφ

theorem TriMod.map {h : K} {A : Matrix (Fin N) (Fin N) K} {d : Fin N → K} (H : TriMod R h A d) :
    TriMod R' (φ h) (A.map φ) fun i => φ (d i) := by
  obtain ⟨E, hE, h₁, h₂⟩ := H
  have e (i j) : (A.map φ - φ h • E.map φ) i j = φ ((A - h • E) i j) := by simp
  exact ⟨E.map φ, fun i j => hφ _ (hE i j), fun i j hij => by rw [e, h₁ hij, map_zero], fun i => by rw [e, h₂]⟩

theorem Fr.map {A : Matrix (Fin N) (Fin N) K} (H : Fr R A) : Fr R' (A.map φ) :=
  ⟨by rw [show (A.map φ).det = φ A.det from (RingHom.map_det φ A).symm]; exact (map_ne_zero φ).2 H.1,
    fun i j => hφ _ (H.2.1 i j), by rw [GlobalTheory.FrameGlue.Pull.matrix_map_inv]; exact fun i j => hφ _ (H.2.2 i j)⟩

end Alg

section Sch

variable {X : Scheme.{0}} [IsIntegral X] {N : ℕ}

def Ov (p : ℕ) {X : Scheme.{0}} (x : X) : Prop := ¬ IsUnit (p : X.presheaf.stalk x)

def loc (x : X) : Subring X.functionField := (algebraMap (X.presheaf.stalk x) X.functionField).range

theorem mem_loc {x : X} {f : X.functionField} : f ∈ loc x ↔ RegAt x f := Iff.rfl

theorem eventually_regAt {x : X} {f : X.functionField} (h : RegAt x f) : ∀ᶠ z in 𝓝 x, RegAt z f := by
  obtain ⟨U, hx, a, rfl⟩ := h.exists_fnOf
  exact Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun z hz => regAt_fnOf hz _ a

theorem eventually_unitAt {x : X} {f : X.functionField} (h : UnitAt x f) : ∀ᶠ z in 𝓝 x, UnitAt z f := by
  obtain ⟨U, hx, hU⟩ := h.exists_nhds
  exact Filter.eventually_of_mem (U.isOpen.mem_nhds hx) hU

theorem eventually_mem_matrix {x : X} {M : Matrix (Fin N) (Fin N) X.functionField} (h : M ∈ (loc x).matrix) :
    ∀ᶠ z in 𝓝 x, M ∈ (loc z).matrix := by
  have : ∀ᶠ z in 𝓝 x, ∀ i j, RegAt z (M i j) :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_regAt (h i j)
  exact this

theorem Fr.eventually {x : X} {M : Matrix (Fin N) (Fin N) X.functionField} (h : Fr (loc x) M) :
    ∀ᶠ z in 𝓝 x, Fr (loc z) M :=
  ((eventually_mem_matrix h.2.1).and (eventually_mem_matrix h.2.2)).mono fun _ hz => ⟨h.1, hz⟩

theorem small_pow {p : ℕ} {x : X} (hx : Ov p x) (k : ℕ) : Small (loc x) ((p : X.functionField) ^ (k + 1)) := by
  refine ⟨pow_mem (natCast_mem _ p) _, ?_⟩
  rintro _ ⟨r, rfl⟩
  have h : IsUnit (1 + (p : X.presheaf.stalk x) ^ (k + 1) * r) := by
    refine (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right fun h => hx ?_
    rw [sub_add_cancel_left, IsUnit.neg_iff, pow_succ', mul_assoc] at h
    exact isUnit_of_mul_isUnit_left h
  obtain ⟨s, hs⟩ := h.exists_right_inv
  refine ⟨_, ⟨s, rfl⟩, ?_⟩
  have := congrArg (algebraMap _ X.functionField) hs
  simpa using this

def Coh (p k : ℕ) (M : X → Matrix (Fin N) (Fin N) X.functionField) (c : X → Fin N → X.functionFieldˣ) : Prop :=
  ∀ x, Ov p x → Fr (loc x) (M x) ∧ ∀ᶠ z in 𝓝 x, Ov p z →
    TriMod (loc z) ((p : X.functionField) ^ k) ((M x)⁻¹ * M z) fun i => (c x i : X.functionField) / c z i

def Cross (p k : ℕ) (M M' : X → Matrix (Fin N) (Fin N) X.functionField) (c c' : X → Fin N → X.functionFieldˣ)
    (P : Matrix (Fin N) (Fin N) X.functionField) : Prop :=
  ∀ x, Ov p x → Fr (loc x) (M x) ∧ Fr (loc x) (M' x) ∧ ∀ᶠ z in 𝓝 x, Ov p z →
    TriMod (loc z) ((p : X.functionField) ^ k) ((M' x)⁻¹ * P * M z) (fun i => (c' x i : X.functionField) / c z i) ∧
    TriMod (loc z) ((p : X.functionField) ^ k) ((M' z)⁻¹ * P * M x) fun i => (c' z i : X.functionField) / c x i

def VEq (p : ℕ) (η : X → X.functionFieldˣ) : Prop :=
  ∀ x, Ov p x → RegAt x (η x : X.functionField) ∧ (∃ a : ℕ, RegAt x ((p : X.functionField) ^ a / η x)) ∧
    ∀ᶠ z in 𝓝 x, Ov p z → UnitAt z ((η x : X.functionField) / η z)

def TrivOn (p : ℕ) (e b : X → X.functionField) : Prop :=
  ∃ t : X → X.functionFieldˣ, ∀ x, Ov p x → (¬ UnitAt x (e x) → UnitAt x (t x * b x)) ∧
    ∀ᶠ z in 𝓝 x, Ov p z → ¬ UnitAt z (e z) → RegAt z (((t x : X.functionField) / t z - 1) / e z)

def Link (p : ℕ) (c c' : X → Fin N → X.functionFieldˣ) : Prop :=
  ∃ (η : X → Fin (N + 1) → X.functionFieldˣ) (γ : X.functionFieldˣ), (∀ j, VEq p fun x => η x j) ∧
    (∀ x, Ov p x → UnitAt x (η x 0 : X.functionField) ∧ UnitAt x ((η x (Fin.last N) : X.functionField) / γ) ∧
      ∀ i : Fin N, RegAt x ((η x i.succ : X.functionField) / η x i.castSucc) ∧
        UnitAt x ((c' x i : X.functionField) / c x i / ((η x i.succ : X.functionField) / η x i.castSucc))) ∧
    ∀ i : Fin N, TrivOn p (fun x => (η x i.succ : X.functionField) / η x i.castSucc)
      fun x => (c x i : X.functionField) / η x i.castSucc

theorem link_of_unitAt {p : ℕ} {c c' : X → Fin N → X.functionFieldˣ}
    (h : ∀ x, Ov p x → ∀ i, UnitAt x ((c' x i : X.functionField) / c x i)) : Link p c c' := by
  refine ⟨fun _ _ => 1, 1, fun j x _ => ⟨(unitAt_one x).regAt, ⟨0, by simpa using (unitAt_one x).regAt⟩,
    .of_forall fun z _ => by simpa using unitAt_one z⟩, fun x hx => ⟨unitAt_one x, by simpa using unitAt_one x,
      fun i => ⟨by simpa using (unitAt_one x).regAt, by simpa using h x hx i⟩⟩, fun i => ⟨fun _ => 1, fun x _ =>
        ⟨fun hn => absurd (by simpa using unitAt_one x) hn, .of_forall fun z _ hn => absurd (by simpa using unitAt_one z) hn⟩⟩⟩

variable {X' X'' : Scheme.{0}} [IsIntegral X'] [IsIntegral X'']

def pf (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) (c : X → Fin N → X.functionFieldˣ) :
    X' → Fin N → X'.functionFieldˣ := fun x i => Units.map (SmallSec.fnMap π hπ).toMonoidHom (c (π x) i)

def pm (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) (M : X → Matrix (Fin N) (Fin N) X.functionField) :
    X' → Matrix (Fin N) (Fin N) X'.functionField := fun x => (M (π x)).map (SmallSec.fnMap π hπ)

@[simp] theorem val_pf (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) (c : X → Fin N → X.functionFieldˣ) (x : X')
    (i : Fin N) : (pf π hπ c x i : X'.functionField) = SmallSec.fnMap π hπ (c (π x) i) := rfl

theorem pf_comp (a : X'' ⟶ X') (b : X' ⟶ X) (ha : a (genericPoint X'') ⤳ genericPoint X')
    (hb : b (genericPoint X') ⤳ genericPoint X) (hab : (a ≫ b) (genericPoint X'') ⤳ genericPoint X)
    (c : X → Fin N → X.functionFieldˣ) : pf (a ≫ b) hab c = pf a ha (pf b hb c) :=
  funext fun x => funext fun i => Units.ext (ProjSpace.fnMap_comp a b ha hb hab _)

theorem pm_comp (a : X'' ⟶ X') (b : X' ⟶ X) (ha : a (genericPoint X'') ⤳ genericPoint X')
    (hb : b (genericPoint X') ⤳ genericPoint X) (hab : (a ≫ b) (genericPoint X'') ⤳ genericPoint X)
    (M : X → Matrix (Fin N) (Fin N) X.functionField) : pm (a ≫ b) hab M = pm a ha (pm b hb M) :=
  funext fun x => Matrix.ext fun i j => ProjSpace.fnMap_comp a b ha hb hab _

section Pull

open GlobalTheory.FrameGlue.Pull

variable (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) {p : ℕ}

omit [IsIntegral X] [IsIntegral X'] in

theorem Ov.map {x : X'} (h : Ov p x) : Ov p (π x) := fun hu => h (by simpa using hu.map (π.stalkMap x).hom)

theorem map_mem_loc (x : X') : ∀ f ∈ loc (π x), SmallSec.fnMap π hπ f ∈ loc x := fun _ h => regAt_fnMap π hπ h

theorem Coh.pull {k : ℕ} {M : X → Matrix (Fin N) (Fin N) X.functionField} {c : X → Fin N → X.functionFieldˣ}
    (h : Coh p k M c) : Coh p k (pm π hπ M) (pf π hπ c) := fun x hx => by
  obtain ⟨h₁, h₂⟩ := h _ (hx.map π)
  refine ⟨h₁.map _ (map_mem_loc π hπ x), (π.continuous.tendsto x).eventually h₂ |>.mono fun z hz hz' => ?_⟩
  have := (hz (hz'.map π)).map _ (map_mem_loc π hπ z)
  rw [Matrix.map_mul, ← matrix_map_inv, map_pow, map_natCast] at this
  (have H := this; simp only [map_div₀] at H; exact H)

theorem VEq.pull {η : X → X.functionFieldˣ} (h : VEq p η) :
    VEq p fun x => Units.map (SmallSec.fnMap π hπ).toMonoidHom (η (π x)) := fun x hx => by
  obtain ⟨h₁, ⟨a, h₂⟩, h₃⟩ := h _ (hx.map π)
  refine ⟨regAt_fnMap π hπ h₁, ⟨a, ?_⟩, (π.continuous.tendsto x).eventually h₃ |>.mono fun z hz hz' => ?_⟩
  · (have H := regAt_fnMap π hπ h₂; simp only [map_div₀, map_pow, map_natCast] at H; exact H)
  · (have H := unitAt_fnMap π hπ (hz (hz'.map π)); simp only [map_div₀] at H; exact H)

theorem TrivOn.pull {e b : X → X.functionField} (h : TrivOn p e b) :
    TrivOn p (fun x => SmallSec.fnMap π hπ (e (π x))) fun x => SmallSec.fnMap π hπ (b (π x)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨fun x => Units.map (SmallSec.fnMap π hπ).toMonoidHom (t (π x)), fun x hx => ?_⟩
  obtain ⟨h₁, h₂⟩ := ht _ (hx.map π)
  refine ⟨fun hn => ?_, (π.continuous.tendsto x).eventually h₂ |>.mono fun z hz hz' hn => ?_⟩
  · (have H := unitAt_fnMap π hπ (h₁ fun hu => hn (unitAt_fnMap π hπ hu)); simp only [map_mul] at H; exact H)
  · (have H := regAt_fnMap π hπ (hz (hz'.map π) fun hu => hn (unitAt_fnMap π hπ hu)); simp only [map_div₀, map_sub, map_one] at H; exact H)

theorem Link.pull {c c' : X → Fin N → X.functionFieldˣ} (h : Link p c c') : Link p (pf π hπ c) (pf π hπ c') := by
  obtain ⟨η, γ, h₁, h₂, h₃⟩ := h
  refine ⟨pf π hπ η, Units.map (SmallSec.fnMap π hπ).toMonoidHom γ, fun j => (h₁ j).pull π hπ, fun x hx => ?_,
    fun i => by (have H := (h₃ i).pull π hπ; simp only [map_div₀] at H; exact H)⟩
  obtain ⟨a, b, d⟩ := h₂ _ (hx.map π)
  refine ⟨unitAt_fnMap π hπ a, by (have H := unitAt_fnMap π hπ b; simp only [map_div₀] at H; exact H), fun i => ⟨?_, ?_⟩⟩
  · (have H := regAt_fnMap π hπ (d i).1; simp only [map_div₀] at H; exact H)
  · (have H := unitAt_fnMap π hπ (d i).2; simp only [map_div₀] at H; exact H)

theorem eqvGen_pull {c c' : X → Fin N → X.functionFieldˣ} (h : Relation.EqvGen (Link p) c c') :
    Relation.EqvGen (Link p) (pf π hπ c) (pf π hπ c') := by
  induction h with
  | rel _ _ h => exact .rel _ _ (h.pull π hπ)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

end Pull

end Sch

section Num

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {N : ℕ}

def Can (M : HermLB q) (E : CartierDiv X) : Prop :=
  ∃ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), M.div hr = E ∧
    ∀ σ (y : CxPts q σ), y ∈ offSupp q σ E ∧ logNorm (M.φ σ) r y = 0

def Vert (p : ℕ) (E : CartierDiv X) : Prop := ∀ x, ¬ Ov p x → E.IsEqn x 1

def Rep (p : ℕ) (L : HermLB q) (b : X → X.functionFieldˣ) : Prop :=
  ∃ (ρ : L.B.ι → X.functionFieldˣ) (hρ : IsRatSec L.B ρ), ∀ x, Ov p x → (L.div hρ).IsEqn x (b x)

def bil {E : Type 1} [AddCommGroup E] [Module ℝ E] {n : ℕ} (num : Form E (n + 1)) (G : Fin n → E) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => num (Fin.cons a (Fin.cons b G))) (fun a a' b => num.cons_add _ a a')
    (fun t a b => num.cons_smul _ t a) (fun a b b' => (num.curryLeft a).cons_add G b b')
    fun t a b => (num.curryLeft a).cons_smul G t b

section Bil

variable {E : Type 1} [AddCommGroup E] [Module ℝ E] {n : ℕ} {num : Form E (n + 1)} (G : Fin n → E)

theorem bil_apply (a b : E) : bil num G a b = num (Fin.cons a (Fin.cons b G)) := rfl

theorem bil_rad_left {a : E} (ha : a ∈ rad num) (b : E) : bil num G a b = 0 := by
  have := ha (Fin.cons a (Fin.cons b G)) 0
  rwa [Fin.update_cons_zero] at this

theorem bil_symm (hs : IsSymm num) (a b : E) : bil num G a b = bil num G b a := by
  rw [bil_apply, bil_apply, ← hs _ (Equiv.swap 0 1)]
  congr 1
  funext j
  refine Fin.cases rfl (fun j => Fin.cases rfl (fun j => ?_) j) j
  rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
  rfl

theorem bil_rad_right (hs : IsSymm num) (a : E) {b : E} (hb : b ∈ rad num) : bil num G a b = 0 :=
  (bil_symm G hs a b).trans (bil_rad_left G hb a)

theorem bil_congr (hs : IsSymm num) {a a' b b' : E} (ha : a - a' ∈ rad num) (hb : b - b' ∈ rad num) :
    bil num G a b = bil num G a' b' := by
  have h₁ := bil_rad_left G ha b
  have h₂ := bil_rad_right G hs a' hb
  rw [map_sub, LinearMap.sub_apply] at h₁
  rw [map_sub] at h₂
  linarith

end Bil

def Moves {n : ℕ} (num : Form (Cl q) (n + 1)) (G : Fin n → HermLB q) (p m : ℕ) (c c' : X → Fin N → X.functionFieldˣ) : Prop :=
  ∃ (Δ : Fin N → HermLB q) (E : Fin N → CartierDiv X),
    (∀ i, Can (Δ i) (E i) ∧ Vert p (E i) ∧ ∀ x, Ov p x → (E i).IsEqn x ((c' x i / c x i) ^ m)) ∧
    ∀ L : Fin N → HermLB q, (∀ i, Rep p (L i) fun x => c x i ^ m) →
      ∑ i, bil num (fun j => cl (G j)) (cl (L i) + cl (Δ i)) (cl (L i) + cl (Δ i)) =
        ∑ i, bil num (fun j => cl (G j)) (cl (L i)) (cl (L i))

end Num

section Cov

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

abbrev jm (V : Cover Y) (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) : V.X.functionField →+* V.G.functionField :=
  SmallSec.fnMap V.j hη

def Reads {C : CxSt F} (V : Cover Y) (p : ℕ) (A : Adl C Y) (c : V.X → V.X.functionFieldˣ) : Prop :=
  ∃ (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) (W : Y.X.Opens) (U : V.X → V.X.Opens), genericPoint Y.X ∈ W ∧
    (∀ x, Ov p x → x ∈ U x) ∧
    (∀ x (z : V.G), V.j z ∈ U x → UnitAt z (V.φ (genAt A.D (V.π z)) * jm V hη (c x))) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ x, ⊤ ≤ yt ⁻¹ᵁ U x → A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) * jm V hη (c x))))

def NormsX (V : Cover Y) (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ)
    (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r) : Prop :=
  (∀ σ (y : CxPts V.p σ), y ∈ offSupp V.p σ (M.div hr) ∧ logNorm (M.φ σ) r y = 0) ∧
    (∀ i (z : V.G), V.j z ∈ M.B.U i → UnitAt (V.j z) (r i : V.X.functionField)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G)
      (yt : Sp e.O ⟶ V.X) (i : M.B.ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ M.B.U i →
      lg v e y = Real.log (e.w (valAt (z ≫ V.j) (r i : V.X.functionField)))

theorem lies_comp {V₁ V₂ V₃ : Cover Y} {a : V₁.X ⟶ V₂.X} {b : V₂.X ⟶ V₃.X} (ha : Lies V₁ V₂ a) (hb : Lies V₂ V₃ b) :
    Lies V₁ V₃ (a ≫ b) := by
  obtain ⟨e', he₁', he₂'⟩ := ha
  obtain ⟨e, he₁, he₂⟩ := hb
  exact ⟨e' ≫ e, by rw [Category.assoc, he₁, ← Category.assoc, he₁', Category.assoc], by rw [Category.assoc, he₂, he₂']⟩

end Cov

end GlobalTheory.LatChain

end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain.CanTens

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k}

theorem presents_dual {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) :
    Presents (-D) (CechPic.dual L) fun i => (r i)⁻¹ := by
  refine ⟨isLB_dual h.isLB, fun i j hij => ?_, fun i x hx => (h.isEqn i x hx).neg⟩
  change (((r i)⁻¹ : X.functionFieldˣ) : X.functionField) =
    fnOf (L.U i ⊓ L.U j) hij ((L.g i j)⁻¹ : Γ(X, L.U i ⊓ L.U j)ˣ) * ((r j)⁻¹ : X.functionFieldˣ)
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv, h.isRatSec i j hij, mul_inv]

theorem ratVal_inv {σ : k →+* ℂ} {y : CxPts q σ} {f : X.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have h1 : UnitAt (under y) (1 : X.functionField) := unitAt_one _
  have e1 : ratVal (1 : X.functionField) y = 1 := by
    have e := ratVal_mul h1.regAt h1.regAt
    rw [mul_one] at e
    exact (mul_eq_left₀ (ratVal_ne_zero h1)).1 e.symm
  have e := ratVal_mul hf.regAt hf.inv.regAt
  rw [mul_inv_cancel₀ hf.ne_zero, e1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem can_tens {M M' : HermLB q} {E E' : CartierDiv X} (h : Can M E) (h' : Can M' E') :
    Can (M.tens M') (E + E') := by
  obtain ⟨r, hr, rfl, H⟩ := h
  obtain ⟨r', hr', rfl, H'⟩ := h'
  have P := (presents_divOfRatSec M.isLB hr).tens (presents_divOfRatSec M'.isLB hr')
  refine ⟨fun c => r c.1 * r' c.2, P.isRatSec, (presents_divOfRatSec _ P.isRatSec).unique P, fun σ y => ?_⟩
  obtain ⟨a, b⟩ := H σ y
  obtain ⟨a', b'⟩ := H' σ y
  refine ⟨mem_offSupp.2 fun hy => ?_, ?_⟩
  · rcases CartierDiv.supp_add_le _ _ hy with hy | hy
    · exact mem_offSupp.1 a hy
    · exact mem_offSupp.1 a' hy
  · have hc := CxPts.mem_ptsIn_inf.1 (CxPts.mem_pick ((M.tens M').φ σ).isLB y)
    rw [logNorm_eq _ hr a hc.1] at b
    rw [logNorm_eq _ hr' a' hc.2] at b'
    have u := hr.unitAt M.isLB a hc.1
    have u' := hr'.unitAt M'.isLB a' hc.2
    have e := Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero u)) (norm_ne_zero_iff.2 (ratVal_ne_zero u'))
    rw [← norm_mul, ← ratVal_mul u.regAt u'.regAt] at e
    refine (congrArg₂ (· - ·) e (add_div _ _ _)).trans ?_
    linarith

theorem can_dual {M : HermLB q} {E : CartierDiv X} (h : Can M E) : Can M.dual (-E) := by
  obtain ⟨r, hr, rfl, H⟩ := h
  have P := presents_dual (presents_divOfRatSec M.isLB hr)
  refine ⟨fun i => (r i)⁻¹, P.isRatSec, (presents_divOfRatSec _ P.isRatSec).unique P, fun σ y => ?_⟩
  obtain ⟨a, b⟩ := H σ y
  refine ⟨mem_offSupp.2 fun hy => hy ?_, ?_⟩
  · have := CartierDiv.IsEqn.neg (not_not.1 (mem_offSupp.1 a))
    rwa [inv_one] at this
  · have hc := CxPts.mem_pick (M.dual.φ σ).isLB y
    rw [logNorm_eq _ hr a hc] at b
    have u := hr.unitAt M.isLB a hc
    have e := congrArg (fun z : ℂ => Real.log ‖z‖) (ratVal_inv u)
    simp only [norm_inv, Real.log_inv] at e
    rw [← Units.val_inv_eq_inv_val] at e
    refine (congrArg₂ (· - ·) e (neg_div _ _)).trans ?_
    linarith

theorem can_tens_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (M M' : HermLB q), (∀ E E' : CartierDiv X, Can M E → Can M' E' → Can (M.tens M') (E + E') ∧ Can M.dual (-E)) ∧ ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) (r' : M'.B.ι → X.functionFieldˣ) (hr' : IsRatSec M'.B r'), ∃ (s : (M.tens M').B.ι → X.functionFieldˣ) (hs : IsRatSec (M.tens M').B s), (M.tens M').div hs = M.div hr + M'.div hr' := by
  intro k _ X _ q M M'
  refine ⟨fun E E' h h' => ⟨can_tens h h', can_dual h⟩, fun r hr r' hr' => ?_⟩
  have P := (presents_divOfRatSec M.isLB hr).tens (presents_divOfRatSec M'.isLB hr')
  exact ⟨fun c => r c.1 * r' c.2, P.isRatSec, (presents_divOfRatSec _ P.isRatSec).unique P⟩

end GlobalTheory.LatChain.CanTens

end
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.CombW

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}

theorem firstChernFormOfWeight_eq_hessianForm_chart {L : LB X.X} (ψ : Weight X.str σ L) (hψ : ψ.IsCInf) (c : AlgChart X.str σ X.dim)
    {y : CxPts X.str σ} (hy : y ∈ c.e.source) :
    c1W ψ ⟨(c, y), hy⟩ = GlobalTheory.ChernTop.matForm X.dim (c.hess ψ (pick ψ.isLB y) y) := by
  have hd := hψ.contDiffAt c hy (mem_pick ψ.isLB y)
  change ofValues _ = kappa • ∑ a, GlobalTheory.ChernTop.rowForm a _
  simp only [ofValues, GlobalTheory.ChernTop.rowForm, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact congrArg (kappa * ·) (GlobalTheory.CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd) a b).symm

theorem firstChernFormOfWeight_tensor {A B : LB X.X} (ψ : Weight X.str σ A) (φ : Weight X.str σ B) (hψ : ψ.IsCInf) (hφ : φ.IsCInf) :
    c1W (ψ.tens φ) = c1W ψ + c1W φ := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have ha := mem_pick ψ.isLB y
  have hb := mem_pick φ.isLB y
  show c1W (ψ.tens φ) ⟨(c, y), hy⟩ = c1W ψ ⟨(c, y), hy⟩ + c1W φ ⟨(c, y), hy⟩
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ (hψ.tens hφ) c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hψ c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hφ c hy,
    c.hess_eq (hψ.tens hφ) hy (i := (pick ψ.isLB y, pick φ.isLB y)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y),
    GlobalTheory.FlatMass.hess_tens hψ hφ hy ha hb, map_add]

theorem firstChernFormOfWeight_dual {B : LB X.X} (φ : Weight X.str σ B) (hφ : φ.IsCInf) :
    c1W φ.dual = -c1W φ := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have hb := mem_pick φ.isLB y
  show c1W φ.dual ⟨(c, y), hy⟩ = -c1W φ ⟨(c, y), hy⟩
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ hφ.dual c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hφ c hy,
    c.hess_eq hφ.dual hy (i := (pick φ.isLB y : B.ι)) hb (mem_pick _ y),
    GlobalTheory.FlatMass.hess_dual hφ hy hb, map_neg]

theorem firstChernFormOfWeight_trivial_zero : c1W (Weight.ofFun (p := X.str) (σ := σ) fun _ => 0) = 0 := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have h0 : (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)).IsCInf := Weight.isCInf_ofFun (cInfAt_const 0)
  show c1W _ ⟨(c, y), hy⟩ = 0
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ h0 c hy]
  have e : c.hess (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)) (pick (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)).isLB y) y = 0 :=
    GlobalTheory.FlatMass.cHess_zero _
  rw [e, map_zero]

def combSub (X : Var F) (σ : F →+* ℂ) : AddSubgroup (X.Dv × ((atlas X σ).Pt → Ev X.dim)) where
  carrier := {x | ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'),
    Presents x.1 L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = x.2}
  zero_mem' := ⟨LB.triv X.X, fun _ => 1, Weight.ofFun fun _ => 0, presents_zero,
    Weight.isCInf_ofFun (cInfAt_const 0), firstChernFormOfWeight_trivial_zero⟩
  add_mem' := by
    rintro ⟨D, w⟩ ⟨E, u⟩ ⟨L, r, ψ, h1, h2, h3⟩ ⟨M, r', φ, h1', h2', h3'⟩
    exact ⟨_, _, ψ.tens φ, h1.tens h1', h2.tens h2', by rw [firstChernFormOfWeight_tensor _ _ h2 h2', h3, h3']; rfl⟩
  neg_mem' := by
    rintro ⟨D, w⟩ ⟨L, r, ψ, h1, h2, h3⟩
    exact ⟨_, _, ψ.dual, GlobalTheory.LatChain.CanTens.presents_dual h1, h2.dual, by rw [firstChernFormOfWeight_dual _ h2, h3]; rfl⟩

end GlobalTheory.ChernCalc.CombW

open GlobalTheory.ChernCalc.CombW in
theorem GlobalTheory.ChernCalc.exists_comb_smoothWeight : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ c : κ → ℤ, ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'), Presents (∑ a, c a • Δ a) L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = ∑ a, (c a : ℂ) • c1W (ψ a) := by
  intro F _ σ X κ _ Δ L r ψ h c
  have hm : (∑ a, c a • ((Δ a, c1W (ψ a)) : X.Dv × ((atlas X σ).Pt → Ev X.dim))) ∈ combSub X σ :=
    AddSubgroup.sum_mem _ fun a _ => AddSubgroup.zsmul_mem _ (show ((Δ a, c1W (ψ a)) : X.Dv × ((atlas X σ).Pt → Ev X.dim)) ∈ combSub X σ from ⟨L a, r a, ψ a, (h a).1, (h a).2, rfl⟩) _
  obtain ⟨L', r', ψ', h1, h2, h3⟩ := hm
  refine ⟨L', r', ψ', ?_, h2, ?_⟩
  · simpa [Prod.fst_sum] using h1
  · rw [h3, Prod.snd_sum]
    simp only [Prod.smul_snd]
    exact Finset.sum_congr rfl fun a _ => (Int.cast_smul_eq_zsmul ℂ (c a) _).symm
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothWeight_integral_combination : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ c : κ → ℤ, ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'), Presents (∑ a, c a • Δ a) L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = ∑ a, (c a : ℂ) • c1W (ψ a) := by
  atlas_forward_decl GlobalTheory.ChernCalc.exists_comb_smoothWeight
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc.FirstChernW

open GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.LineForm.FirstChern

theorem smoothOn_atlas {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {m : Type} {U : Set (CxPts X.str σ)}
    {G : CxPts X.str σ → Matrix m m ℂ} (H : ∀ y ∈ U, MInfAt G y) (i j : m) :
    (atlas X σ).SmoothOn U fun y => G y i j := fun c v hv => by
  have := (H _ hv.2 i j).contDiffAt_chart c (c.e.map_target hv.1)
  erw [c.e.right_inv hv.1] at this
  exact this.contDiffWithinAt

theorem c1W_isForm_and_dbar_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → (atlas X σ).IsForm (fld (atlas X σ) (c1W ψ)) ∧ (atlas X σ).dbar (fld (atlas X σ) (c1W ψ)) = 0 := by
  intro F _ σ X L ψ hψ
  have hφ : ∀ a (x : (atlas X σ).Pt), x.pt ∈ ptsIn X.str σ (L.U a) →
      ContDiffAt ℝ 2 (fun v => ψ.φ a (x.ch.symm v)) x.crd := by
    intro a x hx
    exact ((vInfAt_iff_cInfAt.2 (hψ a _ hx)).contDiffAt_chart x.1.1 x.2).of_le (by norm_cast)
  obtain ⟨hfr, hP⟩ := GlobalTheory.T.chernForms_frame_independent_closed (atlas X σ) (ι := Unit) (fun a => ptsIn X.str σ (L.U a)) (fun _ => isOpen_ptsIn _)
    (fun y => ⟨_, mem_pick ψ.isLB y⟩) (fun a b y => Matrix.of fun _ _ => gv X.str σ L a b y)
    (fun a b _ _ c => (AlgChart.holo c _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.1, hv.2.2⟩⟩)
    (fun a y => Matrix.of fun _ _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ))
    (fun a => smoothOn_atlas fun y hy _ _ => (vInfAt_iff_cInfAt.2 (hψ a y hy)).comp_contDiff
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)))
    (fun a y _ => by
      have : (Matrix.of fun _ _ : Unit => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ)) =
          Matrix.diagonal fun _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ) := by
        ext; simp
      rw [this, Matrix.posDef_diagonal_iff]
      exact fun _ => Complex.zero_lt_real.2 (Real.exp_pos _))
    (fun a b y hy => by
      ext
      have h0 : 0 < ‖gv X.str σ L a b y‖ ^ 2 := by have := gv_ne_zero hy.1 hy.2; positivity
      rw [ψ.trans a b y hy.1 hy.2, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log h0]
      simp only [chg, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        Fintype.sum_unique, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]
      ring) 1
  obtain ⟨h1, -, h3⟩ := hP (fld _ (c1W ψ)) fun a x hx => by
    rw [hfr a _ x hx (mem_pick ψ.isLB x.pt)]
    exact congrArg Subtype.val (chernAt_exp_neg (hφ _ x (mem_pick _ _))).symm
  exact ⟨h1, h3⟩

end GlobalTheory.ChernCalc.FirstChernW
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChernFormOfWeight_isForm_dbar_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L), ψ.IsCInf → (atlas X σ).IsForm (fld (atlas X σ) (c1W ψ)) ∧ (atlas X σ).dbar (fld (atlas X σ) (c1W ψ)) = 0 := by
  atlas_forward_decl GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.TopPow

open ReciprocityTheory.L2DbarEstimates (cHess)
open GlobalTheory.HermFrame (ddc kappa)
open GlobalTheory.GoodMetric (coordVec)

theorem ddc_coordVec (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) (a b : Fin n) :
    ddc u v (coordVec a) (coordVec b) = kappa * cHess n (fun w => (u w : ℂ)) v a b := by
  rw [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm, GlobalTheory.ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu)]
  congr 1
  have hg : (fun x => GlobalTheory.dbar (fun w => (u w : ℂ)) x (coordVec b)) =
      ReciprocityTheory.L2DbarEstimates.wdb n b (fun w => (u w : ℂ)) := by
    funext x
    simp only [GlobalTheory.dbar, GlobalTheory.antilinPart, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [hg]
  simp only [GlobalTheory.del, GlobalTheory.linPart, cHess, Matrix.of_apply, ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  ring

theorem dens_ofValues_ddc_pow (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) :
    (dens ((ofValues (ddc u v) ^ n : Ev n) : Alt n)).re =
      n.factorial / Real.pi ^ n * (cHess n (fun w => (u w : ℂ)) v).det.re := by
  have e : ofValues (ddc u v) = ∑ a, ∑ b, (kappa • cHess n (fun w => (u w : ℂ)) v) a b • sym (a, b) := by
    simp only [ofValues, ddc_coordVec n u v hu, Matrix.smul_apply, smul_eq_mul]
  rw [e, GlobalTheory.CxForm.DensPow.dens_pow, Matrix.det_smul, Fintype.card_fin]
  have hk : kappa = Complex.I / 2 * ((Real.pi : ℂ)⁻¹) := by
    rw [GlobalTheory.HermFrame.kappa]; field_simp
  have h2 : (Complex.I / 2) ^ n ≠ 0 := pow_ne_zero _ (by simp)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hk, show ∀ d : ℂ, (n.factorial : ℂ) * ((Complex.I / 2 * ((Real.pi : ℂ))⁻¹) ^ n * d) / (Complex.I / 2) ^ n =
      (((n.factorial / Real.pi ^ n : ℝ)) : ℂ) * d from fun d => by
    rw [mul_pow]; field_simp; push_cast; ring, Complex.re_ofReal_mul]

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {L : LB X.X}

theorem dens_loc_c1W_pow (ψ : Weight X.str σ L) (hψ : ψ.IsCInf) (c : AlgChart X.str σ X.dim)
    (y : CxPts X.str σ) (hy : y ∈ c.e.source) :
    (dens ((atlas X σ).loc (fld (atlas X σ) (c1W ψ ^ X.dim)) c (c.e y))).re = c.chernDens ψ y := by
  have e := (atlas X σ).loc_crd (fld (atlas X σ) (c1W ψ ^ X.dim)) (⟨(c, y), hy⟩ : (atlas X σ).Pt)
  erw [e]
  have hs := hψ.contDiffAt c hy (mem_pick ψ.isLB y)
  erw [fld, Pi.pow_apply, c1W, dens_ofValues_ddc_pow X.dim _ _ hs]
  rfl

theorem part_c1W_pow : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  intro F _ σ X L ψ hψ ε
  unfold HolAtlas.part Weight.chernPart ChartGlue.glueMeas
  refine iSup_congr fun c => ?_
  unfold ChartGlue.chartMeas
  congr 1
  refine withDensity_congr_ae (ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_)
  have hy := c.e.map_target hv
  simp only [Function.comp_apply]
  erw [dens_loc_c1W_pow ψ hψ c _ hy]

end GlobalTheory.ChernCalc.TopPow
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L), ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  atlas_forward_decl GlobalTheory.ChernCalc.TopPow.part_c1W_pow
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hCD F _ σ X κ _ Δ L r ψ hψ P hP
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hform : ∀ G : MvPolynomial κ ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (fun a => c1W (ψ a)) G) :=
    fun G => ((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.1 κ _ G
      (fun a => (GlobalTheory.T.firstChernFormOfWeight_isForm_dbar_eq_zero F σ X (L a) (ψ a) (hψ a).2).1)).1
  have Pw := GlobalTheory.LineForm.wInt_props (CxPts X.str σ) X.dim (atlas X σ)
  have hint : ∀ G : MvPolynomial κ ℝ, ∀ ε : ℤˣ,
      Integrable (fun _ => (1 : ℝ)) ((atlas X σ).part (evalF (atlas X σ) (fun a => c1W (ψ a)) G) ε) :=
    fun G ε => by
      haveI := Pw.1 _ (hform G) ε
      exact integrable_const _
  have hadd : ∀ G₁ G₂ : MvPolynomial κ ℝ,
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂)) =
        (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₁) +
          (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₂) := fun G₁ G₂ => by
    rw [← wInt_one, ← wInt_one, ← wInt_one, GlobalTheory.LineForm.GeoInt.evalF_add]
    exact (Pw.2.1 _ _ _ (hform G₁) (hform G₂) (hint G₁) (hint G₂)).2
  have hsmul : ∀ (t : ℝ) (G : MvPolynomial κ ℝ),
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G)) =
        t * (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G) := fun t G => by
    rw [← wInt_one, ← wInt_one, GlobalTheory.LineForm.GeoInt.evalF_smul]
    exact Pw.2.2.1 _ t _ (hform G)
  have hspan := GlobalTheory.LineForm.GeoInt.mem_span_pow_lin X.dim P hP
  clear hP
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨L', r', ψ', hpr, hci, hc1⟩ := GlobalTheory.T.exists_smoothWeight_integral_combination F σ X κ Δ L r ψ hψ n
    have e1 : evalF (atlas X σ) (fun a => c1W (ψ a)) (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) =
        fld (atlas X σ) (c1W ψ' ^ X.dim) := by
      funext x
      rw [hc1]
      simp only [evalF, fld, GlobalTheory.ArInt.lin, map_pow, map_sum, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.sum_apply, Pi.smul_apply, Pi.pow_apply]
      congr 2
    have e2 : X.interPoly Δ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = (X.inter fun _ => ∑ a, n a • Δ a : ℝ) := by
      have := Var.interPoly_prod_sum X Δ (fun _ a => n a)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this
    rw [e1, e2, HolAtlas.integral, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci,
      ← (hCD F X σ _ L' r' hpr ψ' hci).2]
    simp only [Weight.chernInt, Measure.restrict_univ, integral_const, smul_eq_mul, mul_one]
  | zero =>
    rw [map_zero]
    have := hsmul 0 0
    rw [zero_smul, zero_mul] at this
    exact this
  | add x y _ _ hx hy =>
    rw [map_add, hadd, hx, hy]
  | smul t x _ hx =>
    rw [map_smul, hsmul, hx, smul_eq_mul]

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chernForm_polynomial_eq_intersectionNumber : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  atlas_forward_decl GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
namespace GlobalTheory.ChernCalc

noncomputable def linPoly {n : ℕ} (α : V n → V n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ a, ∑ b, C (α (coordVec a) (coordVec b)) * X (a, b)

theorem linPoly_isHomogeneous {n : ℕ} (α : V n → V n → ℂ) : (linPoly α).IsHomogeneous 1 := by
  unfold linPoly
  refine IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_
  simpa using (isHomogeneous_C (Fin n × Fin n) (α (coordVec a) (coordVec b))).mul (isHomogeneous_X ℂ (a, b))

theorem aeval_sym_linPoly {n : ℕ} (α : V n → V n → ℂ) : aeval sym (linPoly α) = ofValues α := by
  simp [linPoly, ofValues, map_sum, Algebra.smul_def]

theorem degree_permMono {n : ℕ} (w : Equiv.Perm (Fin n)) :
    Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n := by
  rw [map_sum]; simp [Finsupp.degree_single]

theorem topCoeff_eq_zero_of_isHomogeneous {n d : ℕ} {Q : MvPolynomial (Fin n × Fin n) ℂ} (hQ : Q.IsHomogeneous d)
    (hd : d ≠ n) : topCoeff Q = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hQ.coeff_eq_zero (by rw [degree_permMono]; exact fun h => hd h.symm), mul_zero]

theorem dens_aeval_ofValues_offDeg : ∀ (n : ℕ) (κ : Type) (α : κ → V n → V n → ℂ) (d : ℕ) (P : MvPolynomial κ ℝ),
    P.IsHomogeneous d → d ≠ n →
      dens ((aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = 0 := by
  intro n κ α d P hP hd
  have h1 : (aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) =
      aeval sym (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))) := by
    rw [aeval_bind₁]; simp only [aeval_sym_linPoly]
  have hQ : (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))).IsHomogeneous d := by
    simpa using (hP.map (algebraMap ℝ ℂ)).aeval (fun i => linPoly (α i)) fun i => linPoly_isHomogeneous (α i)
  rw [h1, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_eq_zero_of_isHomogeneous hQ hd, zero_div]

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDensity_hermitianForms_eq_zero_offDegree : ∀ (n : ℕ) (κ : Type) (α : κ → V n → V n → ℂ) (d : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous d → d ≠ n → dens ((aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = 0 := by
  atlas_forward_decl GlobalTheory.ChernCalc.dens_aeval_ofValues_offDeg
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernLine

theorem eq_homogeneousComponent {κ R : Type} [AddCommGroup R] (f : MvPolynomial κ ℝ →+ R) (D : ℕ)
    (hf : ∀ d, d ≠ D → ∀ Q : MvPolynomial κ ℝ, Q.IsHomogeneous d → f Q = 0) (P : MvPolynomial κ ℝ) :
    f P = f (homogeneousComponent D P) := by
  conv_lhs => rw [← sum_homogeneousComponent P]
  rw [map_sum, Finset.sum_eq_single D]
  · intro b _ hb
    exact hf b hb _ (homogeneousComponent_isHomogeneous b P)
  · intro hD
    rw [Finset.mem_range, not_lt] at hD
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem interPoly_eq_zero {F : Type} [Field F] (Y : Var F) {κ : Type} (Δ : κ → Y.Dv) (d : ℕ) (hd : d ≠ Y.dim)
    (Q : MvPolynomial κ ℝ) (hQ : Q.IsHomogeneous d) : Y.interPoly Δ Q = 0 := by
  classical
  rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm' : m.degree = d := by
    have := hQ (mem_support_iff.mp hm)
    first
    | (rw [Finsupp.degree_eq_weight_one]; exact this)
    | exact this
  rw [show monomial m (coeff m Q) = coeff m Q • basisMonomials κ ℝ m by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, Var.interPoly, Module.Basis.constr_basis, dif_neg, smul_zero]
  rintro ⟨s, hs⟩
  apply hd
  rw [← hm', ← hs, map_sum]
  simp

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hC F _ σ X κ _ Δ L r ψ hψ P
  have hR : X.interPoly Δ P = X.interPoly Δ (homogeneousComponent X.dim P) :=
    eq_homogeneousComponent (X.interPoly Δ).toAddMonoidHom X.dim (fun d hd Q hQ => interPoly_eq_zero X Δ d hd Q hQ) P
  have hL : ∀ x, dens (evalF (atlas X σ) (fun a => c1W (ψ a)) P x) =
      dens (evalF (atlas X σ) (fun a => c1W (ψ a)) (homogeneousComponent X.dim P) x) := by
    intro x
    let f : MvPolynomial κ ℝ →+ ℂ :=
      { toFun := fun Q => dens (evalF (atlas X σ) (fun a => c1W (ψ a)) Q x)
        map_zero' := by simp [evalF, LineForm.fld, dens]
        map_add' := fun Q Q' => by
          simp only [evalF, LineForm.fld, map_add, Subalgebra.coe_add]
          exact LineForm.TopInt.dens_add _ _ }
    refine eq_homogeneousComponent f X.dim (fun d hd Q hQ => ?_) P
    exact GlobalTheory.T.topDensity_hermitianForms_eq_zero_offDegree X.dim κ _ d Q hQ hd
  rw [hR, ← GlobalTheory.T.integral_chernForm_polynomial_eq_intersectionNumber hC F σ X κ Δ L r ψ hψ _ (homogeneousComponent_isHomogeneous _ P)]
  simp only [HolAtlas.integral, LineForm.TopInt.part_congr _ hL]

end GlobalTheory.ChernLine
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chernFormPoly_eq_intersectionNumber : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  atlas_forward_decl GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly
end
