module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.Toroidal

namespace GlobalTheory.LocM

section Inv

structure InvFun (O : Type) [CommRing O] : Type where

  toFun : ∀ n : ℕ, ((Fin n → O) → (Fin n → O) → ℝ) → ℝ

  inv : ∀ (n m : ℕ) (r : (Fin n → O) →ₗ[O] (Fin m → O)), Function.Surjective r →
    ∀ B, toFun n (fun a b => B (r a) (r b)) = toFun m B

  zero : ∀ B, toFun 0 B = 0

namespace InvFun

variable {O : Type} [CommRing O] (φ : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

theorem toFun_pull_eq {n m : ℕ} {r : (Fin n → O) →ₗ[O] X} {s : (Fin m → O) →ₗ[O] X} (hr : Function.Surjective r)
    (hs : Function.Surjective s) (B : X → X → ℝ) :
    φ.toFun n (fun a b => B (r a) (r b)) = φ.toFun m (fun a b => B (s a) (s b)) := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property r s hr
  obtain ⟨k, hk⟩ := Module.projective_lifting_property s r hs
  let P : (Fin (n + m) → O) →ₗ[O] (Fin n → O) := LinearMap.funLeft O O (Fin.castAdd m)
  let Q : (Fin (n + m) → O) →ₗ[O] (Fin m → O) := LinearMap.funLeft O O (Fin.natAdd n)
  have h1 : Function.Surjective (P + h ∘ₗ Q) := fun a => ⟨Fin.append a 0, by
    have e : Q (Fin.append a 0) = 0 := by ext i; simp [Q]
    have e' : P (Fin.append a 0) = a := by ext i; simp [P]
    simp [e, e']⟩
  have h2 : Function.Surjective (k ∘ₗ P + Q) := fun a => ⟨Fin.append 0 a, by
    have e : Q (Fin.append 0 a) = a := by ext i; simp [Q]
    have e' : P (Fin.append 0 a) = 0 := by ext i; simp [P]
    simp [e, e']⟩
  rw [← φ.inv _ _ _ h1, ← φ.inv _ _ _ h2]
  have e : ∀ a, r ((P + h ∘ₗ Q) a) = s ((k ∘ₗ P + Q) a) := fun a => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add (f := _)]
    rw [← LinearMap.comp_apply r h, hh, ← LinearMap.comp_apply s k, hk]
  simp only [e]

variable (X) in
def eval [Module.Finite O X] (B : X → X → ℝ) : ℝ :=
  φ.toFun (Module.Finite.exists_fin' O X).choose fun a b =>
    B ((Module.Finite.exists_fin' O X).choose_spec.choose a) ((Module.Finite.exists_fin' O X).choose_spec.choose b)

theorem eval_eq [Module.Finite O X] {n : ℕ} {r : (Fin n → O) →ₗ[O] X} (hr : Function.Surjective r) (B : X → X → ℝ) :
    φ.eval X B = φ.toFun n fun a b => B (r a) (r b) :=
  φ.toFun_pull_eq (Module.Finite.exists_fin' O X).choose_spec.choose_spec hr B

theorem eval_pi (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : φ.eval (Fin n → O) B = φ.toFun n B :=
  φ.eval_eq (r := LinearMap.id) Function.surjective_id B

theorem eval_comp [Module.Finite O X] [Module.Finite O X₁] {r : X →ₗ[O] X₁} (hr : Function.Surjective r)
    (B : X₁ → X₁ → ℝ) : φ.eval X (fun a b => B (r a) (r b)) = φ.eval X₁ B := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O X
  rw [φ.eval_eq hs, φ.eval_eq (r := r ∘ₗ s) (hr.comp hs)]
  rfl

theorem eval_equiv [Module.Finite O X] [Module.Finite O X₁] (e : X ≃ₗ[O] X₁) (B : X₁ → X₁ → ℝ) :
    φ.eval X (fun a b => B (e a) (e b)) = φ.eval X₁ B := φ.eval_comp (r := e.toLinearMap) e.surjective B

theorem eval_of_subsingleton [Module.Finite O X] [Subsingleton X] (B : X → X → ℝ) : φ.eval X B = 0 := by
  rw [φ.eval_eq (n := 0) (r := 0) (fun x => ⟨0, Subsingleton.elim _ _⟩), φ.zero]

variable (O) in
def minVal : InvFun O where
  toFun _ B := sInf {x | (∃ y, B y y = x) ∧ x ≠ B 0 0}
  inv n m r hr B := by
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, map_zero]
    exact and_congr_left' ⟨fun ⟨y, h⟩ => ⟨r y, h⟩, fun ⟨y, h⟩ => (hr y).elim fun z e => ⟨z, e ▸ h⟩⟩
  zero B := by
    rw [← Real.sInf_empty]
    congr 1
    exact Set.eq_empty_of_forall_notMem fun x ⟨⟨y, h⟩, h'⟩ => h' (by rw [← h, Subsingleton.elim y 0])

def evalZ [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) : ℝ := φ.eval X fun a b => (β a b : ℝ)

def LinearOn [Module.Finite O X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → φ.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φ.evalZ (γ i)

variable {φ} in
theorem LinearOn.eval_eq_sum [Module.Finite O X] [Module.Finite O X₁] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h : φ.LinearOn γ) {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ → X₁ → ℝ} {c : Fin m → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hB : ∀ a b, B (r a) (r b) = ∑ i, c i * (γ i a b : ℝ)) :
    φ.eval X₁ B = ∑ i, c i * φ.evalZ (γ i) := by
  rw [← φ.eval_comp hr, ← h c hc]
  simp only [hB]

end InvFun

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E))
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {m : ℕ}

end Inv

section Ord

variable {R : Type} [CommRing R]

end Ord

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

instance finite_pelUnif {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) :
    Module.Finite (𝓞 E) P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _

def idlAlong {X : Scheme.{0}} (I : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) : Ideal R :=
  (FinalTheorems.stalkId I (ξ (closedPoint R))).map (Scheme.stalkClosedPointTo ξ).hom

namespace PolData

variable {i : Idx H p} (d : PolData Y i₀ i)

end PolData

instance Mdl.isProper_π (Z : Mdl Y i₀) : IsProper Z.π := by
  have := isProper_toroidalModel_structureMap (Y Z.i)
  have : IsProper (Z.π ≫ (Y Z.i).s) := by
    rw [Z.π_s, Pre.s]
    have := isProper_str (Z.i.c.V W) Z.n
    infer_instance
  exact IsProper.of_comp Z.π (Y Z.i).s

namespace PolData

variable {Z₀ : Mdl Y i₀} [IsIso Z₀.π] (d : PolData Y i₀ Z₀.i)

instance quasiCompact_ρ : QuasiCompact d.ρ := by
  have : IsAffineHom d.Z.genO.ι := by unfold Mdl.genO; infer_instance
  unfold ρ π
  infer_instance

end PolData

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

end GlobalTheory.LocM
