import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1

section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.W1
open scoped TensorProduct

namespace GlobalTheory.WH

variable (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → F) {κ : Type} [LinearOrder κ] (p1 p2 : κ → Fin (d + 1))

def bI (s : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ)) : Finset (Fin (d + 1)) := lft (lft s) ∪ (rgt s).image p1

def bJ (s : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ)) : Finset (Fin (d + 1)) := rgt (lft s) ∪ (rgt s).image p2

def TZ (a : ℕ) (q : ℤ) (s : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ)) : Submodule ℂ (Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :=
  if (lft (lft s)).Nonempty ∧ (rgt (lft s)).Nonempty ∧ 0 < q then
    ⨅ i ∈ bI p1 s, ⨅ j ∈ bJ p2 s, kFam (YZ F K x) (XZ F K x i) (XZ F K x i ^ 0 * YZ F K x j) (MZ F K x a (bI p1 s) (bJ p2 s)) q
  else ⊥

def wZ (z : κ → K ⊗[ℂ] K) : (Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ → Module.End ℂ (Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :=
  fun t => match ofLex t with
    | Sum.inl _ => 1
    | Sum.inr l => pw (actZ K (z l))

def YZi : Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  LinearMap.lTensor _ ((Algebra.lsmul ℂ ℂ (DR ℂ K)) (algebraMap F K (x 0)⁻¹))

def topZ (c : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :
    Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K :=
  fun b => YZi F K x (c (uni b ∅) {0})

def MZmix (a : ℕ) : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  mixF fun I J => MZ F K x a I J

section Y

variable {F K} {K' : Type} [Field K'] [Algebra ℂ K'] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K']
  [IsScalarTower F K K'] [IsScalarTower ℂ F K']

def XY (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K') := (Algebra.lsmul ℂ ℂ (DR ℂ K')) (algebraMap F K' (x l))

def YY (j2 : K →ₐ[ℂ] K') (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K') :=
  (Algebra.lsmul ℂ ℂ (DR ℂ K')) (j2 (algebraMap F K (x l)))

def MY (j2 : K →ₐ[ℂ] K') (I J : Finset (Fin (d + 1))) : Submodule ℂ (DR ℂ K') := omB ℂ K' (RY x j2 I J) d

def TY (j2 : K →ₐ[ℂ] K') (q : ℤ) (s : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ)) : Submodule ℂ (Finset (Fin (d + 1)) → DR ℂ K') :=
  if (lft (lft s)).Nonempty ∧ (rgt (lft s)).Nonempty ∧ 0 < q then
    ⨅ i ∈ bI p1 s, ⨅ j ∈ bJ p2 s, kFam (YY x j2) (XY x i) (XY x i ^ 0 * YY x j2 j) (MY x j2 (bI p1 s) (bJ p2 s)) q
  else ⊥

def gz (j2 : K →ₐ[ℂ] K') (z : K ⊗[ℂ] K) : K' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ K K') j2 z

def wY (j2 : K →ₐ[ℂ] K') (z : κ → K ⊗[ℂ] K) : (Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ → Module.End ℂ (Finset (Fin (d + 1)) → DR ℂ K') :=
  fun t => match ofLex t with
    | Sum.inl _ => 1
    | Sum.inr l => pw ((Algebra.lsmul ℂ ℂ (DR ℂ K')) (gz j2 (z l)))

def topY (j2 : K →ₐ[ℂ] K') (c : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K') :
    Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → DR ℂ K' :=
  fun b => (Algebra.lsmul ℂ ℂ (DR ℂ K')) (j2 (algebraMap F K (x 0)))⁻¹ (c (uni b ∅) {0})

def MYmix (j2 : K →ₐ[ℂ] K') : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → Submodule ℂ (DR ℂ K') :=
  mixF fun I J => MY x j2 I J

end Y

end GlobalTheory.WH
end
end

section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.W1
open scoped TensorProduct

namespace GlobalTheory.WH

section Z

variable (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → F)

def RZ (I J : Finset (Fin (d + 1))) : Subalgebra ℂ (K ⊗[ℂ] K) :=
  (Algebra.TensorProduct.map (rB ℂ K x I).val (rB ℂ K x J).val).range

def IsGen {κ : Type} [Fintype κ] (p1 p2 : κ → Fin (d + 1)) (z : κ → K ⊗[ℂ] K) : Prop :=
  (∀ l, z l ∈ RZ F K x {p1 l} {p2 l} ∧ Algebra.TensorProduct.lmul' ℂ (z l) = 0) ∧
    ∀ i j : Fin (d + 1), ∀ y ∈ RZ F K x {i} {j}, Algebra.TensorProduct.lmul' ℂ y = 0 →
      ∃ cf : κ → K ⊗[ℂ] K, (∀ l, cf l ∈ RZ F K x {i} {j}) ∧
        y = ∑ l ∈ Finset.univ.filter (fun l => p1 l = i ∧ p2 l = j), cf l * z l

def totZ {κ : Type} [LinearOrder κ] (p1 p2 : κ → Fin (d + 1)) (a : ℕ) (z : κ → K ⊗[ℂ] K) :
    GlobalTheory.PD.Cx ℂ (Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :=
  tcx (TZ F K x p1 p2 a) (wZ K z) (wd (XZ F K x))

def botZ {κ : Type} [LinearOrder κ] (m : Fin (d + 1) → Fin (d + 1) → DR ℂ K ⊗[ℂ] DR ℂ K) :
    Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K := fun s =>
  ∑ i, ∑ j, if s = uni (uni {i} {j}) ∅ then Pi.single Finset.univ ((XZ F K x i ^ d * YZ F K x j) (m i j)) else 0

def IsCanFam (τ : DR ℂ K →ₗ[K] K) (a : ℕ) (m : Fin (d + 1) → Fin (d + 1) → DR ℂ K ⊗[ℂ] DR ℂ K) : Prop :=
  ∀ i j, m i j ∈ MZ F K x a {i} {j} ∧
    ∀ w ∈ ⋀[K]^a Ω[K⁄ℂ], ctr F K τ w (m i j) = algebraMap F K ((∏ l, x l) / (x i ^ d * x j)) • w

end Z

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

def totY {κ : Type} [LinearOrder κ] (p1 p2 : κ → Fin (d + 1)) (j2 : K →ₐ[ℂ] K') (z : κ → K ⊗[ℂ] K) :
    GlobalTheory.PD.Cx ℂ (Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K') :=
  tcx (TY x p1 p2 j2) (wY j2 z) (wd (XY x))

def pullY {κ : Type} (j2 : K →ₐ[ℂ] K')
    (c : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :
    Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K' := fun s U => gY j2 (c s U)

def LefData (j2 : K →ₐ[ℂ] K') (Fx : Finset (fib ℂ K' x)) (A : fib ℂ K' x → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ (i : Fin (d + 1)) (e : rB ℂ K' x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j},
      ∃ (b : K') (hb : b ∈ rB ℂ K' x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ K' x {i}) ∧
  IsReduced ((rB ℂ K' x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K' x j⟩ : rB ℂ K' x {0})))) ∧
  (∀ (i : Fin (d + 1)), i ≠ 0 → ∀ e : rB ℂ K' x {i} →ₐ[ℂ] ℂ, ¬ IsFix (rB ℂ K' x {i}) e j2 (rB ℂ K x {i})) ∧
  (∀ e : rB ℂ K' x {0} →ₐ[ℂ] ℂ, IsFix (rB ℂ K' x {0}) e j2 (rB ℂ K x {0}) → ∀ j : Fin d, e ⟨_, tco_mem ℂ K' x j⟩ = 0) ∧
  (∀ e : fib ℂ K' x, e ∈ Fx ↔ IsFix (rB ℂ K' x {0}) e.1 j2 (rB ℂ K x {0})) ∧
  (∀ e ∈ Fx, ∀ (b : K) (hb1 : algebraMap K K' b ∈ rB ℂ K' x {0}), b ∈ rB ℂ K x {0} → e.1 ⟨_, hb1⟩ = 0 →
    ∃ (c : K) (hc1 : algebraMap K K' c ∈ rB ℂ K' x {0}), c ∈ rB ℂ K x {0} ∧ e.1 ⟨_, hc1⟩ ≠ 0 ∧
      ∃ g : Fin d → K, (∀ l, g l ∈ rB ℂ K x {0}) ∧ c * b = ∑ l, g l * algebraMap F K (x l.succ / x 0)) ∧
  (∀ e ∈ Fx, ∀ m : Fin d, ∃ (c : K') (hc : c ∈ rB ℂ K' x {0}) (g : Fin d → K') (hg : ∀ l, g l ∈ rB ℂ K' x {0}),
    e.1 ⟨c, hc⟩ ≠ 0 ∧ c * j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l * algebraMap F K' (x l.succ / x 0) ∧
      ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * A e m l) ∧
  (∀ e ∈ Fx, (1 - A e).det ≠ 0)

end Y

end GlobalTheory.WH
end
end
