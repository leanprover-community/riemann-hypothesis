module

public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataNChoice

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Idx

open NumberField IsDedekindDomain Formalism.BasicNotions

variable (D : D7)

instance modO (μ : D.what₂.Tup) (j : ℕ) : Module (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  Module.compHom _ (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)

theorem smul_def (μ : D.what₂.Tup) (j : ℕ) (s : 𝓞 D.what₂.LL) (x : D.what₂.MtL μ j) :
    s • x = (s : D.what₂.LL) • x := rfl

instance towO (μ : D.what₂.Tup) (j : ℕ) : IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL (D.what₂.MtL μ j) :=
  ⟨fun a b x => by rw [smul_def, Algebra.smul_def, mul_smul]⟩

def TjL (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt μ j x ∈ D.what₂.TjSet μ j}

def TjV (μ : D.what₂.Tup) (j : ℕ) : Submodule D.what₂.LL (D.what₂.MtL μ j) :=
  Submodule.span D.what₂.LL (TjL D μ j : Set (D.what₂.MtL μ j))

def TjDual (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) where
  carrier := {x | x ∈ TjV D μ j ∧ ∀ a ∈ TjL D μ j, ∃ c : 𝓞 D.what₂.LL,
    inner ℂ (D.what₂.jMt μ j a) (D.what₂.jMt μ j x) = D.what₂.embLL (c : D.what₂.LL)}
  add_mem' := by
    rintro x y ⟨hx, h1⟩ ⟨hy, h2⟩
    refine ⟨(TjV D μ j).add_mem hx hy, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    obtain ⟨d, hd⟩ := h2 a ha
    exact ⟨c + d, by rw [map_add (f := _), inner_add_right, hc, hd]; simp⟩
  zero_mem' := ⟨(TjV D μ j).zero_mem, fun a _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro s x ⟨hx, h1⟩
    refine ⟨by rw [smul_def]; exact (TjV D μ j).smul_mem _ hx, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    exact ⟨s * c, by rw [smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hc]; simp⟩

variable {D} (X : DivX D)

def thImg (μ : D.what₂.Tup) (j : ℕ) (A : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j)) :
    Submodule (𝓞 D.what₂.LL) (X.MjH j).V where
  carrier := {y | ∃ x ∈ A, X.jM j y = D.what₂.thetaP μ j (D.what₂.jMt μ j x)}
  add_mem' := by
    rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
    exact ⟨x + y, A.add_mem hx hy, by rw [map_add (f := _), map_add (f := _), map_add (f := _), h1, h2]⟩
  zero_mem' := ⟨0, A.zero_mem, by simp⟩
  smul_mem' := by
    rintro s a ⟨x, hx, h1⟩
    refine ⟨s • x, A.smul_mem s hx, ?_⟩
    rw [smul_def, ← algebraMap_smul D.what₂.LL s a, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1,
      LinearMap.map_smul]

def thTj (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (X.MjH j).V := thImg X μ j (TjL D μ j)

def IjIdx (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl) : ℤ :=
  Formalism.HermitianLatticesTheory.lidx (D.plEq w).asIdeal (X.MjH j).L (thTj X μ j)

variable (D) in
def jwIdx (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl) : ℤ :=
  Formalism.HermitianLatticesTheory.lidx (D.plEq w).asIdeal (TjL D μ j) (TjDual D μ j)

end Formalism.BasicNotions.Idx

namespace Formalism.BasicNotions

structure IdxDefs (D : D7) (X : DivX D) : Prop where
  Ij_def : ∀ μ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.Ij μ j w = Idx.IjIdx X μ j w
  jw_def : ∀ μ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.jw μ j w = Idx.jwIdx D μ j w

end Formalism.BasicNotions

namespace Formalism.BasicNotions.Idx

open NumberField IsDedekindDomain Formalism.BasicNotions

variable (D : D7)

def Z0 (μ : D.what₂.Tup) (j : ℕ) : Submodule ℂ (D.what₂.Mt μ j) :=
  (LinearMap.ker (D.what₂.thetaP μ j))ᗮ ⊓ LinearMap.range (D.what₂.eMt μ j)

variable {D} (X : DivX D)

theorem jM_inj (j : ℕ) : Function.Injective (X.jM j) :=
  inj_of_li D.what₂.embLL (X.jM j) (X.MjH j).b (X.jM_basis j).1

end Formalism.BasicNotions.Idx

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain

end Formalism.BasicNotions

namespace Formalism.BasicNotions.Idx

open NumberField IsDedekindDomain Formalism.BasicNotions

end Formalism.BasicNotions.Idx

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

namespace NForms

variable (D : D7)

def eG (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) (D.nexp.eAlg i b)

def Fm0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  ⨅ u : D.nexp.U, LinearMap.ker ((D.nexp.actG i j b u).toLinearMap -
    ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • LinearMap.id)

def V0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  (Fm0 D i j b).map (eG D i j b)

def IsLatIn {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (M V : Submodule R W) : Prop :=
  M.FG ∧ M ≤ V ∧ ∀ x ∈ V, ∃ c : R, c ≠ 0 ∧ c • x ∈ M

end NForms

set_option synthInstance.maxHeartbeats 400000 in
def NChoice.thPe (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) :
    FractionRing (c.Oe w) ⊗[D.ntw.Ok (c.twI w) (c.k' w)]
        D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) →ₗ[FractionRing (c.Oe w)]
      FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
      (FractionRing (c.Oe w)) (FractionRing (c.Oe w)) (D.nexp.Fm (c.twI w) j (c.sd w))).toLinearMap ∘ₗ
    (D.nexp.thP (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))).baseChange
      (FractionRing (c.Oe w))

set_option synthInstance.maxHeartbeats 400000 in
theorem NChoice.thPe_one (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (m : D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))) :
    NChoice.thPe D c w j ((1 : FractionRing (c.Oe w)) ⊗ₜ m) =
      ((Algebra.linearMap (D.ntw.Ok (c.twI w) (c.k' w)) (FractionRing (c.Oe w))).restrictScalars (D.ntw.O (c.twI w))).rTensor
        (D.nexp.Fm (c.twI w) j (c.sd w))
        (D.nexp.thP (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) m) := by
  simp only [NChoice.thPe, LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe]
  induction (D.nexp.thP (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) m)
    using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul]
    simp [Algebra.smul_def]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add (f := _), hx, hy, map_add (f := _)]

namespace NMj

variable {D : D7} {X : DivX D} {c : NChoice D} (T : NMj D X c)

end NMj

end Formalism.BasicNotions

end
