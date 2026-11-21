import Mathlib
import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.DataDIVDefs

noncomputable section

namespace GlobalTheory.Survey.IrrationalRotationBlocks

open Formalism.BasicNotions NumberField

def withBk (D : D7) (B : ∀ u, (D.div.Nu u).V →ₗ[D.what₂.LL] Module.Dual D.what₂.LL D.div.RR.V) : D7 :=
  { D with div := { D.div with Bk := B } }




def ValuesRational (D : D7) : Prop := ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V),
  D.what₂.Bu u (D.jN u φ) (D.jEE x) ∈ Set.range D.what₂.embLL


def rot (D : D7) (c : ℂ) : D.div.RR.V →ₛₗ[D.what₂.embLL] D.what₂.EE where
  toFun x := c • D.jEE x
  map_add' x y := by rw [map_add, smul_add]
  map_smul' a x := by rw [map_smulₛₗ, smul_comm]

def withRot (D : D7) (c : ℂ) (hc : ‖c‖ = 1) : D7 :=
  { D with
    jEE := rot D c
    jEE_basis := by
      have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      let e : D.what₂.EE ≃ₗ[ℂ] D.what₂.EE := LinearEquiv.smulOfNeZero ℂ D.what₂.EE c hc0
      have he : (fun i => rot D c (D.div.RR.b i)) = e ∘ (fun i => D.jEE (D.div.RR.b i)) := rfl
      refine ⟨?_, ?_⟩
      · rw [he]
        exact D.jEE_basis.1.map' e.toLinearMap e.ker
      · rw [he, Set.range_comp]
        have := Submodule.span_image e.toLinearMap (s := Set.range (fun i => D.jEE (D.div.RR.b i)))
        simp only [LinearEquiv.coe_coe] at this
        rw [this, D.jEE_basis.2, Submodule.map_top, LinearEquiv.range]
    jEE_norm := fun x => by
      rw [D.jEE_norm x]
      change _ = ‖c • D.jEE x‖
      rw [norm_smul, hc, one_mul] }

end GlobalTheory.Survey.IrrationalRotationBlocks
