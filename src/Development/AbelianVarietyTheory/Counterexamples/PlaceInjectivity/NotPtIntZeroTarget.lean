import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty

noncomputable section

namespace GlobalTheory.LvT.PtIntTest

open Formalism.BasicNotions Classical NumberField

variable {D : D7} {u : D.what₂.Word}


def zeroTarget (Tw : TwForms D) : TwForms D where
  A := Tw.A
  A_T := Tw.A_T
  fm u μ := { Tw.fm u μ with
    ptC := ⊥
    ipP := 0
    ptLat := Examples₂.fmZeroHLat D.what₂.LL
    ptLat_good := Examples₂.fmZeroHLat_good _
    ptEmb := 0
    ptEmb_basis := ⟨linearIndependent_empty_type, by rw [Set.range_eq_empty, Submodule.span_empty]⟩
    ptEmb_norm := fun x => by rw [Examples₂.fmZeroHLat_maj]; simp }
  e0 := Tw.e0
  twist_preserves_base_lattice := Tw.twist_preserves_base_lattice
  embed_mul_block_embedding := Tw.embed_mul_block_embedding
  eMu0 := Tw.eMu0
  eMu0_lat := Tw.eMu0_lat
  eMu0_emb := Tw.eMu0_emb

def scaleTarget (Tw : TwForms D) (c : D.what₂.LL) (hc : c ≠ 0) : TwForms D where
  A := Tw.A
  A_T := Tw.A_T
  fm u μ := { Tw.fm u μ with
    ptLat := { (Tw.fm u μ).ptLat with
      L := (Tw.fm u μ).ptLat.L.map ((c • LinearMap.id : _ →ₗ[D.what₂.LL] _).restrictScalars (𝓞 D.what₂.LL)) }
    ptLat_good := by
      obtain ⟨h1, h2, h3⟩ := (Tw.fm u μ).ptLat_good
      refine ⟨h1, h2.map _, ?_⟩
      rw [eq_top_iff, ← h3, Submodule.span_le]
      intro x hx
      have : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    ptEmb := (Tw.fm u μ).ptEmb
    ptEmb_basis := (Tw.fm u μ).ptEmb_basis
    ptEmb_norm := (Tw.fm u μ).ptEmb_norm }
  e0 := Tw.e0
  twist_preserves_base_lattice := Tw.twist_preserves_base_lattice
  embed_mul_block_embedding := Tw.embed_mul_block_embedding
  eMu0 := Tw.eMu0
  eMu0_lat := Tw.eMu0_lat
  eMu0_emb := Tw.eMu0_emb

end GlobalTheory.LvT.PtIntTest
