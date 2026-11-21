import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNeAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLawsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameRamifiedTypeAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricBlockTypeVectorCuspidalSupportTameChara
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVector

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameParahoricRep_splits_as_product : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], TameSplit k := by
  first | exact @GlobalTheory.TameIwahori.tameSplit | exact GlobalTheory.TameIwahori.tameSplit | (intros; apply GlobalTheory.TameIwahori.tameSplit <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.BlockSplitProof

private theorem is_smooth_char_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : IsSmoothChar χ⁻¹ := by
  have hk : (χ⁻¹).ker = χ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  unfold IsSmoothChar
  rw [hk]
  exact h

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], BlockSplit k := by
  intro hBZ hGL hUP hDZ k _ _ _ _ r t χ π v hχ hT hv hvec

  obtain ⟨s, d, σ, hsupp, hle⟩ := GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters hBZ hGL hUP hDZ k r t χ π v hχ hT hv hvec
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inr ⟨s, d, σ, hsupp, hlt⟩
  ·
    obtain ⟨π₁, π₂, hE, hns⟩ := GlobalTheory.T.irreducible_split_exact_twistCount_product hBZ hGL hUP k r t χ π s d σ hχ hsupp heq.symm
    have hsph := GlobalTheory.T.spherical_twist_of_blockTypeVector hBZ hGL hDZ k r t χ π π₁ π₂ v hχ hT hns hE hv hvec
    have hχi : IsSmoothChar χ⁻¹ := is_smooth_char_inv hχ
    refine Or.inl ⟨π₁, GlobalTheory.SplitPairLift.twistIrr π₂ hχi, hsph, ?_⟩
    have h2 := GlobalTheory.SplitPairLift.twist_twist_inv π₂ χ⁻¹
    rw [inv_inv] at h2
    show Nonempty (π.π.Equiv (prod₂ π₁.π (twist (twist π₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
    rw [h2]
    exact hE

end GlobalTheory.BlockSplitProof
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockTypeVector_irreducible_splits_as_product : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], BlockSplit k := by
  atlas_forward_decl GlobalTheory.BlockSplitProof.main
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypesAtPin

theorem not_over_g_of_mem_Q (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ D.nd.Q i)
    (k : Fin 2) : w ∉ placesOver D.host.E (D.host.g k) := by
  intro hk
  have hS : w ∈ D.nd.S i := (D.nd.S_def i w).2 ⟨by
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk), D.nd.SQ_l i w (Or.inr hw)⟩
  exact Finset.disjoint_left.1 (D.nd.SQ_disj i) hS hw

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → GlobalTheory.NRows.RowsA D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro pr hL D P hrow rA
  obtain ⟨S, hTrue, hLaws, hSupp⟩ := GlobalTheory.T.exists_true_reading_with_laws pr.fin hL D P hrow
  have hTS : TameSplitAll D.host.E := fun w => GlobalTheory.T.tameParahoricRep_splits_as_product pr.bz pr.geo pr.unl pr.mp _
  have hBS : BlockSplitAll D.host.E := fun w => GlobalTheory.T.blockTypeVector_irreducible_splits_as_product pr.bz pr.geo pr.unl pr.mp _
  have hchi : ChiIne D.nd D.naut := GlobalTheory.SplitRead.chiIne_main D rA.tie0 rA.a2 rA.a5
    (GlobalTheory.MuIntegral.muInt_of_charTied D P.cf P.C P.tp P.chr)
  have hTT : ∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) →
      TypeTame S i w hw := by
    intro i w hw h
    have hng : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := by
      rcases h with hQ | ⟨-, hg⟩
      · exact not_over_g_of_mem_Q D i w hQ
      · exact hg
    have hSQ : w ∈ D.nd.S i ∨ w ∈ D.nd.Q i := by
      rcases h with hQ | ⟨hS, -⟩
      · exact Or.inr hQ
      · exact Or.inl hS
    have ht := GlobalTheory.MuTameQS.main hL D P S hTrue i w hw hSQ
    exact GlobalTheory.T.tame_ramified_type_at_place hL D P S hTrue i w hw hng ht.1 (ht.2 hng)
  have hTB : ∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw := by
    intro i w hw hSQ
    have ht := GlobalTheory.MuTameQS.main hL D P S hTrue i w hw hSQ
    by_cases hg : ∃ k, w ∈ placesOver D.host.E (D.host.g k)
    · exact GlobalTheory.T.tame_block_type_at_split_place hL D P S hTrue i w hw hg ht.1
    · have hng : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := fun k hk => hg ⟨k, hk⟩
      have hT : TypeTame S i w hw := hTT i w hw (by
        rcases hSQ with hS | hQ
        · exact Or.inr ⟨hS, hng⟩
        · exact Or.inl hQ)
      refine ⟨hT.1, fun Q => ?_⟩
      obtain ⟨v, hv0, hv⟩ := hT.2.2 Q
      exact ⟨v, hv0, fun h hK h1 _ u hu => hv h hK h1 u hu⟩
  exact GlobalTheory.InertialTypes.main D P.T S hTS hBS hLaws hSupp hchi hTT hTB

end GlobalTheory.TypesAtPin
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm4_of_rows_a : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → GlobalTheory.NRows.RowsA D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  atlas_forward_decl GlobalTheory.TypesAtPin.main
end
