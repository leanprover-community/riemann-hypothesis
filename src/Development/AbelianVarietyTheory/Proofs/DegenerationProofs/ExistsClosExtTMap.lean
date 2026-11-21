import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTuple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseFactsOfIsEE
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemGenusOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAbelianSchemeProjectiveClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPoint

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_system_genus_one : Laws → Laws2 → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω), S.g = 1 ∧ S.Big ∧ Nonempty S.Real := by
  first | exact @GlobalTheory.ZH.RealDimOne.exists_real_dim_one | exact GlobalTheory.ZH.RealDimOne.exists_real_dim_one | (intros; apply GlobalTheory.ZH.RealDimOne.exists_real_dim_one <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.ClosureExample

theorem exists_adm (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) :
    ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ := by
  obtain ⟨s, hs⟩ := S.fg
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  let t₀ : Option s → Ω := fun j => j.elim 1 Subtype.val
  have htop : Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) = ⊤ := by
    set F := Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) with hF
    have hR : ∀ a ∈ S.R, a ∈ F := by
      intro a ha
      rw [← hs] at ha
      induction ha using Algebra.adjoin_induction with
      | mem x hx =>
        refine Subfield.subset_closure (Or.inr ⟨(x₀, none), (x₀, some ⟨x, hx⟩), ?_⟩)
        simp only [t₀, Option.elim]
        field_simp
      | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
    refine top_unique fun x _ => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := S.frac x
    exact div_mem (hR a ha) (hR b hb)
  obtain ⟨M, U₀, h, -⟩ := GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω S (Option s) t₀ ⟨none, one_ne_zero⟩ (by
    rw [htop]
    exact Module.Finite.of_surjective (Algebra.linearMap (⊤ : Subfield Ω) Ω) fun x => ⟨⟨x, trivial⟩, rfl⟩)
  exact ⟨M, U₀, h⟩


end GlobalTheory.ZH.ClosureExample
end
