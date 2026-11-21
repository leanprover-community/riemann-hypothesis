import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEmbeddingCongrIntegralCharacter

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_frobenius_pow_of_ringHoms : ∀ {l : ℕ} [Fact l.Prime] {k D : Type} [Field k] [Finite k] [CommRing D] [IsDomain D] [CharP D l]
    (α β : k →+* D), ∃ i : ℕ, ∀ x, β x = α x ^ l ^ i := by
  intro l _ k D _ _ _ _ _ α β
  haveI : CharP k l := α.charP α.injective l
  exact GlobalTheory.ResidueChar.exists_pow_of_finite_field l α β

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_field_embeddings_differ_frobenius : ∀ {l : ℕ} [Fact l.Prime] {k D : Type} [Field k] [Finite k] [CommRing D] [IsDomain D] [CharP D l]
    (α β : k →+* D), ∃ i : ℕ, ∀ x, β x = α x ^ l ^ i := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms
