import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrime

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAddChar_placeIdempotent_div_prime : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  first | exact @GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | exact GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | (intros; apply GlobalTheory.StdCharDegOne.stdChar_placeIdem_div <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.TypePrimes.psiG_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ ψ, Formalism.L2.Theta.IsStdChar (I.rec7 l Z) ψ (-1) → ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((I.rec7 l Z).host.g k : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (I.rec7 l Z).host.F), Formalism.L2.Theta.IsPlaceIdem (I.rec7 l Z) v ε → ∀ c y : 𝓞 (I.rec7 l Z).host.F, Valued.v (algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (c : (I.rec7 l Z).host.F) - G.phi k v h (inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (I.rec7 l Z).host.xi0)) < 1 → ∀ z : v.adicCompletionIntegers (I.rec7 l Z).host.F, (z : v.adicCompletion (I.rec7 l Z).host.F) = algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (y : (I.rec7 l Z).host.F) → G.psi0 k v h (IsLocalRing.residue _ z) = ψ (ε * algebraMap (I.rec7 l Z).host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (I.rec7 l Z).host.F) ((c : (I.rec7 l Z).host.F) * (y : (I.rec7 l Z).host.F) / ((I.rec7 l Z).host.g k : (I.rec7 l Z).host.F))) :=
  GlobalTheory.Mem.TypePrimes.Red.psiG_of_loc GlobalTheory.T.standardAddChar_placeIdempotent_div_prime
end
