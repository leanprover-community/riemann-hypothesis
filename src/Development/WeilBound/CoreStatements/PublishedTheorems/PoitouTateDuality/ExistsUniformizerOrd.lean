import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsUnif
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsKummer
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsChi
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsHasse

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2



theorem exists_kummer (F : Type) [Field F] [NumberField F] {l r : ℕ} [Fact l.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra F (AlgebraicClosure ℚ)]
    [IsAlgClosure F (AlgebraicClosure ℚ)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r)) (a : F) (ha : a ≠ 0)
    (y : AlgebraicClosure ℚ) (hy : y ^ (l ^ r) = algebraMap F (AlgebraicClosure ℚ) a) :
    ∃ κ : Dec (F := F) A → ZMod (l ^ r),
      (∀ g : Dec (F := F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y) ∧
      Continuous κ ∧
      ∀ g h : Dec (F := F) A, κ (g * h) =
        κ g + ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)) * κ h := by
  apply exists_kummer' <;> assumption

theorem exists_chi (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (v : HeightOneSpectrum (𝓞 Kf.1)) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v)
    (N : ℕ+)
    (ι : AlgebraicClosure ℚ →ₐ[Kf.1] AlgebraicClosure (v.adicCompletion Kf.1))
    (ev : (AlgebraicClosure (v.adicCompletion Kf.1) ≃ₐ[v.adicCompletion Kf.1]
        AlgebraicClosure (v.adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ι (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ι x)) :
    ∃ χ : Dec (F := Kf.1) A → ZMod (N : ℕ),
      (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) ∈ Ine (F := Kf.1) A → χ g = 0) ∧
      (∀ g : Dec (F := Kf.1) A, IsFrob (F := Kf.1) A (normV v) (g : G Kf.1 (AlgebraicClosure ℚ)) →
        χ g = 1) ∧
      Continuous χ ∧
      ∀ σ, χ (ev σ) = urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N σ := by
  apply exists_chi' <;> assumption

end PositivityTheory.Lit1.PTN
