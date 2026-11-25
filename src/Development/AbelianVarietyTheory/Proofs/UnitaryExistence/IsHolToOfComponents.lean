module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolPullback

theorem isHolTo_of_components :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (Y Y' S S' : Scheme.{0}) (φ : Y' ⟶ Y) (p' : Y' ⟶ S') (p : Y ⟶ S) (f : S' ⟶ S) (a : V → (Sp ℂ ⟶ Y')), IsPullback φ p' p f → IsOpen B → IsHolTo B (fun b => a b ≫ φ) → IsHolTo B (fun b => a b ≫ p') → IsHolTo B a :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ H _ h₁ h₂ => GlobalTheory.HolFibre.isHolTo_of_isPullback H h₁ h₂

end GlobalTheory.HolPullback
