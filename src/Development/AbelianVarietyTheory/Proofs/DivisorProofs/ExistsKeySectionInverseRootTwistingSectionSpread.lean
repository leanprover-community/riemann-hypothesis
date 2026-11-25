module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFour
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionNormComplexPointsEqTwoPiPow
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.KeyRootTw

namespace GlobalTheory.KeyRootSpread

theorem exists_twSec_keyRoot_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ Z : Comp Xo c, ∃ t : TwSec U x Z (wtOf Dw 0 1), IntOff (badPrimes H l) t.hi ∧ ∀ w, t.hi w - t.lo w ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U hU x hx hF hpq hg hun
  obtain ⟨hkey, hsecs⟩ := exists_twSec_keyRoot_bounds E H Dw l Xo c r U x hU hx hF hpq hg hun
  refine ⟨hkey, fun Z => ?_⟩
  obtain ⟨t, _, hhi, _, hspread⟩ := hsecs Z
  exact ⟨t, hhi, fun w => (hspread w).le⟩

end GlobalTheory.KeyRootSpread
