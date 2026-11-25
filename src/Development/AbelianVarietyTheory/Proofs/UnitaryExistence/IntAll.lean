module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevel
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec

@[expose] public section

namespace GlobalTheory.IntegralFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem intAll : PartI → N1ab → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Formalism.L2.PjFree.IntAll Xo c := by
  intro hI hA hB hT E _ _ _ H Dw l Xo c hpq hg
  exact Formalism.L2.PjFree.intAll_of' (_root_.GlobalTheory.Exist.intFrExt_of_good hI hA hB hT E H Dw l Xo c hpq hg)
    (fun S S' _ _ _ _ φ y => _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S S' φ y)
    (fun S _ x _ v hv _ w A N w' hw hw' => GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv w A N w' hw hw')
    (_root_.GlobalTheory.IntRebase.intRebase hB E H Dw l Xo c)

end GlobalTheory.IntegralFrames
