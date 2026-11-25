module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnReadingsNormalisedThetaPoints
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNormalisedFramedPointOnEachComponent
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyThetaDataFlagDomainModels
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSig
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRuleStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrame

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_framesOK : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∃ un, FramesOK e F M un := by
  intro hB hT E _ _ _ H Dw l Xo c σ g e F r M hσ hM hξ
  have T : ∀ k, ThetaData e F M k := fun k =>
    (_root_.GlobalTheory.FrameUnif.nonempty_thetaData E H Dw l Xo c σ g e F r M hσ hM hξ k).some
  choose un hun using fun k => _root_.GlobalTheory.FrameUnif.exists_isNormUn hT E H Dw l Xo c σ g e F r M k (T k)
  exact ⟨un,
    fun k => _root_.GlobalTheory.NormFrame.frameOK_of_isNormUn hT E H Dw l Xo c σ g e F r M k (T k) (un k) hσ hM hξ (hun k),
    fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
    fun k => _root_.GlobalTheory.FrameUnif.normUn_gamma hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
    fun a n han f hf k => _root_.GlobalTheory.FrameUnif.NormUnHol.differentiableOn_rdU hB hT E H Dw l Xo c σ g e F r M un k (T k) (hun k) a n han f hf⟩

end GlobalTheory.FrameUnif
