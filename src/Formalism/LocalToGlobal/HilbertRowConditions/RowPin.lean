module

public import Formalism.LocalToGlobal.UnitaryNorms.CharGal
public import Formalism.LocalToGlobal.JointCharacters.SameChr
public import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingSpecSidedEmbeddingFixedField
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ValLeOneOfIsIntegral
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Choice
public import Formalism.LocalToGlobal.LocalInduction.BridgeInd
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
public import Formalism.SharpRestriction.PageFix
public import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
public import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalRingCardinality.DataBu
public import Formalism.LocalToGlobal.HermitianForms.TiedBr

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

def LowerMapTieS {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (Formalism.L2.Forms.bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u D.R.m)) (Formalism.L2.Forms.mZ u Tf.til.z0) P
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen D u P)

end Formalism.L2.Rows

end
