module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2

@[expose] public section




section
namespace UpperTheory.V.Af
open UpperTheory.V.Published
structure Hypotheses' : Prop where
  litN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis
  cohC : ClozelCohC
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : _root_.UpperTheory.Gal.SV.GaloisRepExistsTotallyRealGL2
  smoR : StrongMultOneReal
  gkR : GelfandKazhdanReal
  admR : AdmissibleReal
  bc : Br.QuadBC0
  newform : NewformRep
end UpperTheory.V.Af
end
