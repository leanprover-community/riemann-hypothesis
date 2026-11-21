import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LeviDeterminants.ActsEx
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SingleLocalAdele
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationPackage

noncomputable section

namespace UpperTheory.TP

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def mulH {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n d : ℕ}
    (a : GL (Fin n) K) (c : GL (Fin d) K) : Matrix (Fin n) (Fin d) K ≃ₜ Matrix (Fin n) (Fin d) K :=
  _root_.UpperTheory.Reformulated.B.MatrixHomeomorphOfGeneralLinearPair.mulH_pk a c

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}





end UpperTheory.TP

end

