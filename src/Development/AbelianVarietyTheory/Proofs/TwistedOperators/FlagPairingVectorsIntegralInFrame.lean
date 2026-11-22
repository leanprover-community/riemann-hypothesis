module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubOneIffEntries

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeConjRead
open Classical

theorem cast_fun_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) {m : ℕ} (f : Fin m → Formalism.L2.SG.HidaSetting.VA I)
    (hf : ∀ a, f a ∈ I.Lf) (a : Fin m) :
    (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin m → Formalism.L2.SG.HidaSetting.VA I) h) f) a ∈ J.Lf := by
  subst h
  exact hf a

theorem cast_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) (v : Formalism.L2.SG.HidaSetting.VA I) (hv : v ∈ I.Lf) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) v ∈ J.Lf := by
  subst h
  exact hv

theorem flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M)
    (z : M) (he : ∀ a, e a ∈ S) (hf : ∀ a, f a ∈ S) (hb : ∀ a, b a ∈ S) (hz : z ∈ S) (i : Fin n) :
    flagV ρ k n e f b z i ∈ S := by
  unfold flagV
  split_ifs
  exacts [he _, hb _, hz, hf _, h0]

theorem colMat_entry {D : D7} {n : ℕ} (M : Matrix (Fin n) (Fin n) (EAf D)) (w : Fin n → Fin n → EAf D) (i j : Fin n) :
    (M * colMat w) i j = Matrix.mulVec M (w j) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]

end GlobalTheory.SeeConjRead
