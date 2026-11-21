import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutRepDefiniteUnitarySpannedBySplitComponent
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInert
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ActsRhoFin

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TP

open scoped Classical

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}





end Gen


section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]





end CM

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ}
  {B : Base (maximalRealSubfield E) E} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
  {M : Model (cj E) X W} {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
  {e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J} {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}



end Main

section Split

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ}
  {B : Base (maximalRealSubfield E) E} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
  {M : Model (cj E) X W} {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
  {e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J} {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}


end Split

section Split2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ}
  {B : Base (maximalRealSubfield E) E} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
  {M : Model (cj E) X W} {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
  {e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J} {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}


end Split2


end UpperTheory.TP

end
