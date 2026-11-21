import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Af
section Rep
variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
end Rep
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {r r' : G F Ω →* GL (Fin n) (Qbar l)}
variable [IsAlgClosure F Ω]
abbrev _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty : Prop := ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (P : _root_.UpperTheory.V.Af.Hypotheses') {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w),
    ∃ rc : IrrGL (w.adicCompletion F) → WD h, _root_.UpperTheory.Zero.LLC.IsRecT h rc
end UpperTheory.V.Af
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
theorem exRec'_alt (_N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (h : IsPlaceOver A w) : ∃ rc, IsRecT h rc := recTExists E Ω A w h
theorem exists_rec_alt_alt_alt : _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty := by
  unfold _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty
  intros
  exact _root_.UpperTheory.V.Z.Win.exRec'_alt (by assumption : _root_.UpperTheory.V.Af.Hypotheses').litN _
end UpperTheory.V.Z.Win
end
end
end
