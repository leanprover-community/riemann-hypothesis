module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.ChiProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

@[expose] public section

noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

section Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ} (V : ConjugateFieldNorm.HSpace E r)

end Gen

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

instance totallyReal_host (D : D7) : IsTotallyReal D.host.F := D.sp.cm.totReal

variable {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r)

variable {V hr} {V' : ConjugateFieldNorm.HSpace D.host.E r} {ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V}

def RightInv (V : HSp D) (ν : Measure (Formalism.L2.Pj.AutQ V)) : Prop :=
  ∀ (h : GA D V) (ρ : Formalism.L2.Pj.AutQ V → Formalism.L2.Pj.AutQ V),
    (∀ g : GA D V, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s

end Rec

end GlobalTheory.CoreLawsCompare
