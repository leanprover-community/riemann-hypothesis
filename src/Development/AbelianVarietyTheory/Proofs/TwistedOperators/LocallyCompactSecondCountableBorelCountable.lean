module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteCountableGQ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.TwistAdelicTop

theorem locallyCompact_secondCountable_borel_countable :
    ∀ {D : D7} (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧
      BorelSpace (GA D V) ∧ Countable (GQ V) := by
  intro D V
  obtain ⟨hlc, hsc, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  exact ⟨hlc, hsc, ⟨rfl⟩, (GlobalTheory.RationalCountable.discrete_countable_GQ D V).2⟩

end GlobalTheory.TwistAdelicTop
