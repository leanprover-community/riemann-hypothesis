import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRPres
import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRWeyl
import Formalism.FormalDegreeBessel.FormalDegreeRatio.AdjointFunctionalHolds
import Formalism.YangianSpanCharacter.StatementT

noncomputable section

namespace Formalism.QuantumDeterminants

theorem presOps : PresOps := preserved_operators_holds
theorem linOps : LinOps := linear_operators_holds
theorem weylFun : WeylFun := weyl_functional_holds
theorem commFun : CommFun := commuting_functional_holds

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def opEnd (l : Fin m) (i : Fin 6) : Module.End ℂ (WSm m E) where
  toFun f := ⟨opL l i f, preserved_operators_holds m E l i f f.2⟩
  map_add' f g := Subtype.ext (linear_operators_holds m E l i f g 1 f.2 g.2).1
  map_smul' a f := Subtype.ext (linear_operators_holds m E l i f f a f.2 f.2).2

abbrev pEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 0

abbrev cEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 1

abbrev ciEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 2

abbrev pbEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 3

abbrev cbEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 4

abbrev cbiEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 5



end Formalism.QuantumDeterminants
