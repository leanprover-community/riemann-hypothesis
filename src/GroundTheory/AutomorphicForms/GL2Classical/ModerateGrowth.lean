import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.GrowthReduction

open NumberField IsDedekindDomain Matrix Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global ModularForm

set_option linter.unusedSectionVars false

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

variable {N : ℕ} [NeZero N] {k : ℤ}













end GL2Classical

end

end GroundTheory.Automorphic
