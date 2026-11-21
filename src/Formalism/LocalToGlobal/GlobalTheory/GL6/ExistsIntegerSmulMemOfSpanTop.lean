import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedRankEqFinrank
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedMaxSlopeLe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClearDenominatorsLattice

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions NumberField Matrix

theorem exists_integer_smul_mem_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • x ∈ L :=
  _root_.UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top L hL x

variable (D : D7) (u : D.what₂.Word)






end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
