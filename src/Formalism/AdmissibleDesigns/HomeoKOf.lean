import Formalism.AdmissibleDesigns.CycMatchRec
import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Classical Topology

namespace Formalism.MainNotions.N.KBKa

open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf

section HK

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]


end HK

section Final

open NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]


end Final

end Formalism.MainNotions.N.KBKa
