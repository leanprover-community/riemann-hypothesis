module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOfNormRepCountNeZero
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandG

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V]

variable {𝔭 : Ideal (𝓞 F)}

variable [FiniteDimensional K V]

end Formalism.HermitianLattices.Ext.L3.Cell
