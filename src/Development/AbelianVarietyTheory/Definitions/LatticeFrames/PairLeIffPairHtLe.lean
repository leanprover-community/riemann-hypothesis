module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Formalism.LocalToGlobal.Columns.ToHLat
public import Formalism.HarderNarasimhan.QuotRealize
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Formalism.LocalRingCardinality.DataArith

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Ht2

open NumberField Formalism.BasicNotions

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev nrm (A : HLat K) (v : InfinitePlace K) (x : A.V) : ℝ := Formalism.HermitianLatticesTheory.normAt A.b A.X v x

end Generic

namespace Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

variable {K n}

end Std

end GlobalTheory.Core.Ht2

end
