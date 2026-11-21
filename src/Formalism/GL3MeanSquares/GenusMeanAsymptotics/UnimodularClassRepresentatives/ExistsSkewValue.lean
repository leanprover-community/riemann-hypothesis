import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open HermitianSublattices idealPowerSpanBounds

section Abstract

variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]


end Abstract

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

abbrev Hq (H : Matrix κ κ (𝓞 K)) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))

variable [Fact (IsFixF K F)]





end Formalism.HermitianLattices.Ext.L3.HU
