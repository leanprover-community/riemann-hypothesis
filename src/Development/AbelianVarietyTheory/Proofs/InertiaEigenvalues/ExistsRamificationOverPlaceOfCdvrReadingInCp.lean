module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

noncomputable section

namespace GlobalTheory.ReadingOver

open GlobalTheory.GoodPts

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p])

variable (T : CDVR)

variable {T}

end GlobalTheory.ReadingOver

end
