import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree

noncomputable section

namespace GlobalTheory.TrivialValuationTest

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Ring

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

theorem vV_unit (u : Vˣ) : vV V (algebraMap V F (u : V)) = 0 := by
  have h : valV V (algebraMap V F (u : V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm u.isUnit
  simp [vV, h]

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}








def powerSeriesCDVR (K : Type) [Field K] [CharZero K] : CDVR where
  V := PowerSeries K
  cpl := by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  ch0 := algebraRat.charZero _



end GlobalTheory.TrivialValuationTest
