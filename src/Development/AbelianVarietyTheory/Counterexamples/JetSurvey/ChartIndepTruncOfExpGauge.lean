import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffPolyAdd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAdd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsNabNotIsNablaPin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicFixedCard
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartIndepExpTest

open NumberField MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1


section Quad

variable {S : Type} [CommRing S] {d : ℕ}

abbrev sq2 (i j : Fin d) : Fin 1 × Fin d →₀ ℕ := Finsupp.single (0, i) 1 + Finsupp.single (0, j) 1



def quadMat (q : MvPowerSeries (Fin 1 × Fin d) S) : Matrix (Fin d) (Fin d) S :=
  fun i j => if i ≤ j then coeff (sq2 i j) q else 0


end Quad


theorem expUniqTan : ExpUniqTanSt := ExpUniqChart.expUniqTan




end GlobalTheory.ChartIndepExpTest
