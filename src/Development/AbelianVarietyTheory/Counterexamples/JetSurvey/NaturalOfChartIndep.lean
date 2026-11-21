import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThExprBCPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrBCField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Semichar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigenLiftsOfDirectionsBiext
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqH
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeBeta

section
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
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpPiecesCheck




section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

end


end GlobalTheory.ExpPiecesCheck
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaExprBaseChangeTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
  Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

theorem frBCField : FrBCFieldSt Xo c := fun S _ _ y K _ _ ψ =>
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S K ψ y

end GlobalTheory.ThetaExprBaseChangeTest
end
end
