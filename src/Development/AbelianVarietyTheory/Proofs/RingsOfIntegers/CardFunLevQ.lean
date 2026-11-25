module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open GlobalTheory.PlaceInt

theorem GlobalTheory.PlaceInt.card_fun_levQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (n : ℕ), Nat.card (Fin n → LevQ Dw l) = l.M ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q) * n) := by
  intro E _ _ _ H Dw l n
  rw [Nat.card_fun, (GlobalTheory.card_levQ E H Dw l).2, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]
  rfl
