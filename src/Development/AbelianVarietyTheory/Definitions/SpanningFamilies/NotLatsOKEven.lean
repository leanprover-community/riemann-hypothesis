import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.StandardLatticeGoodPlace
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.PowSqEqOneOfKilledBy

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsValTest

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}





def oneSim (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower n _ _ _ a := ⟨0, by simp⟩
  inv n _ := ⟨LinearMap.id, fun a => ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩⟩
  mult n _ a b := by simp







end

end GlobalTheory.ClsValTest
