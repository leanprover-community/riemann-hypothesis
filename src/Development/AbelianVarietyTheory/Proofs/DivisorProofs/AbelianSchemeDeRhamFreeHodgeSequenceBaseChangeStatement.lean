module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

theorem _root_.GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.Hodge ∧ GlobalTheory.Published.AbelianDeRham.BaseChange := by
  first | exact @GlobalTheory.abelianDeRham_free_hodge_baseChange
