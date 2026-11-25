module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProof

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exactKeyFormula_proof : KeyFormula := by
  first | exact @GlobalTheory.KeyFam.keyFormula_holds
