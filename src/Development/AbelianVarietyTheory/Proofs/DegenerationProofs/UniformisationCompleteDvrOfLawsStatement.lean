module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationCompleteDvrOfLaws

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.uniformisation_complete_dvr_of_laws : Laws → Laws2 → Laws3 → Laws4 → Laws5 → USt := by
  first | exact @GlobalTheory.LN.uniformisation_dvr
