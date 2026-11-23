module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapSecEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHOmega :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_forms → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_sections → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega := by
  intro hE hF hS hA k k' _ _ _ J e X X' s s' g h a V hV
  letI := algΓ s
  letI := algΓ s'
  haveI : IsAffineHom g := hA k k' (algebraMap k k') X X' s s' g h
  have hV' : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  have hForms : IsBC e (formPullS h.w V a) :=
    hF k k' J e _ _ _ (semiHom_appSecS h.w V) (hS k k' J e X X' s s' g h V hV) a
  refine hE k k' J e _ _ _ _ (formPullS h.w V a) (omSecEquiv s a ⟨V, hV⟩).symm
    (omSecEquiv s' a ⟨g ⁻¹ᵁ V, hV'⟩) _ (fun x ↦ ?_) hForms
  obtain ⟨y, rfl⟩ := (omSecEquiv s a ⟨V, hV⟩).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact omegaPullS_toOmega h.w a V y
