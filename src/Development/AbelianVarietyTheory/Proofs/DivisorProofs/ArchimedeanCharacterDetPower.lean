module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem mu_real_eq_prod_det : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) (e : D.what₂.Tau → ℤ), IsInfFam θ → MuVal V χ mu → (∀ ρ, HasInfExp D χ ρ (-(e ρ : ℚ))) → ∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ (-(e ρ)) := by
  intro D θ V χ mu e hθ hmu he u hu
  obtain ⟨x, hx, h⟩ := GlobalTheory.VacuumCharacter.exists_root hθ V
    (fun τ => (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ).ne_zero) u hu
  rw [hmu.2 u x hx, h χ (fun ρ => -(e ρ)) (fun ρ => by push_cast; exact he ρ)]
  rfl

end GlobalTheory.HolRead
