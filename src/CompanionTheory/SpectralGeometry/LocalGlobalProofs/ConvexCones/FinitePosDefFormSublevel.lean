module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.RatFormPosOfIntPos
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Pi.Interval
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Topology.Instances.Matrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan


open Matrix in

open Matrix in
theorem sublevel_finite : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ y z, β y z = β z y) → (∀ y, y ≠ 0 → 0 < β y y) →
    ∀ c : ℤ, {y : X | β y y ≤ c}.Finite := by
  intros
  apply GlobalTheory.ToricData.finite_form_le <;> assumption

end GlobalTheory.CompanionTheory.Ar.Fan
