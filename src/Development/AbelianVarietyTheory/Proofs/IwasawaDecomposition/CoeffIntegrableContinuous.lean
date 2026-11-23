module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.BesselDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffIntegrableContinuousOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.CoefInt

theorem coeff_integrable_continuous : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ F : GA D B → ℂ, Continuous F → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → (∀ g, IntegrableOn (fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))) 𝓝 ν) ∧ Continuous (d.coeff ψ ν 𝓝 F) ∧ ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M :=
  coeff_integrable_continuous_of fun D B ρ e he => (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1

end GlobalTheory.RootExch.CoefInt
