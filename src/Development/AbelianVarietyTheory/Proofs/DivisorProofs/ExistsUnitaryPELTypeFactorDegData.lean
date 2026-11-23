module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicFactorOfUnimodularTensorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataAStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorDegenerationDataOfUnimodularPosDefStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataUnitaryTypeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodLatticeBarBar
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_pelOK_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ D : DegData R (maximalIdeal R), Nontrivial D.toPre.X → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dm : Datum H) (D' : DegData R (maximalIdeal R)) (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), PelOK Dm D'.toPre o ∧ (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  intro R _ _ _ hR D hX
  obtain ⟨E, _, _, _, ⟨H⟩⟩ := GlobalTheory.Mum.exists_host
  obtain ⟨r, W, ρ, hr, hpos, hdet, hadj, hW⟩ := GlobalTheory.Mum.unimodLattice E H
  obtain ⟨D', ⟨T⟩⟩ := GlobalTheory.T.exists_tensorDegenerationData_of_unimodular_posDef R hR.1 D W hpos hdet
  obtain ⟨_, o, hact, hψ⟩ := GlobalTheory.T.exists_ringOfIntegers_module_on_tensor_data R hR.1 E H D D' W hpos hdet T ρ hadj hW
  obtain ⟨Dm, hDm⟩ := GlobalTheory.T.tensorDegData_unitary_type R hR E H D D' W hpos hdet T ρ hadj hW hX hr o hact hψ
  exact ⟨E, _, _, _, H, Dm, D', _, o, hDm, GlobalTheory.T.exists_algebraic_factor_of_unimodular_tensor R hR.1 D D' W hpos hdet T hr⟩

end GlobalTheory.Mum
