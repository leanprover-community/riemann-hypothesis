module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalPointsUnitaryGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSpecialUnitarySupportedAtPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncationSpecialUnitaryMemClosureStrongApproxStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.StrongApproxSUProof

theorem strongApproxSU : StrongApproxSU := by
  intro F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc g hg
  have h3 := GlobalTheory.T.truncation_specialUnitary_mem_closure_strongApprox GlobalTheory.T.specialUnitary_fixing_plane_complement_mem_closure GlobalTheory.T.exists_isotropic_places_alt F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  refine closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces F E σ hcm M J hJ g hg)
  rintro x ⟨T₁, T₂, η, hη, hx⟩
  refine closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_rational_points_unitary_group F E σ hcm M J hJ T₁ T₂ η hη x hx)
  rintro y ⟨γ, hγ, hy⟩
  exact h3 T₁ T₂ η hη γ hγ y hy

end GlobalTheory.StrongApproxSUProof
