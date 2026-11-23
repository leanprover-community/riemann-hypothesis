module

public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.BlowOpen

theorem exists_specializes_of_dense {X : Type} [TopologicalSpace X] [QuasiSober X] [NoetherianSpace X] (S : Set X)
    (hSo : IsOpen S) (hSd : Dense S) (x : X) : ∃ w ∈ S, w ⤳ x := by
  classical
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hCi : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent x) := isClosed_of_mem_irreducibleComponents _ hC
  have hη : IsGenericPoint hCi.genericPoint (irreducibleComponent x) := by
    simpa [hCc.closure_eq] using hCi.isGenericPoint_genericPoint_closure
  let F := ⋃ C' ∈ (irreducibleComponents X \ {irreducibleComponent x}), C'
  have hFc : IsClosed F := (NoetherianSpace.finite_irreducibleComponents.diff).isClosed_biUnion
    (fun C' h => isClosed_of_mem_irreducibleComponents C' h.1)
  have hηF : hCi.genericPoint ∉ F := by
    simp only [F, Set.mem_iUnion]
    rintro ⟨C', ⟨hC', hne⟩, hηC'⟩
    have hsub : irreducibleComponent x ⊆ C' := fun y hy =>
      (hη.specializes hy).mem_closed (isClosed_of_mem_irreducibleComponents C' hC') hηC'
    exact hne (Set.mem_singleton_iff.2 (hC.eq_of_le hC'.1 hsub).symm)
  obtain ⟨w, hwF, hwS⟩ := hSd.inter_open_nonempty Fᶜ hFc.isOpen_compl ⟨_, hηF⟩
  have hwC : w ∈ irreducibleComponent x := by
    by_contra h
    apply hwF
    simp only [F, Set.mem_iUnion]
    refine ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => h ?_⟩,
      mem_irreducibleComponent⟩
    rw [← Set.mem_singleton_iff.1 e]; exact mem_irreducibleComponent
  exact ⟨_, (hη.specializes hwC).mem_open hSo hwS, hη.specializes mem_irreducibleComponent⟩

theorem exists_specializes_of_dense_scheme (N : Scheme.{0}) [IsLocallyNoetherian N] (W : Set N) (hWo : IsOpen W)
    (hWd : Dense W) (n : N) : ∃ w ∈ W, w ⤳ n := by
  obtain ⟨_, ⟨O, hO, rfl⟩, hnO, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ n) isOpen_univ
  haveI : IsNoetherianRing Γ(N, O) := IsLocallyNoetherian.component_noetherian ⟨O, hO⟩
  obtain ⟨w, hw, hwn⟩ := @exists_specializes_of_dense (O : Set N) _ O.isOpen.isOpenEmbedding_subtypeVal.quasiSober
    (noetherianSpace_of_isAffineOpen O hO) (Subtype.val ⁻¹' W : Set (O : Set N)) (hWo.preimage continuous_subtype_val)
    (hWd.preimage O.isOpen.isOpenMap_subtype_val) ⟨n, hnO⟩
  exact ⟨w, hw, hwn.map continuous_subtype_val⟩

end GlobalTheory.BlowOpen
