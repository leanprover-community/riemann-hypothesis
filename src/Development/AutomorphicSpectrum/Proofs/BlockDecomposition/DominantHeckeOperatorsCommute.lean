module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUniqueStatement
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.CassHecke

theorem isHeckeOpG_mul_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} {K : Subgroup G} {g c : G} (hc : c ∈ K)
    {T : Module.End ℂ (fixed π K)} (h : PositivityTheory.Lbc.IsHeckeOpG π K g T) :
    PositivityTheory.Lbc.IsHeckeOpG π K (g * c) T := by
  intro v f hf
  have hv : π c (v : V) = v := by simpa using v.2 ⟨c, hc⟩
  rw [map_mul, Module.End.mul_apply, hv]
  exact h v f hf

theorem heckeOp_commute : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), (∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J),
    PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' → U * U' = U' * U := by
  intro G _ _ _ D hcomm V _ _ π hπ t t' ht ht' U U' hU hU'
  have h1 := GlobalTheory.T.casselman_first_property G D V π hπ t t' ht ht' U U' hU hU'
  have h2 := GlobalTheory.T.casselman_first_property G D V π hπ t' t ht' ht U' U hU' hU
  have hc : (t' : G)⁻¹ * (t : G)⁻¹ * (t' : G) * (t : G) ∈ D.J := by
    have := hcomm (t' : G)⁻¹ (D.T.inv_mem t'.2) (t : G)⁻¹ (D.T.inv_mem t.2)
    simpa using this
  have h3 : PositivityTheory.Lbc.IsHeckeOpG π D.J ((t : G) * t') (U' * U) := by
    have := isHeckeOpG_mul_mem (D.J.inv_mem hc) h2
    have e : (t' : G) * (t : G) * ((t' : G)⁻¹ * (t : G)⁻¹ * (t' : G) * (t : G))⁻¹ = (t : G) * t' := by
      group
    rwa [e] at this
  exact (GlobalTheory.T.hecke_character_exists_unique G D.J D.isOpen_J D.isCompact_J V π hπ ((t : G) * t')).unique h1 h3

end GlobalTheory.CompanionTheory.CassHecke
