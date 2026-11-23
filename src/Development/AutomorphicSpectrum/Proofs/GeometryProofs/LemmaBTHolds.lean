module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGenericStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHomStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtaleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherianStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentialsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbeddingStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLiftStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnitStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProperStatement
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

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem lemmaBT_holds : LemmaBT := by
  unfold GlobalTheory.CompanionTheory.Ar.BT.LemmaBT
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i hi hG
  refine ⟨GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ, ?_,
    fun hN => GlobalTheory.T.btOrder_eq_top_of_etale R T Γ
      (GlobalTheory.T.torsion_group_etale_of_unit R T Γ S G x N i hi hG hN), ?_, ?_,
    fun L _ _ M => GlobalTheory.T.exists_dual_to_invariant_differentials R T Γ S G x N i hi hG L M⟩
  · obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding R T Γ
    obtain ⟨hoi, htr⟩ := GlobalTheory.T.btOrder_embedding_open_immersion R T Γ j hj
    refine ⟨j, hj, hoi, htr, fun hP => ?_⟩
    exact GlobalTheory.T.btOrder_embedding_iso_finite R T Γ j hj
      (GlobalTheory.T.torsion_group_finite_of_proper R T Γ S G x N i hi hP)
  · intro a _ α hα f hf
    obtain ⟨a', _, ha'⟩ := GlobalTheory.T.torsion_group_endomorphism_lift R T Γ S G x N i hi a
    refine GlobalTheory.T.btOrder_comap_hom R T Γ T Γ a' α (fun t => ?_) f hf
    obtain ⟨_, _, hcancel, _⟩ := hi
    apply hcancel
    rw [Over.comp_left, Category.assoc, ha', hα t]
  · intro R' _ _ _ Γ' F hF
    obtain ⟨hd, hΓ'⟩ :=
      GlobalTheory.T.btOrder_base_change_generic R T Γ R' Γ' F hF
    obtain ⟨-, e, he⟩ := GlobalTheory.T.hopf_order_scalar_extension R T R' _
      (GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ) hd
    rw [hΓ']
    exact ⟨e, he⟩

end GlobalTheory.CompanionTheory.Ar.BT
