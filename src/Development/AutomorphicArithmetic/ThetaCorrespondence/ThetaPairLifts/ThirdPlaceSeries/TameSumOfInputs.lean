module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameAnyAtPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameFixedAway
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameOfFrobeniusDense
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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



section
noncomputable section
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem tameSum_of_inputs_alt : ∀ D : D7, WildOne D →
    (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k →
      ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) →
    _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → PointPar D → _root_.GlobalTheory.TypeLeaf.TameSumAlt D := by
  intro D hW hχ hG hF hP i Sig hx hfull hc ρ hρ k hk
  obtain ⟨x, hx⟩ := hx
  obtain ⟨π, rfl⟩ := hc
  obtain ⟨h1, h2⟩ := hP i x π hx
  refine ⟨_root_.GlobalTheory.T.tame_fixed_of_l_ne_g D hW hG hF i π ρ h1 h2 hfull hρ k hk, fun w hw ht => ?_⟩
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · subst hv
    exact _root_.GlobalTheory.T.tame_any_at_pl_gw D hG hF i π ρ h1 h2 hfull hρ k hk v
  · exact _root_.GlobalTheory.T.tame_any_at_conj_of_frobenius_dense D hW hχ hG hF i π ρ h1 h2 hfull hρ k hk v w hv ht
end GlobalTheory.TypeLeaf
end
end
