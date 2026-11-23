module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneRanksFieldCharP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRigExtMapRelFrobLeRangeRigOfOmegaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRigOfOmegaLeRangeRigExtMapVerschiebungStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulIdStatement
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory

namespace PDivGroup

open PDiv

theorem ker_eq_range_of_range_eq_ker {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (_ : Module.Finite K V) (_ : Module.Finite K W) (f : V →ₗ[K] W)
    (g : W →ₗ[K] V) (hd : Module.finrank K V = Module.finrank K W) (h0 : g ∘ₗ f = 0)
    (h1 : LinearMap.range g = LinearMap.ker f) : LinearMap.ker g = LinearMap.range f := by
  have e1 := g.finrank_range_add_finrank_ker
  have e2 := f.finrank_range_add_finrank_ker
  rw [h1] at e1
  exact (Submodule.eq_of_le_of_finrank_eq (LinearMap.range_le_ker_iff.2 h0) (by omega)).symm

theorem rigExt_field_of_charP (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧
    Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height ∧
    LinearMap.range (rigExtMap (verschiebung h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (relFrob h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (verschiebung h G)) = LinearMap.range (rigExtMap (relFrob h G)) ∧
    LinearMap.range (rigExtMap (relFrob h G)) =
      Submodule.span K (Set.range fun x : G.RigExt => SemiHom.rig (absFrob h G) x) := by
  obtain ⟨-, f1, d1, d2⟩ := GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G
  obtain ⟨-, f2, d3, -⟩ := GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h (frobTwist h G)
  have h4 := le_antisymm (range_rigExtMap_verschiebung_le h G) (GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung' p K h G)
  have h5 := le_antisymm (GlobalTheory.T.ker_rigExtMap_relFrob_le_range_rigOfOmega' p K h G)
    (LinearMap.range_le_ker_iff.2 (rigExtMap_relFrob_comp_rigOfOmega h G))
  have h6 : rigExtMap (verschiebung h G) ∘ₗ rigExtMap (relFrob h G) = 0 := by
    rw [← rigExtMap_comp, verschiebung_comp_relFrob]
    exact (GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id p K h
      (frobTwist h G) (frobTwist h G)).2
  exact ⟨f1, d1, d2, h4, h5, ker_eq_range_of_range_eq_ker f2 f1 _ _
    (d3.trans ((frobTwist_height h G).trans d1.symm)) h6 (h4.trans h5.symm),
    range_rigExtMap_relFrob h G⟩

end PDivGroup

end GlobalTheory
