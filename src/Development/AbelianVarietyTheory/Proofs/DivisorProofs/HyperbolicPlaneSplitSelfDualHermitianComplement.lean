module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPartnerSplittingSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicHermitianSpaceOfNegativeIndexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrthogonalComplementHyperbolicPlanStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementNegativeIndexPredStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplement

theorem plane_split_complement : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (q : ℕ),
    IsSelfDualC S Λ → NegIdx S (q + 1) → q + 2 ≤ S.rank → 3 ≤ S.rank →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ S₁.SigOK ∧ IsSelfDualC S₁ Λ₁ ∧ NegIdx S₁ q := by
  intro D S Λ q hΛ hneg hq h3
  obtain ⟨x, hx0, hxx⟩ := GlobalTheory.T.exists_isotropic_hermitianSpace_of_negativeIndex D S (q + 1) hneg (by omega) (by omega) h3
  obtain ⟨y, hyy, hxy, hsp⟩ := GlobalTheory.T.exists_hyperbolicPartner_splitting_selfDualLattice D S Λ x hΛ hx0 hxx
  obtain ⟨S₁, Λ₁, ι, hPS, hSD, hs⟩ := GlobalTheory.T.exists_selfDual_orthogonalComplement_hyperbolicPlane D S Λ x y (fun _ => (S.rank - 2 - q, q)) hΛ hxx hyy hxy hsp
  have hrk : S.rank = S₁.rank + 2 := hPS.1
  have hsig := GlobalTheory.T.hyperbolicPlaneComplement_negativeIndex_pred D S S₁ ι x y q hrk hPS.2.1 hxx hyy hxy
    (fun u => ⟨(hPS.2.2.2.2.2.1 u).1, (hPS.2.2.2.2.2.1 u).2⟩) hneg
  have e : S.rank - 2 - q = S₁.rank - q := by omega
  refine ⟨S₁, Λ₁, ι, x, y, hPS, fun τ => ?_, hSD, fun τ => ?_⟩
  · rw [hs]; simp only [e]; exact hsig τ
  · exact hsig _

end GlobalTheory.PlaneComplement

end
