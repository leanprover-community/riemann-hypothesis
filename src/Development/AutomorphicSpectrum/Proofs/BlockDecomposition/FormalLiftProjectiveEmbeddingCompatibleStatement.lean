module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftProjectiveEmbeddingCompatible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem _root_.GlobalTheory.T.formal_lift_projective_embedding_compatible : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (t : ℤ) (e : ℕ), (∀ (c : ∀ i j : Fin (m + 1), Tm I Y N D (d : ℤ) (e + 1) t {i, j}), (∀ i j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i, j} (c i j) = 0) → (∀ i j k, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ij i j k) (c i j) + resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_jk i j k) (c j k) = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, Tm I Y N D (d : ℤ) (e + 1) t {i}, (∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} (b i) = 0) ∧ ∀ i j, c i j = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) - resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j)) → ∀ σ : LB.Sec (pw (N e) ((d : ℤ) * t)), ∃ σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)), SecMaps (pullPow (v e) ((d : ℤ) * t)) σ (secPull σ' (β e)) := by
  exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.lift_of_cech_pairs
