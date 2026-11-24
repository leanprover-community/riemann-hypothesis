module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIntegralPreservesLocalisedLatticeImage
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

theorem _root_.GlobalTheory.T.centralIntegral_preserves_localisedLatticeImage : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), (∀ a : 𝓞 D.what₂.LL, D.nd.embK i (a : D.what₂.LL) ∈ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range) → (∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)), D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) → S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x))) → CenInt D → ∀ (c : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, c * a = a * c) → ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m') = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) c) (S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m)) := by
  first | exact @GlobalTheory.PendOf.CenLat.cenInt_lat | exact GlobalTheory.PendOf.CenLat.cenInt_lat | (intros; apply GlobalTheory.PendOf.CenLat.cenInt_lat <;> assumption)
