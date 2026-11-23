module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockConjugation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_common_eigenline :
    ∀ {H k : Type} [Group H] [TopologicalSpace H] [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : H →* GL (Fin (n + 1)) k) (κ : Fin (n + 1) → H →* kˣ) (v : Fin (n + 1) → k), Continuous r → v ≠ 0 → (∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ v = (κ 0 g : k) • v) → ∃ (p : GL (Fin (n + 1)) k) (r₁ : H →* GL (Fin (n + 1)) k) (r' : H →* GL (Fin n) k), (∀ g, r₁ g = p * r g * p⁻¹) ∧ Continuous r₁ ∧ Continuous r' ∧ (∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ 0 = 0) ∧ (∀ g, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 0 = (κ 0 g : k)) ∧ (∀ g (i j : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ j.succ = (r' g : Matrix (Fin n) (Fin n) k) i j) ∧ (HasFlag r' (fun i => κ i.succ) → HasFlag r κ) :=
  _root_.UpperTheory.Reformulated.B.BlockConjugation.exists_common_eigenline
