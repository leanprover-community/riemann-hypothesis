module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryTorusUnipotentCosetTransportIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

theorem _root_.GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q q' n m : ℕ), IsUnramInv ϖ σ q → IsUnramInv ϖ' σ' q' → 2 * m ≤ n → ∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  first | exact @GlobalTheory.SatInd.cosetT_iff | exact GlobalTheory.SatInd.cosetT_iff | (intros; apply GlobalTheory.SatInd.cosetT_iff <;> assumption)
