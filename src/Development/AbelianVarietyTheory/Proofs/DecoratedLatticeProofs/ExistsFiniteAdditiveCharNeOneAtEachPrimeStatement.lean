module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime : ∀ (D : D7) (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ), (∀ x y, psiEf (x + y) = psiEf x * psiEf y) → (∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1) → (∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1) → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1 := by
  first | exact @GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one | exact GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one | (intros; apply GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one <;> assumption)
