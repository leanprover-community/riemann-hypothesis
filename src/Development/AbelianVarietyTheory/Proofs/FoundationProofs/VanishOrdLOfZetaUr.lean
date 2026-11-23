module

public import Development.AbelianVarietyTheory.Definitions.Foundations.VanishOrdL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrdinaryNormalFormUnramifiedSourceStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocPublishedOfLitCoh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem repIso_symm_srcL {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W W' : R2 Ω l}
    (h : RepIso W W') : RepIso W' W := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, fun s => ?_⟩
  rw [hg s]
  group

theorem vanishOrdL_of_zetaUr : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ZetaUr → VanishOrdL := by
  intro hC hZ l _ hl Ω _ _ _ ι e he W hW hS
  obtain ⟨S, A, W', g, hiso, hnf, hsrc⟩ := GlobalTheory.T.exists_ordinary_normal_form_unramified_source l Ω ι e W hl he hW hS
  have hes : ES W' A := hZ l Ω ι e S A W' g hnf hsrc
  have hv : BlochKatoSelmerVanishes l (Loc.colRep W') := GlobalTheory.Ord2.es_vanish hC l Ω e S A W' hnf hes
  exact UpperTheory.V.X.Kato.conj l ℚ Ω 2 W' W (repIso_symm_srcL hiso) hv

end GlobalTheory.Ord2
