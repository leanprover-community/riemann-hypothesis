module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.IsPrincipalCongruenceAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.B.fixOne :
    UpperTheory.One.M.B.FixOne := by
  intro L _ _ _ n a S hS s f hf hf0 hfix σ hσ
  obtain ⟨c, T, hc, hci, -⟩ := id hσ
  have hiso : f ∈ NG.isoTyp a.ρ S :=
    (le_sSup (s := {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'})
      ⟨hS, LinearEquiv.refl ℂ S, fun _ _ _ e => e⟩ : S ≤ NG.isoTyp a.ρ S) hf
  have hint : ∀ g ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n),
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun g hg => by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
    exact GlobalTheory.StepData.KOne_le_KO hg
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci
    (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1 hint
    (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    f hiso hf0 (fun κ hκ h => by
      rw [hfix κ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκ).1 (hint _ h)) hκ
        ((GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h)]
      simp)
  rw [Submodule.ne_bot_iff]
  refine ⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩
  have e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h := by
    ext i j
    simp
  have hg := GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)
  have h3 := hu _ hg
  rw [e] at h3
  simpa using h3
