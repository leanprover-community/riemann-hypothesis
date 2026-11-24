module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

def CutRec (D : D7) : Prop :=
  ∀ i : D.nd.Loc, ∀ P : D.naut.AV i, D.naut.ptV i P ≠ none →
    ∀ (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), UpperTheory.GalS.Nc D.nd D.naut (D.naut.locV i P w)

def Tie4 (D : D7) : Prop :=
  PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly D ∧ GlobalTheory.TypeLeaf.SerLoc D

structure CutD (D : D7) where
  keep : D.nd.Loc → Prop
  Xs : ∀ i, Set (D.nd.X i)
  ne : ∀ i, keep i → (Xs i).Nonempty

def CutD.all (D : D7) : CutD D := ⟨fun _ => True, fun _ => Set.univ, fun _ _ => Set.univ_nonempty⟩

structure CutD.Good {D : D7} (c : CutD D) : Prop where
  keep : ∀ i, c.keep i ↔ (D.nd.Zgood i).Nonempty
  good : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ c.Xs i
  theta : ∀ i, ∀ x ∈ D.nd.Z i, x ∈ c.Xs i → x ∈ D.nd.Zgood i
  op : ∀ i, c.keep i → ∃ α : Module.End (D.nd.O i) (D.nd.Mt i),
    (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
    (∀ x ∈ D.nd.Zgood i, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      α.baseChange (FractionRing (D.nd.O i)) u = ((D.what₂.restRowsFiniteGroupCard : ℤ) : FractionRing (D.nd.O i)) • u) ∧
    ∀ x, x ∉ c.Xs i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, α.baseChange (FractionRing (D.nd.O i)) u = 0
  nice : ∀ i, c.keep i → ∀ P : D.naut.AV i, ∀ x ∈ c.Xs i, D.naut.ptV i P = some x →
    ∀ (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), UpperTheory.GalS.Nc D.nd D.naut (D.naut.locV i P w)

end UpperTheory.GalC
