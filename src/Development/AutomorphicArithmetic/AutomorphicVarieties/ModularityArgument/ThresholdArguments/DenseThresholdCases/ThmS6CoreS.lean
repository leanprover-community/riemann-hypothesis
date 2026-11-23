module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyClauseStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
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




section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia
namespace UpperTheory.V.Aut
structure BPrime_s (K : Type) [Field K] [NumberField K] [IsCMField K] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : G ℚ Ω → Matrix (Fin 3) (Fin 3) (Qbar l)) : Prop where
  opens : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ (eta4 Ω).ker → MatIrr U a
  cyc : MatIrr ((eta4 Ω).ker ⊓ (cycZ ℚ Ω l).ker) a
  aut : _root_.UpperTheory.V.Af.AutOnAlt K ι (-1) a
def ThmS6_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∃ g₁ : Gam Ω S, F.Marked g₁ ∧
    ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (u : Gam Ω S →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
      Module.Finite c.O (wpart c.O u 0) ∧
      ∀ (ξ : Sring (O := c.O) u →ₐ[c.O] PadicAlgCl l) (r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r →
        _root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat
def ThmS6Core_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∃ g₁ : Gam Ω S, F.Marked g₁ ∧
    ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (u : Gam Ω S →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
      Module.Finite c.O (wpart c.O u 0) ∧
      ∀ (ξ : Sring (O := c.O) u →ₐ[c.O] PadicAlgCl l) (r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r →
        _root_.UpperTheory.V.Af.AutOnAlt K ι (-1) fun s => (r (toGS Ω _ s)).mat
end UpperTheory.V.Aut
end
end
