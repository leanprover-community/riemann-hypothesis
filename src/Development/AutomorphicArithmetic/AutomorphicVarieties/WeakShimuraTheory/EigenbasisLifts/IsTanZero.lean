module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Mathlib.Algebra.DualNumber
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

open Matrix

namespace UpperTheory.V.Ws.Eb

abbrev dF (K : Type) [CommRing K] : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K : DualNumber K →+* K)

section

variable {H K : Type} [Group H] [CommRing K] {n : ℕ}

def Full (ρ : H →* GL (Fin n) K) : Prop := Submodule.span K (Set.range (W.mat ρ)) = ⊤

def IsTan (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K) (ρ' : H →* GL (Fin n) (DualNumber K)) : Prop :=
  ∀ g i j, (ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j =
    ⟨(ρ g : Matrix (Fin n) (Fin n) K) i j, (y g * (ρ g : Matrix (Fin n) (Fin n) K)) i j⟩

theorem IsTan.comp {ρ : H →* GL (Fin n) K} {y : H → Matrix (Fin n) (Fin n) K} {ρ' : H →* GL (Fin n) (DualNumber K)}
    (h : IsTan ρ y ρ') {H' : Type} [Group H'] (φ : H' →* H) : IsTan (ρ.comp φ) (fun g => y (φ g)) (ρ'.comp φ) :=
  fun g => h (φ g)

end

structure IsAdExt {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K : Type} [CommRing K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K)
    (P : GL (Fin n) K) (R : Representation K F.Γ (Matrix (Fin n) (Fin n) K)) : Prop where
  ad : ∀ (g : F.G₀) X, R g X = Loc.adGL ρ g X
  c : ∀ X, R F.c X = -((P⁻¹ : GL (Fin n) K) * Xᵀ * (P : Matrix (Fin n) (Fin n) K))

end UpperTheory.V.Ws.Eb

end
