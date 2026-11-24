module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GRepresents
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

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

section Coord

variable {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] (η : G →* ℤˣ) (Ψ : G →* Oˣ)
  (r : G →* GG (m := 3) (R := R)) (W : WPres O ℤ R)

def IsCoord (s : W.σ) : Prop :=
  ∃ g a b, W.wt s = wt6 a - wt6 b ∧ W.z s = emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)

def EntHomog : Prop := ∀ g a b, emb (r g) a b ∈ W.part (wt6 a - wt6 b)

end Coord

def boxDef (j : ℤ) : ℕ := if |j| ≤ 1 then 1 else 0

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ H : Type} [Group Γ] [TopologicalSpace Γ]
  [Group H] [TopologicalSpace H]

def IsLocPres {η : H →* ℤˣ} {Ψ : H →* Oˣ} (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) (WB : WPres O ℤ (U.R ⧸ I)) :
    Prop :=
  (∀ s, IsCoord η Ψ (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB s) ∧ EntHomog (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB

variable {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
  {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R}

def BoxPres (B : Univ (BoxCond N ι hι U I)) (WB : WPres O ℤ (U.R ⧸ I)) : Prop :=
  ∃ (W : WPres O ℤ B.R) (i : (U.R ⧸ I) →ₐ[O] B.R) (τ κ : Type) (_ : Fintype τ) (_ : Fintype κ) (e : WB.σ ⊕ τ ≃ W.σ)
    (f : κ → MvPowerSeries W.σ O) (wf : κ → ℤ),
    IsRelPres WB i W e f wf ∧ push (i.comp (Ideal.Quotient.mkₐ O I)) U.r.hom = B.r.hom.comp ι ∧
    (∀ t, IsCoord η Ψ B.r.hom W (e (.inr t))) ∧ EntHomog B.r.hom W ∧
    ∀ j, Nat.card {u // wf u = j} = Nat.card {t // W.wt (e (.inr t)) = j} + boxDef j

end UpperTheory.V.U3
